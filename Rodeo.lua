-- Tame a Bull - Trainer + Auto Catch v2.20 (combined, Rayfield Gen 2 GUI)
-- The Auto Catch system below, plus the Bull Trainer at the bottom:
--   AUTO TAP   : center-of-screen taps every 0.125s (8/s cap, VIM)
--   AUTO REACT : presses HUD.Training's React bubble button on sight
-- Catches wild bulls end to end:
--   1. Finds the nearest wild bull (workspace Model with a BullId attribute,
--      not one of your ranch bulls, not already ridden), walks to it and
--      fires the Lasso function on Ride_BLINK_RELIABLE_REMOTE:
--          00 <callId u8> <len u8> <bullId string>
--   2. Parses the server's RideStart event (id 3) itself: fixed 185-byte
--      block + string tail -> {bullId, kind, size, seed, styles, radius,
--      pull, steer, circleSpeed, follow, length, gripSeconds, gripRefill,
--      tempo, swapSeconds, pathX/Z, minX, maxX, homeHalfX/Z, homeYaw,
--      start, seat, lift, delay}.
--   3. Runs a shadow copy of the game's own RideSim (required from
--      ReplicatedStorage.Features.Game.Ride.RideSim -- identical code,
--      identical LCG rng, identical step) and steers it with a PD
--      controller: keep the bull inside the moving circle until the sim
--      parks at home and holds 30 ticks -> "Tamed".
--   4. Sends RideInput on Ride_BLINK_RELIABLE_REMOTE in the game's own
--      format:  01 <startTick u16> <x1 i8> <z1 i8> <x2 i8> <z2 i8>
--      <x3 i8> <z3 i8>  (3 ticks per packet). While a bot ride is live,
--      a __namecall hook swallows the game client's own RideInput fires
--      so only the bot's inputs reach the server.
--   5. RideEnd (id 4) is the server's verdict: 0=Tamed, 1=Flung, 2=Ended.
--      Flung bulls are blacklisted for 60s (usually too strong for now).
-- Strength gates stay the server's: a bull above your strength still
-- flings you; this automates the catches you can legitimately win.

local Players = game:GetService("Players")
local RS = game:GetService("ReplicatedStorage")
local RunService = game:GetService("RunService")
local Player = Players.LocalPlayer
local PlayerGui = Player:WaitForChild("PlayerGui")

local Reliable = RS:WaitForChild("Ride_BLINK_RELIABLE_REMOTE", 15)
local Unreliable = RS:WaitForChild("Ride_BLINK_UNRELIABLE_REMOTE", 15)
local StateR = RS:WaitForChild("State_BLINK_RELIABLE_REMOTE", 15)

local RideSim = nil
do
    local ok, mod = pcall(function()
        return require(RS.Features.Game.Ride.RideSim)
    end)
    if ok and type(mod) == "table" and mod.new and mod.step and mod.quantize then
        RideSim = mod
    else
        print("[AutoCatch] RideSim require FAILED: " .. tostring(mod))
    end
end

local STYLE_NAMES = {
    [0] = "Charger", [1] = "Zigzag", [2] = "Spinner", [3] = "Bucker",
    [4] = "StopGo", [5] = "Pulser", [6] = "Squeezer", [7] = "Drifter",
}

--------------------------------------------------------------------------------
-- State
--------------------------------------------------------------------------------
local autoCatch = false
local cycleStaging = false -- idle-cycle staging: catch loop pauses while set
local idleLogAt = 0
local riding = false
local simDone = false
local rideParams, rideState = nil, nil
local rideT0 = 0
local rideBullId = nil
local rideDeadline = 0
local batch = {}
local batchStart = 0
local firingMine = false
local callIdCounter = math.random(1, 200)
local myBulls = {}
local myBullInfo = {} -- guid -> {kind, level, size} for my pen bulls
local blacklist = {} -- bullId -> os.clock() expiry
local lassoAttemptAt = 0
local lassoTargetId = nil
local shadowPrediction = nil
local diagBotBatches, diagSwallowed, diagRideStartClock = 0, 0, 0
local diagLastPrint = 0
local maxShadowOffset = 0
local lastAnalogX, lastAnalogZ = 0, 0
local lastSkippedRarity = nil
local catchCount, flingCount = 0, 0

--------------------------------------------------------------------------------
-- Rarity filter: kind -> rarity learned from the game's own Breeds data
-- (Breeds.kind(name).tier), from State herd entries, and from attributes.
--------------------------------------------------------------------------------
local RARITY_ORDER = { "Common", "Uncommon", "Rare", "Epic", "Legendary",
    "Mythic", "Secret", "Godly" }
local RARITY_SET = {}
for _, r in ipairs(RARITY_ORDER) do RARITY_SET[r] = true end
local rarityFilter = nil -- nil = catch all rarities
local kindRarity = { Superhero = "Secret" } -- from a Time spawn broadcast
local herdKind = {} -- bullId -> kind (from State entries / model attributes)
-- v2.8 catch filters: name (kind) multi-pick, mutation multi-pick, and a
-- minimum weight in kg from a text box. All optional; default AND:
-- a bull must pass every active filter. The OR-mode toggle on the
-- Catch tab flips it: a bull matching ANY active filter counts.
local nameFilter = nil -- set of lowercased kind names, nil = any name
local mutationFilter = nil -- set of lowercased mutation names, nil = any
local weightMinKg = nil -- number, nil = any weight
local orMode = false -- v2.15: OR mode, any matching filter counts
local orModeWarnAt = 0
local namePicks = {} -- raw dropdown selections (for refresh restore)
local mutationPicks = {}
local seenKinds = {} -- kind display strings learned (name dropdown options)
local knownMutations = {} -- mutation display strings learned (options)
local knownMutationsLower = {} -- lowercased token -> display string
local filterStats = { seen = 0, rarity = 0, name = 0, mutation = 0,
    weight = 0, weightUnknown = 0 }
local nameDropdown, mutationDropdown -- Rayfield handles (GUI section)
-- v2.10 target priority: which passing bull to chase first. "Nearest" is
-- the classic behavior; the others rank by the picked stat, nearest as
-- the tiebreak. Too-strong bulls stay demoted in every mode.
local PRIORITY_MODES = { "Nearest", "Highest Rarity", "Heaviest",
    "Highest Level", "Most $/s" }
local priorityMode = "Nearest"
local RARITY_RANK = {}
for i, r in ipairs(RARITY_ORDER) do RARITY_RANK[r] = i end
local parseRate -- forward-declared; defined in the AUTO TRAIN section

local function noteMutation(tok)
    if type(tok) ~= "string" then return end
    tok = string.gsub(tok, "^%s+", "")
    tok = string.gsub(tok, "%s+$", "")
    if #tok < 2 or #tok > 24 then return end
    if not string.find(tok, "%a") then return end
    if tonumber(tok) then return end
    local low = string.lower(tok)
    if not knownMutationsLower[low] then
        knownMutationsLower[low] = tok
        knownMutations[tok] = true
    end
end

local function filtersActive()
    return rarityFilter ~= nil or nameFilter ~= nil
        or mutationFilter ~= nil or weightMinKg ~= nil
end

local BreedsMod = nil
do
    local ok, mod = pcall(function()
        return require(RS.Features.Game.Breeds)
    end)
    if ok and type(mod) == "table" then BreedsMod = mod end
    local function scanBreedTable(t, depth)
        if type(t) ~= "table" or depth > 3 then return end
        for k, v in pairs(t) do
            if type(v) == "table" then
                if type(k) == "string"
                    and (k == "mutations" or k == "Mutations") then
                    for mk, mv in pairs(v) do
                        if type(mk) == "string" then noteMutation(mk) end
                        if type(mv) == "table" then
                            noteMutation(mv.id)
                            noteMutation(mv.name)
                        elseif type(mv) == "string" then
                            noteMutation(mv)
                        end
                    end
                end
                local rar = v.tier or v.rarity
                if type(rar) == "string" and RARITY_SET[rar] then
                    for _, name in ipairs({ v.id, v.name, v.displayName,
                        type(k) == "string" and k or nil }) do
                        if type(name) == "string" then
                            kindRarity[name] = rar
                        end
                    end
                end
                scanBreedTable(v, depth + 1)
            end
        end
    end
    for _, path in ipairs({ "BreedsContent", "Breeds" }) do
        local ok2, mod2 = pcall(function()
            return require(RS.Features.Game.Breeds[path])
        end)
        if ok2 then scanBreedTable(mod2, 0) end
    end
    local n = 0
    for _ in pairs(kindRarity) do n = n + 1 end
    print("[AutoCatch] kind->rarity map: " .. n .. " kinds known")
    for name in pairs(kindRarity) do seenKinds[name] = true end
    local gameFolder = RS.Features and RS.Features:FindFirstChild("Game")
    if gameFolder then
        for _, child in ipairs(gameFolder:GetChildren()) do
            if child:IsA("ModuleScript")
                and string.find(string.lower(child.Name), "mutation") then
                local okM, modM = pcall(require, child)
                if okM and type(modM) == "table" then
                    scanBreedTable(modM, 0)
                end
            end
        end
    end
    local mn = 0
    for _ in pairs(knownMutations) do mn = mn + 1 end
    print("[AutoCatch] mutations known: " .. mn)
end

local function rarityOfKind(kind)
    if not kind then return nil end
    local rar = kindRarity[kind]
    if rar then return rar end
    if BreedsMod and type(BreedsMod.kind) == "function" then
        local ok, entry = pcall(BreedsMod.kind, kind)
        if ok and type(entry) == "table" then
            rar = entry.tier or entry.rarity
            if type(rar) == "string" and RARITY_SET[rar] then
                kindRarity[kind] = rar
                return rar
            end
        end
    end
    return nil
end

local kindOfModel
local function rarityOfModel(model, bullId)
    local attr = model:GetAttribute("Rarity")
    if type(attr) == "string" and #attr > 0 then
        local norm = attr:sub(1, 1):upper() .. attr:sub(2):lower()
        if RARITY_SET[norm] then return norm end
    end
    return rarityOfKind(kindOfModel(model, bullId))
end

kindOfModel = function(model, bullId)
    local attrKind = model:GetAttribute("Kind")
    if type(attrKind) == "string" then
        herdKind[bullId] = attrKind
        return attrKind
    end
    if herdKind[bullId] then return herdKind[bullId] end
    for name, value in pairs(model:GetAttributes()) do
        if type(value) == "string" and (kindRarity[value] or name == "Kind") then
            herdKind[bullId] = value
            return value
        end
    end
    if kindRarity[model.Name] then
        herdKind[bullId] = model.Name
        return model.Name
    end
    for _, d in ipairs(model:GetDescendants()) do
        if d:IsA("TextLabel") and kindRarity[d.Text] then
            herdKind[bullId] = d.Text
            return d.Text
        end
    end
    return nil
end

-- Mutations on a wild model: string attributes named Mutations / Mutation /
-- Traits / Trait / Trait2 / Trait3 (values may be comma lists), plus tag
-- labels that match a learned mutation name.
local function mutationsOfModel(model)
    local out = {}
    for attrName, value in pairs(model:GetAttributes()) do
        if type(value) == "string" then
            local ln = string.lower(attrName)
            if string.find(ln, "mutation") or string.find(ln, "trait") then
                for tok in string.gmatch(value, "[^,;|/]+") do
                    tok = string.gsub(tok, "^%s+", "")
                    tok = string.gsub(tok, "%s+$", "")
                    if #tok >= 2 then
                        noteMutation(tok)
                        out[string.lower(tok)] = true
                    end
                end
            end
        end
    end
    for _, d in ipairs(model:GetDescendants()) do
        if (d:IsA("TextLabel") or d:IsA("TextButton")) and d.Text then
            local disp = knownMutationsLower[string.lower(d.Text)]
            if disp then out[string.lower(d.Text)] = true end
        end
    end
    return out
end

local WEIGHT_SUFFIX = { [""] = 1, K = 1e3, M = 1e6, B = 1e9, T = 1e12,
    QA = 1e15 }

-- Weight in kg: a Weight attribute if the model carries one, else the
-- "3.8K kg" style text on the bull's own tag.
local function weightOfModel(model)
    local w = model:GetAttribute("Weight")
    if type(w) == "number" then return w end
    for _, d in ipairs(model:GetDescendants()) do
        if (d:IsA("TextLabel") or d:IsA("TextButton")) and d.Text then
            local num, suf = string.match(d.Text,
                "([%d%.]+)%s*([KMBTQa]*)%s*kg")
            if not num then
                num, suf = string.match(d.Text,
                    "([%d%.]+)%s*([KMBTQA]*)%s*KG")
            end
            if num then
                local v = tonumber(num)
                if v then
                    return v * (WEIGHT_SUFFIX[string.upper(suf or "")]
                        or 1)
                end
            end
        end
    end
    return nil
end

-- Text box parser: "1500", "1.5K", "2M", "1,200" all work.
local function parseKgText(text)
    if type(text) ~= "string" then return nil end
    local t = string.gsub(text, "[,%s]", "")
    if t == "" then return nil end
    local num, suf = string.match(t, "^([%d%.]+)([KkMmBbTtQqAa]*)$")
    if not num then return nil end
    local v = tonumber(num)
    if not v then return nil end
    return v * (WEIGHT_SUFFIX[string.upper(suf or "")] or 1)
end

--------------------------------------------------------------------------------
-- Status plumbing: the Rayfield GUI is built at the end of the script;
-- these setters forward status text to its paragraphs once they exist.
-- (Also clears out any GUI left by older versions of this script.)
--------------------------------------------------------------------------------
for _, g in ipairs(PlayerGui:GetChildren()) do
    if g.Name == "BullComboGui" or g.Name == "AutoCatchGui"
        or g.Name == "BullTrainerGui" then
        g:Destroy()
    end
end

local catchStatusPara, trainStatusPara = nil, nil
local catchStatusText = RideSim and "Idle" or "RideSim failed to load!"
local trainStatusText = "Trainer idle"

local function setCatchStatus(s)
    catchStatusText = s
    if catchStatusPara then
        pcall(function()
            catchStatusPara:Set({ Title = "Auto Catch Status", Content = s })
        end)
    end
end

local function setTrainStatus(s)
    trainStatusText = s
    if trainStatusPara then
        pcall(function()
            trainStatusPara:Set({ Title = "Trainer Status", Content = s })
        end)
    end
end

--------------------------------------------------------------------------------
-- Zone teleports: zone layout from the game's HerdZones module (lane along
-- +Z, spawn boxes per zone); names from Breeds.zones when readable.
--------------------------------------------------------------------------------
local ZONE_BOXES = { -- {zMin, zMax} per zone, from HerdZones
    { 135, 220 }, { 234, 520 }, { 534, 970 },
    { 984, 1570 }, { 1584, 2318 }, { 2334, 2918 },
}
local zoneNames = {}
for i = 1, 6 do zoneNames[i] = "Zone " .. i end
if BreedsMod and type(BreedsMod.zones) == "table" then
    for i, z in ipairs(BreedsMod.zones) do
        if type(z) == "table" and type(z.name) == "string" then
            zoneNames[i] = z.name
        end
    end
end

local function teleportToZone(i)
    local box = ZONE_BOXES[i]
    if not box then return end
    local char = Player.Character
    local root = char and char:FindFirstChild("HumanoidRootPart")
    if root then
        root.CFrame = CFrame.new(0, 4, (box[1] + box[2]) / 2)
        setCatchStatus("📍 Teleported to " .. zoneNames[i])
    end
end

-- Run to Zone: same destinations as the teleports, but on foot (MoveTo,
-- re-issued until arrival). Pauses while AUTO CATCH is walking to a bull.
local runTarget = nil -- { pos = Vector3, name = string }

local function startRunToZone(i)
    local box = ZONE_BOXES[i]
    if not box then return end
    runTarget = {
        pos = Vector3.new(0, 0, (box[1] + box[2]) / 2),
        name = zoneNames[i],
    }
    setCatchStatus("🏃 Running to " .. zoneNames[i] .. "...")
end

local function stopRun(silent)
    if runTarget and not silent then
        setCatchStatus("⏹ Run stopped")
    end
    runTarget = nil
end

task.spawn(function()
    while true do
        if runTarget and not autoCatch then
            local char = Player.Character
            local root = char and char:FindFirstChild("HumanoidRootPart")
            local hum = char and char:FindFirstChildOfClass("Humanoid")
            if root and hum then
                local dx = runTarget.pos.X - root.Position.X
                local dz = runTarget.pos.Z - root.Position.Z
                if math.sqrt(dx * dx + dz * dz) <= 8 then
                    setCatchStatus("🏃 Arrived at " .. runTarget.name)
                    runTarget = nil
                else
                    pcall(function() hum:MoveTo(runTarget.pos) end)
                end
            end
        end
        task.wait(0.3)
    end
end)

--------------------------------------------------------------------------------
-- My ranch bulls (from State patches) -- never lasso targets
--------------------------------------------------------------------------------
local stateEventCount = 0
local stateShapePrinted = false

local function absorbBulls(bulls)
    if type(bulls) ~= "table" then return end
    for guid, entry in pairs(bulls) do
        if type(guid) == "string" and type(entry) == "table" then
            if type(entry.kind) == "string" then
                myBulls[guid] = true
                herdKind[guid] = entry.kind
                myBullInfo[guid] = {
                    kind = entry.kind,
                    level = entry.level,
                    size = entry.size,
                }
            elseif entry.__none then
                myBullInfo[guid] = nil
            end
        end
    end
end

-- State arrives as patches; absorb bull entries wherever they sit in the
-- patch (any table carrying a 'bulls' field), and learn herd kinds en route.
local function absorbState(root)
    local seen = {}
    local function walk(t, depth)
        if type(t) ~= "table" or depth > 5 or seen[t] then return end
        seen[t] = true
        if type(t.bulls) == "table" then absorbBulls(t.bulls) end
        for k, v in pairs(t) do
            if type(k) == "string" and #k == 36 and type(v) == "table"
                and type(v.kind) == "string" then
                herdKind[k] = v.kind
            end
            walk(v, depth + 1)
        end
    end
    walk(root, 0)
end

if StateR then
    StateR.OnClientEvent:Connect(function(a, b)
        stateEventCount = stateEventCount + 1
        if not stateShapePrinted then
            stateShapePrinted = true
            local function shape(x)
                if type(x) ~= "table" then return type(x) end
                local keys = {}
                for k in pairs(x) do
                    table.insert(keys, tostring(k))
                    if #keys >= 8 then break end
                end
                return "table{" .. table.concat(keys, ",") .. "}"
            end
            print("[AutoTrain] first State event: arg1=" .. shape(a)
                .. " arg2=" .. shape(b))
        end
        if type(a) == "table" then absorbState(a) end
        if type(b) == "table" then absorbState(b) end
    end)
    print("[AutoTrain] State handler connected")
else
    print("[AutoTrain] State remote MISSING - pen bulls unavailable")
end

local TimeR = RS:FindFirstChild("Time_BLINK_RELIABLE_REMOTE")
if TimeR then
    TimeR.OnClientEvent:Connect(function(_, tbl)
        if type(tbl) == "table" and type(tbl.kind) == "string"
            and type(tbl.rarity) == "string" and RARITY_SET[tbl.rarity] then
            if kindRarity[tbl.kind] ~= tbl.rarity then
                kindRarity[tbl.kind] = tbl.rarity
                print("[AutoCatch] learned " .. tbl.kind .. " = " .. tbl.rarity)
            end
        end
    end)
end

--------------------------------------------------------------------------------
-- __namecall hook: while a bot ride is live, swallow the game client's own
-- RideInput fires so only the bot's inputs reach the server.
--------------------------------------------------------------------------------
if hookmetamethod and getnamecallmethod and Reliable then
    local oldNamecall
    local okHook = pcall(function()
        oldNamecall = hookmetamethod(game, "__namecall", function(self, ...)
            if getnamecallmethod() == "FireServer" and self == Reliable
                and riding and not firingMine then
                local a1 = ...
                if typeof(a1) == "buffer" and buffer.len(a1) > 0
                    and buffer.readu8(a1, 0) == 1 then
                    diagSwallowed = diagSwallowed + 1
                    return
                end
            end
            return oldNamecall(self, ...)
        end)
    end)
    print("[AutoCatch] input hook " .. (okHook and "installed" or "FAILED"))
end

--------------------------------------------------------------------------------
-- Lasso
--------------------------------------------------------------------------------
local function equipLasso()
    local char = Player.Character
    if not char then return end
    if char:FindFirstChild("Lasso") then return end
    local bp = Player:FindFirstChildOfClass("Backpack")
    local tool = bp and bp:FindFirstChild("Lasso")
    local hum = char:FindFirstChildOfClass("Humanoid")
    if tool and hum then
        pcall(function() hum:EquipTool(tool) end)
    end
end

local function fireLasso(bullId)
    if not Reliable then return false end
    callIdCounter = (callIdCounter + 1) % 256
    local b = buffer.create(3 + #bullId)
    buffer.writeu8(b, 0, 0)
    buffer.writeu8(b, 1, callIdCounter)
    buffer.writeu8(b, 2, #bullId)
    buffer.writestring(b, 3, bullId)
    local ok, err = pcall(function()
        Reliable:FireServer(b, {})
    end)
    print("[AutoCatch] lasso fired id=" .. bullId .. " ok=" .. tostring(ok)
        .. (ok and "" or (" err=" .. tostring(err))))
    return ok
end

--------------------------------------------------------------------------------
-- RideStart / RideEnd parsing (payload base = byte 1, after the packet id)
--------------------------------------------------------------------------------
local function parseRideStart(buf)
    if buffer.len(buf) < 1 + 185 then return nil end
    local B = 1
    local p = {}
    local bullIdLen = buffer.readu8(buf, B + 0)
    local kindLen = buffer.readu8(buf, B + 1)
    p.size = buffer.readf64(buf, B + 2)
    local coatFlag = buffer.readu8(buf, B + 10)
    local mutFlag = buffer.readu8(buf, B + 11)
    p.seed = buffer.readu32(buf, B + 12)
    local styleCount = buffer.readu8(buf, B + 16)
    p.radius = buffer.readf64(buf, B + 17)
    p.pull = buffer.readf64(buf, B + 25)
    p.steer = buffer.readf64(buf, B + 33)
    p.circleSpeed = buffer.readf64(buf, B + 41)
    p.follow = buffer.readf64(buf, B + 49)
    p.length = buffer.readf64(buf, B + 57)
    p.gripSeconds = buffer.readf64(buf, B + 65)
    p.gripRefill = buffer.readf64(buf, B + 73)
    p.tempo = buffer.readf64(buf, B + 81)
    p.swapSeconds = buffer.readf64(buf, B + 89)
    p.pathX = buffer.readf64(buf, B + 97)
    p.pathZ = buffer.readf64(buf, B + 105)
    p.minX = buffer.readf64(buf, B + 113)
    p.maxX = buffer.readf64(buf, B + 121)
    p.homeHalfX = buffer.readf64(buf, B + 129)
    p.homeHalfZ = buffer.readf64(buf, B + 137)
    p.homeYaw = buffer.readf64(buf, B + 145)
    p.startPos = Vector3.new(
        buffer.readf32(buf, B + 153), buffer.readf32(buf, B + 157),
        buffer.readf32(buf, B + 161))
    p.delay = buffer.readf32(buf, B + 181)
    local tail = B + 185
    p.bullId = buffer.readstring(buf, tail, bullIdLen)
    tail = tail + bullIdLen
    p.kind = buffer.readstring(buf, tail, kindLen)
    tail = tail + kindLen
    if coatFlag == 1 then tail = tail + 1 + buffer.readu8(buf, tail) end
    if mutFlag == 1 then tail = tail + 1 + buffer.readu8(buf, tail) end
    p.styles = {}
    for i = 1, styleCount do
        p.styles[i] = STYLE_NAMES[buffer.readu8(buf, tail)] or "Charger"
        tail = tail + 1
    end
    return p
end

if Reliable then
    Reliable.OnClientEvent:Connect(function(buf)
        if typeof(buf) ~= "buffer" or buffer.len(buf) < 1 then return end
        local pid = buffer.readu8(buf, 0)
        if pid == 3 then
            local ok, p = pcall(parseRideStart, buf)
            if not ok or not p then
                print("[AutoCatch] RideStart parse FAILED: " .. tostring(p))
                return
            end
            print(("[AutoCatch] RideStart bull=%s kind=%s size=%.2f styles=%s "
                .. "grip=%.1fs/%.1f length=%.0f steer=%.1f radius=%.1f "
                .. "cs=%.1f pull=%.1f follow=%.2f tempo=%.2f swap=%.1f "
                .. "delay=%.2f path=(%.2f,%.2f) bounds=(%.0f,%.0f)"):format(
                p.bullId, p.kind, p.size, table.concat(p.styles, "+"),
                p.gripSeconds, p.gripRefill, p.length, p.steer, p.radius,
                p.circleSpeed, p.pull, p.follow, p.tempo, p.swapSeconds,
                p.delay or 0, p.pathX, p.pathZ, p.minX, p.maxX))
            if not autoCatch or not RideSim then return end
            local params = {
                seed = p.seed, styles = p.styles, radius = p.radius,
                pull = p.pull, steer = p.steer, circleSpeed = p.circleSpeed,
                follow = p.follow, length = p.length,
                gripSeconds = p.gripSeconds, gripRefill = p.gripRefill,
                tempo = p.tempo, swapSeconds = p.swapSeconds,
                pathX = p.pathX, pathZ = p.pathZ, minX = p.minX, maxX = p.maxX,
                homeHalfX = p.homeHalfX, homeHalfZ = p.homeHalfZ,
                homeYaw = p.homeYaw,
            }
            local okState, st = pcall(RideSim.new, params)
            if not okState then
                print("[AutoCatch] RideSim.new FAILED: " .. tostring(st))
                return
            end
            rideParams, rideState = params, st
            rideT0 = os.clock() + (p.delay or 0)
            rideBullId = p.bullId
            rideDeadline = os.clock() + (RideSim.duration
                and RideSim.duration(params) or 120) + 20
            batch = {}
            riding = true
            simDone = false
            shadowPrediction = nil
            maxShadowOffset = 0
            diagBotBatches, diagSwallowed = 0, 0
            diagRideStartClock = os.clock()
            diagLastPrint = 0
            lastAnalogX, lastAnalogZ = 0, 0
            setCatchStatus("🐂 Riding " .. p.kind .. "...")
        elseif pid == 4 and buffer.len(buf) >= 2 then
            local oc = buffer.readu8(buf, 1)
            local name = oc == 0 and "Tamed" or (oc == 1 and "Flung" or "Ended")
            print("[AutoCatch] RideEnd: " .. name)
            print(("[AutoCatch] VERDICT server=%s shadow=%s match=%s "
                .. "sent=%d swallowed=%d"):format(
                name, tostring(shadowPrediction),
                tostring(shadowPrediction == name),
                diagBotBatches, diagSwallowed))
            shadowPrediction = nil
            if name == "Tamed" then
                catchCount = catchCount + 1
                setCatchStatus("🎉 Tamed! (x" .. catchCount .. ")")
            elseif name == "Flung" then
                flingCount = flingCount + 1
                if rideBullId then blacklist[rideBullId] = os.clock() + 60 end
                setCatchStatus("💨 Flung (x" .. flingCount .. ") - too strong?")
            else
                setCatchStatus("Ride ended")
            end
            riding = false
            simDone = false
            rideState, rideParams = nil, nil
        end
    end)
end

--------------------------------------------------------------------------------
-- Steering: PD on the shadow sim state (world-frame inputs, like _stick's)
--------------------------------------------------------------------------------
local function computeInput()
    local st, pm = rideState, rideParams
    local pathSpeed = 0
    if st.parked then
        pathSpeed = 0
    elseif st.home then
        pathSpeed = st.glide
    else
        pathSpeed = pm.circleSpeed
    end
    local pathVX, pathVZ = pm.pathX * pathSpeed, pm.pathZ * pathSpeed
    local baseVX = pathVX + pm.follow * (st.cvx - pathVX)
    local baseVZ = pathVZ + pm.follow * (st.cvz - pathVZ)
    -- desired bull velocity: ride with the center, close the offset gap,
    -- damp the relative velocity, and lean against a telegraphed lunge.
    -- Gains are near critically damped (kd ~= 2*sqrt(kp)) so the bull
    -- settles ON the center instead of orbiting it; the ride home
    -- (glide/parked) uses stiffer gains to park it dead-center.
    -- Gains tuned headlessly against the game's own RideSim (Oct 21):
    -- firm + near-critically damped; the ride home averages ~0.3 studs
    -- off dead-center (worst ~0.6), the floor set by 30Hz steps and the
    -- 1/127 input quantization. Higher kd hunted on low-steer bulls.
    local kp, kd
    if st.home or st.parked then
        kp, kd = 6.0, 4.6
    else
        kp, kd = 6.0, 4.0
    end
    local desVX = st.cvx - st.x * kp - (st.vx - st.cvx) * kd
    local desVZ = st.cvz - st.z * kp - (st.vz - st.cvz) * kd
    if st.tell and st.tell > 0.3 then
        desVX = desVX - (st.tellX or 0) * st.tell * 6
        desVZ = desVZ - (st.tellZ or 0) * st.tell * 6
    end
    local ix = (desVX - baseVX) / pm.steer
    local iz = (desVZ - baseVZ) / pm.steer
    local m = math.sqrt(ix * ix + iz * iz)
    if m > 1 then
        ix, iz = ix / m, iz / m
    end
    return RideSim.quantize(ix, iz)
end

local function sendBatch()
    if #batch == 0 then return end
    local b = buffer.create(9)
    buffer.writeu8(b, 0, 1)
    buffer.writeu16(b, 1, batchStart % 65536)
    for i = 1, 6 do
        buffer.writei8(b, 2 + i, batch[i] or 0)
    end
    firingMine = true
    pcall(function() Reliable:FireServer(b, {}) end)
    firingMine = false
    diagBotBatches = diagBotBatches + 1
    batch = {}
end

RunService.Heartbeat:Connect(function()
    if not riding or simDone or not rideState then return end
    if os.clock() > rideDeadline then
        print("[AutoCatch] ride deadline passed, giving up control")
        riding = false
        simDone = false
        rideState, rideParams = nil, nil
        return
    end
    local targetTick = math.floor((os.clock() - rideT0) * 30)
    if targetTick < 0 then return end
    local steps = math.min(targetTick - rideState.tick, 6)
    if steps <= 0 then return end
    for _ = 1, steps do
        if rideState.outcome ~= "Riding" then break end
        if #batch == 0 then batchStart = rideState.tick end
        local ix, iz = computeInput()
        RideSim.step(rideParams, rideState, ix, iz)
        lastAnalogX, lastAnalogZ = ix / 127, iz / 127
        local offNow = math.sqrt(rideState.x * rideState.x
            + rideState.z * rideState.z)
        if offNow > maxShadowOffset then maxShadowOffset = offNow end
        table.insert(batch, ix)
        table.insert(batch, iz)
        if #batch >= 6 then sendBatch() end
    end
    if riding and rideState and os.clock() - diagLastPrint >= 1 then
        diagLastPrint = os.clock()
        print(("[AutoCatch] t+%.0fs tick=%d off=%.1f grip=%.0f%% "
            .. "sent=%d swallowed=%d"):format(
            os.clock() - diagRideStartClock, rideState.tick,
            math.sqrt(rideState.x * rideState.x + rideState.z * rideState.z),
            rideState.grip * 100, diagBotBatches, diagSwallowed))
    end
    if rideState.outcome ~= "Riding" then
        sendBatch()
        simDone = true
        shadowPrediction = rideState.outcome
        print(("[AutoCatch] shadow sim predicts: %s (tick %d, grip %.0f%%, "
            .. "max offset %.1f of radius %.1f)"):format(
            rideState.outcome, rideState.tick, rideState.grip * 100,
            maxShadowOffset, rideParams.radius))
        setCatchStatus("Sim says " .. rideState.outcome .. " - waiting for server")
    end
end)

--------------------------------------------------------------------------------
-- Target scan + approach + lasso attempts
--------------------------------------------------------------------------------
local function rootPos()
    local char = Player.Character
    local root = char and char:FindFirstChild("HumanoidRootPart")
    return root and root.Position or nil
end

local function myStrength()
    local ls = Player:FindFirstChild("leaderstats")
    local s = ls and ls:FindFirstChild("Strength")
    if s and type(s.Value) == "number" then return s.Value end
    return nil
end

local function candBetter(a, b)
    local ab = a.tooStrong and 1 or 0
    local bb = b.tooStrong and 1 or 0
    if ab ~= bb then return ab < bb end
    if priorityMode == "Highest Rarity"
        and a.rarityRank ~= b.rarityRank then
        return a.rarityRank > b.rarityRank
    end
    if priorityMode == "Heaviest"
        and (a.weight or -1) ~= (b.weight or -1) then
        return (a.weight or -1) > (b.weight or -1)
    end
    if priorityMode == "Highest Level" and a.level ~= b.level then
        return a.level > b.level
    end
    if priorityMode == "Most $/s"
        and (a.rate or -1) ~= (b.rate or -1) then
        return (a.rate or -1) > (b.rate or -1)
    end
    return a.dist < b.dist
end

local function findTarget()
    local pos = rootPos()
    if not pos then return nil end
    filterStats = { seen = 0, rarity = 0, name = 0, mutation = 0,
        weight = 0, weightUnknown = 0 }
    local mine = myStrength()
    local best, bestDist = nil, math.huge
    for _, d in ipairs(workspace:GetDescendants()) do
        if d:IsA("Model") then
            local id = d:GetAttribute("BullId")
            if type(id) == "string" and not myBulls[id]
                and d:GetAttribute("Rider") == nil then
                local exp = blacklist[id]
                if not (exp and exp > os.clock()) then
                    local kind = kindOfModel(d, id)
                    if kind then seenKinds[kind] = true end
                    local rar = rarityOfModel(d, id)
                    local muts = mutationsOfModel(d)
                    filterStats.seen = filterStats.seen + 1
                    -- Per-category matches (a nil filter = unset).
                    local rarityMatch = rar ~= nil
                        and rarityFilter ~= nil
                        and rarityFilter[rar] == true
                    local nameMatch = kind ~= nil
                        and nameFilter ~= nil
                        and nameFilter[string.lower(kind)] == true
                    local mutationMatch = false
                    if mutationFilter ~= nil then
                        for m in pairs(muts) do
                            if mutationFilter[m] then
                                mutationMatch = true
                                break
                            end
                        end
                    end
                    local weight = nil
                    local weightMatch = false
                    if weightMinKg ~= nil then
                        weight = weightOfModel(d)
                        if weight == nil then
                            filterStats.weightUnknown =
                                filterStats.weightUnknown + 1
                        elseif weight >= weightMinKg then
                            weightMatch = true
                        else
                            filterStats.weight = filterStats.weight + 1
                        end
                    end
                    if rarityFilter ~= nil and not rarityMatch then
                        if rar then lastSkippedRarity = rar end
                        filterStats.rarity = filterStats.rarity + 1
                    end
                    if nameFilter ~= nil and not nameMatch then
                        filterStats.name = filterStats.name + 1
                    end
                    if mutationFilter ~= nil and not mutationMatch then
                        filterStats.mutation = filterStats.mutation + 1
                    end
                    -- AND (default): every set category must match.
                    -- OR (v2.15 toggle): a bull matching ANY set
                    -- category is a target - e.g. rarity Secret +
                    -- min weight 100k catches any Secret (any size)
                    -- and any 100k+ bull (any rarity). OR mode with
                    -- no categories set matches nothing (warned).
                    local pass
                    if orMode then
                        pass = rarityMatch or nameMatch or mutationMatch
                            or weightMatch
                        if not (rarityFilter ~= nil or nameFilter ~= nil
                            or mutationFilter ~= nil
                            or weightMinKg ~= nil) then
                            pass = false
                            if os.clock() - orModeWarnAt > 10 then
                                orModeWarnAt = os.clock()
                                print("[AutoCatch] OR mode on but no "
                                    .. "filters picked - nothing matches")
                            end
                        end
                    else
                        pass = (rarityFilter == nil or rarityMatch)
                            and (nameFilter == nil or nameMatch)
                            and (mutationFilter == nil or mutationMatch)
                            and (weightMinKg == nil or weightMatch)
                    end
                    if pass then
                        local req = d:GetAttribute("Strength")
                        local tooStrong = type(req) == "number"
                            and mine ~= nil and req > mine
                        local bp = d:GetPivot().Position
                        local dist = (bp - pos).Magnitude
                        local lvl = d:GetAttribute("Level")
                        if type(lvl) ~= "number" then lvl = 0 end
                        local w = weight
                        if w == nil and priorityMode == "Heaviest" then
                            w = weightOfModel(d)
                        end
                        local rate = nil
                        if priorityMode == "Most $/s" then
                            rate = parseRate(d)
                        end
                        local cand = {
                            id = id, pos = bp, model = d,
                            kind = kind, rarity = rar,
                            tooStrong = tooStrong,
                            weight = w, mutations = muts,
                            level = lvl, rate = rate, dist = dist,
                            rarityRank = rar and RARITY_RANK[rar] or 0,
                        }
                        if not best or candBetter(cand, best) then
                            best, bestDist = cand, dist
                        end
                    end
                end
            end
        end
    end
    return best, bestDist
end

task.spawn(function()
    while true do
        if autoCatch and not riding and RideSim and not cycleStaging then
            equipLasso()
            local target, dist = findTarget()
            if not target then
                if os.clock() - idleLogAt > 10 then
                    idleLogAt = os.clock()
                    print("[AutoCatch] idle pass: no catchable bull "
                        .. "(filters " .. (filtersActive() and "on" or "off")
                        .. ")")
                    if filtersActive() then
                        print(("[AutoCatch] filter pass: seen=%d "
                            .. "raritySkip=%d nameSkip=%d mutationSkip=%d "
                            .. "weightSkip=%d weightUnknown=%d"):format(
                            filterStats.seen, filterStats.rarity,
                            filterStats.name, filterStats.mutation,
                            filterStats.weight, filterStats.weightUnknown))
                    end
                end
                if filtersActive() then
                    setCatchStatus("🔍 No bulls match your filters nearby")
                else
                    setCatchStatus("🔍 No wild bulls found")
                end
            elseif dist > 40 then
                setCatchStatus((target.tooStrong
                    and "⚠️ Strong %s - walking (%dm)"
                    or "🚶 Walking to %s (%dm)"):format(
                    target.kind or "bull", dist))
                local char = Player.Character
                local hum = char and char:FindFirstChildOfClass("Humanoid")
                if hum then
                    pcall(function() hum:MoveTo(target.pos) end)
                end
            else
                if os.clock() - lassoAttemptAt >= 3.5 then
                    lassoAttemptAt = os.clock()
                    lassoTargetId = target.id
                    setCatchStatus(target.tooStrong
                        and "⚠️ Lassoing a stronger bull..."
                        or "🎯 Lassoing...")
                    fireLasso(target.id)
                    task.delay(3, function()
                        if not riding and lassoTargetId == target.id then
                            blacklist[target.id] = os.clock() + 15
                            print("[AutoCatch] no RideStart for " .. target.id
                                .. " - skipping it for 15s")
                        end
                    end)
                else
                    setCatchStatus("🎯 Bull in range (lasso cooldown)")
                end
            end
            task.wait(0.7)
        else
            task.wait(0.4)
        end
    end
end)

--------------------------------------------------------------------------------
-- Input mirror (v1.4): the on-screen ride is rendered from the game client's
-- OWN sim, which steps on the player's stick inputs - idle while the bot
-- drives by remote, so the visual bull used to wander out of the circle even
-- on perfect rides. The mirror holds WASD (VirtualInputManager key events)
-- to reproduce the bot's steering through the game's real input path
-- (PlayerModule MoveAction, rotated by camera facing exactly like _stick),
-- so the local sim - and the picture - follow the same inputs the server
-- gets. Server control is unchanged (direct batches, hook still swallows
-- the client's own fires). Mirror failures disable it silently.
--------------------------------------------------------------------------------
local MirrorVIM = game:GetService("VirtualInputManager")
local mirrorKeysDown = {}
local mirrorOk = true
local mirrorFrame = 0

local function setMirrorKey(code, down)
    if mirrorKeysDown[code] == down then return end
    mirrorKeysDown[code] = down
    if not mirrorOk then return end
    local ok, err = pcall(function()
        MirrorVIM:SendKeyEvent(down, code, false, game)
    end)
    if not ok then
        mirrorOk = false
        print("[AutoCatch] input mirror disabled: " .. tostring(err))
    end
end

local function releaseMirrorKeys()
    for code in pairs(mirrorKeysDown) do
        setMirrorKey(code, false)
    end
end

RunService.Heartbeat:Connect(function()
    if not riding then
        releaseMirrorKeys()
        return
    end
    local cam = workspace.CurrentCamera
    if not cam then return end
    local look = cam.CFrame.LookVector
    local fx, fz = look.X, look.Z
    local fl = math.sqrt(fx * fx + fz * fz)
    if fl < 0.001 then return end
    fx, fz = fx / fl, fz / fl
    -- invert _stick: q = R(forward) * m  ->  m = R^T * q
    local qx, qz = lastAnalogX, lastAnalogZ
    local mx = -fz * qx + fx * qz
    local mz = -fx * qx - fz * qz
    local sx, sy = mx, -mz -- MoveAction state: X = strafe, Y = forward
    mirrorFrame = mirrorFrame + 1
    -- full deflection above 0.45; mid-range duty-cycles on alternate frames
    local function want(v)
        local a = math.abs(v)
        if a >= 0.45 then return v end
        if a >= 0.22 and mirrorFrame % 2 == 0 then return v end
        return 0
    end
    local wx, wy = want(sx), want(sy)
    setMirrorKey(Enum.KeyCode.D, wx > 0)
    setMirrorKey(Enum.KeyCode.A, wx < 0)
    setMirrorKey(Enum.KeyCode.W, wy > 0)
    setMirrorKey(Enum.KeyCode.S, wy < 0)
end)

--------------------------------------------------------------------------------
-- Bull Trainer half: AUTO TAP (center screen taps) + AUTO REACT (HUD bubble)
--------------------------------------------------------------------------------
local VIM = game:GetService("VirtualInputManager")
local autoTap = false
local autoReact = false
local reactCount = 0

-- (Trainer toggles live in the Rayfield GUI at the end of the script.)

-- AUTO TAP: center-of-screen tap every 0.125s while ON - exactly the
-- game's TapCapPerSecond (8). v2.16 offered 10/s; the server caps at
-- 8/s anyway, so the extra 2/s were pure waste. Combo (5 taps/step,
-- 1s window) still sustains at 8/s.
local vimWarned = false
local function tapCenter()
    local cam = workspace.CurrentCamera
    if not cam then return end
    local vs = cam.ViewportSize
    local x, y = math.floor(vs.X / 2), math.floor(vs.Y / 2)
    local ok, err = pcall(function()
        VIM:SendMouseButtonEvent(x, y, 0, true, game, 0)
        VIM:SendMouseButtonEvent(x, y, 0, false, game, 0)
    end)
    if not ok and not vimWarned then
        vimWarned = true
        print("[TrainerCatch] screen tap failed: " .. tostring(err))
    end
end

task.spawn(function()
    while true do
        if autoTap then
            tapCenter()
            task.wait(0.125)
        else
            task.wait(0.2)
        end
    end
end)

-- AUTO REACT: press HUD.Training's "React" button while it is visible
local function findTrainingRoot()
    local hud = PlayerGui:FindFirstChild("HUD")
    if hud then
        local t = hud:FindFirstChild("Training")
        if t then return t end
    end
    for _, d in ipairs(PlayerGui:GetDescendants()) do
        if string.lower(d.Name) == "training"
            and string.find(d:GetFullName(), ".HUD.", 1, true) then
            return d
        end
    end
    return nil
end

local function guiChainVisible(inst)
    local node = inst
    while node and node ~= PlayerGui do
        if node:IsA("GuiObject") and not node.Visible then return false end
        node = node.Parent
    end
    return true
end

local function pressReactButton()
    if not firesignal then return false end
    local root = findTrainingRoot()
    local btn = root and root:FindFirstChild("React", true)
    if btn and btn:IsA("GuiButton") and guiChainVisible(btn) then
        local ok = pcall(function()
            firesignal(btn.MouseButton1Click)
            firesignal(btn.Activated)
        end)
        if ok then
            reactCount = reactCount + 1
            print("[TrainerCatch][React] bubble pressed x" .. reactCount)
            setTrainStatus("🫧 Bubble pressed (x" .. reactCount .. ")")
            return true
        end
    end
    return false
end

task.spawn(function()
    local pressesThisBubble = 0
    local lastPressAt = 0
    while true do
        if autoReact and firesignal then
            local root = findTrainingRoot()
            local btn = root and root:FindFirstChild("React", true)
            local vis = btn and btn:IsA("GuiButton") and guiChainVisible(btn)
            if vis then
                local now = os.clock()
                -- v2.17: 5 presses cover the full 2s ReactWindowSeconds
                if pressesThisBubble == 0
                    or (pressesThisBubble < 5 and now - lastPressAt >= 0.4) then
                    pressReactButton()
                    pressesThisBubble = pressesThisBubble + 1
                    lastPressAt = now
                end
                task.wait(0.05)
            else
                pressesThisBubble = 0
                task.wait(0.1)
            end
        else
            pressesThisBubble = 0
            task.wait(0.3)
        end
    end
end)

--------------------------------------------------------------------------------
-- Rayfield Gen 2 GUI (v2.0): every control lives here now. All toggles
-- start OFF and nothing is saved between executions.
--------------------------------------------------------------------------------
pcall(function()
    if getgenv and getgenv().__BullCatchWindow then
        getgenv().__BullCatchWindow:Destroy()
    end
end)

-- Embedded Rayfield fallback (v2.12): a pinned copy of the official
-- sirius.menu build (fetched + compile-verified Oct 23 2026), used
-- only if the live download fails - the same Delta HttpGet failure
-- that killed the seed farm's GUI on Oct 23 also kills this one
-- (HttpError: ConnectFail at the load line). The same leak patch is
-- applied to either copy.
local EMBEDDED_RAYFIELD = [=======[--[[

	Rayfield Interface Suite
	by Sirius

	shlex  | Designing + Programming
	iRay   | Programming
	Max    | Programming
	Damian | Programming

]]

-- Read first, so secure mode covers Rayfield's output from its first line.
local secureMode = false
if getgenv then
	local ok, result = pcall(function() return getgenv().RAYFIELD_SECURE end)
	if ok and result then secureMode = true end
end

-- Rayfield's own console output goes through these locals. Under secure mode they are silent.
-- They are never assigned as globals: in an executor those are shared with every other script.
local warn, print, error, assert = warn, print, error, assert
if secureMode then
	local rawError = error
	local rawAssert = assert
	warn = function(...) end
	print = function(...) end
	error = function(_, level) rawError("", level) end
	assert = function(v, ...) return rawAssert(v) end
end

if debugX then
	warn('Initialising Rayfield')
end



local function getService(name)
	local service = game:GetService(name)
	return if cloneref then cloneref(service) else service
end

-- Remote modules are fetched from a fixed commit rather than a branch, so what runs is exactly what
-- was reviewed and a push to a branch can't change it under every running script. Bump this to
-- ship a new reporter or icon set. sirius-gate pins its reporter to the same commit.
local RAYFIELD_COMMIT = "3ef72398fb4c8ba6fd1801e98704991d3cc9cbc2" -- SiriusSoftwareLtd/Rayfield: reporter.lua, icons.lua
local RAYFIELD_RAW = "https://raw.githubusercontent.com/SiriusSoftwareLtd/Rayfield/" .. RAYFIELD_COMMIT .. "/"

-- Services
local UserInputService = getService("UserInputService")
local TweenService = getService("TweenService")
local Players = getService("Players")
local CoreGui = getService("CoreGui")

-- Some executors have no task.cancel. Without it the thread is left to finish on its own.
local function cancelThread(thread: thread)
	if task.cancel then
		pcall(task.cancel, thread)
	end
end

-- Loads and executes a function hosted on a remote URL. Cancels the request if the requested URL takes too long to respond.
-- Errors with the function are caught and logged to the output
local function loadWithTimeout(url: string, timeout: number?): ...any
	assert(type(url) == "string", "Expected string, got " .. type(url))
	timeout = timeout or 5
	local requestCompleted = false
	local success, result = false, nil

	local requestThread = task.spawn(function()
		local fetchSuccess, fetchResult = pcall(game.HttpGet, game, url) -- game:HttpGet(url)
		-- If the request fails the content can be empty, even if fetchSuccess is true
		if not fetchSuccess or #fetchResult == 0 then
			if #fetchResult == 0 then
				fetchResult = "Empty response" -- Set the error message
			end
			success, result = false, fetchResult
			requestCompleted = true
			return
		end
		local content = fetchResult -- Fetched content
		local execSuccess, execResult = pcall(function()
			return loadstring(content)()
		end)
		success, result = execSuccess, execResult
		requestCompleted = true
	end)

	local timeoutThread = task.delay(timeout, function()
		if not requestCompleted then
			warn("Request for " .. url .. " timed out after " .. tostring(timeout) .. " seconds")
			cancelThread(requestThread)
			result = "Request timed out"
			requestCompleted = true
		end
	end)

	-- Wait for completion or timeout
	while not requestCompleted do
		task.wait()
	end
	-- Cancel timeout thread if still running when request completes
	if coroutine.status(timeoutThread) ~= "dead" then
		cancelThread(timeoutThread)
	end
	if not success then
		warn("Failed to process " .. tostring(url) .. ": " .. tostring(result))
	end
	return if success then result else nil
end

local requestsDisabled = false
local analyticsOptOut = false -- the player set getgenv().RAYFIELD_ANALYTICS = false
local customAssetId = nil
if getgenv then
	local ok, result = pcall(function() return getgenv().DISABLE_RAYFIELD_REQUESTS end)
	if ok and result then requestsDisabled = true end
	local ok2, result2 = pcall(function() return getgenv().RAYFIELD_ASSET_ID end)
	if ok2 and type(result2) == "number" then customAssetId = result2 end
	local ok3, result3 = pcall(function() return getgenv().RAYFIELD_ANALYTICS end)
	if ok3 and result3 == false then analyticsOptOut = true end
end

local secureWarnings = {}
local customAssets = {}

local function secureNotify(wType, title, content)
	if secureWarnings[wType] then return end
	secureWarnings[wType] = true
	task.spawn(function()
		while not RayfieldLibrary or not RayfieldLibrary.Notify do task.wait(0.5) end
		RayfieldLibrary:Notify({
			Title = title,
			Content = content,
			Duration = 8,
		})
	end)
end
local InterfaceBuild = 'UU2NX'
local Release = "Build 1.753"
local RayfieldFolder = "Rayfield"
local ConfigurationFolder = RayfieldFolder.."/Configurations"
local ConfigurationExtension = ".rfld"
local settingsTable = {
	General = {
		-- if needs be in order just make getSetting(name)
		rayfieldOpen = {Type = 'bind', Value = 'K', Name = 'Rayfield Keybind'},
		-- buildwarnings
		-- rayfieldprompts

	},
	System = {
		usageAnalytics = {
			Type = 'toggle',
			Value = true,
			Name = 'Usage Analytics (pseudonymous)',
			Description = 'Sends a hashed user ID, executor, game, locale and script details when a window opens, plus kick error codes. Nothing you type. sirius.menu/privacy',
		},
	}
}

-- Settings that have been overridden by the developer. These will not be saved to the user's configuration file
-- Overridden settings always take precedence over settings in the configuration file, and are cleared if the user changes the setting in the UI
local overriddenSettings: { [string]: any } = {} -- For example, overriddenSettings["System.rayfieldOpen"] = "J"
local function overrideSetting(category: string, name: string, value: any)
	overriddenSettings[category .. "." .. name] = value
end

local function getSetting(category: string, name: string): any
	if overriddenSettings[category .. "." .. name] ~= nil then
		return overriddenSettings[category .. "." .. name]
	elseif settingsTable[category][name] ~= nil then
		return settingsTable[category][name].Value
	end
end

-- If requests/analytics have been disabled by the developer or the player, set the user-facing
-- setting to false as well
if requestsDisabled or analyticsOptOut then
	overrideSetting("System", "usageAnalytics", false)
end

local HttpService = getService('HttpService')
local RunService = getService('RunService')

-- Environment Check
local useStudio = RunService:IsStudio() or false

local settingsCreated = false
local settingsInitialized = false -- Whether the UI elements in the settings page have been set to the proper values
local requestFunc = (syn and syn.request) or (fluxus and fluxus.request) or (http and http.request) or http_request or request


-- The function below provides a safe alternative for calling error-prone functions
-- Especially useful for filesystem function (writefile, makefolder, etc.)
local function callSafely(func, ...)
	if func then
		local success, result = pcall(func, ...)
		if not success then
			warn("Rayfield | Function failed with error: ", result)
			return false
		else
			return result
		end
	end
end

-- Ensures a folder exists by creating it if needed
local function ensureFolder(folderPath)
	if isfolder and not callSafely(isfolder, folderPath) then
		callSafely(makefolder, folderPath)
	end
end

-- Folder and file names a hub supplies go into paths under the executor's workspace, so they can't
-- be allowed to climb out of it. Removing a character can expose a new "..", so ".:./" is cleaned
-- of the character first and the dots after, repeating until nothing changes.
local function stripTraversal(text: string): string
	local previous
	repeat
		previous = text
		text = string.gsub(text, "%.%.", "")
	until text == previous
	return text
end

-- Keeps "/" so a hub can still nest its folder, but never a leading one, a drive letter or "..".
local function sanitizeFolderName(value: any): string
	local text = string.gsub(string.gsub(tostring(value), "\\", "/"), "[:%c]", "")
	text = string.gsub(stripTraversal(text), "/+", "/")
	return (string.gsub(text, "^/+", ""))
end

-- A single file name: no slashes of either kind, control characters or "..".
local function sanitizeFileName(value: any): string
	local text = string.gsub(tostring(value), "[/\\%c]", "")
	return stripTraversal(text)
end

local function loadSettings()
	local file = nil

	local success, result =	pcall(function()
		if callSafely(isfolder, RayfieldFolder) then
			if callSafely(isfile, RayfieldFolder..'/settings'..ConfigurationExtension) then
				file = callSafely(readfile, RayfieldFolder..'/settings'..ConfigurationExtension)
			end
		end

		-- for debug in studio
		if useStudio then
			file = [[
	{"General":{"rayfieldOpen":{"Value":"K","Type":"bind","Name":"Rayfield Keybind","Element":{"HoldToInteract":false,"Ext":true,"Name":"Rayfield Keybind","Set":null,"CallOnChange":true,"Callback":null,"CurrentKeybind":"K"}}},"System":{"usageAnalytics":{"Value":false,"Type":"toggle","Name":"Usage Analytics (pseudonymous)","Element":{"Ext":true,"Name":"Usage Analytics (pseudonymous)","Set":null,"CurrentValue":false,"Callback":null}}}}
]]
		end

		if file then
			local decodeSuccess, decodedFile = pcall(function() return HttpService:JSONDecode(file) end)
			if decodeSuccess then
				file = decodedFile
			else
				file = {}
			end
		else
			file = {}
		end


		if not settingsCreated then
			return
		end

		-- Check if settings file has any entries
		if next(file) ~= nil then
			-- If it does, apply them
			for categoryName, categoryTable in file do
				for settingName, setting in categoryTable do
					local default = settingsTable[categoryName] and settingsTable[categoryName][settingName]
					if not default then continue end -- ignore keys not in settingsTable (old/renamed settings)
					local settingType = typeof(default.Value)
					-- Make sure setting has the correct type
					if not (settingType == typeof(setting.Value)) then
						warn("Rayfield | Error parsing settings file. '"..settingName.."' must be a "..settingType)
						continue
					end
					default.Value = setting.Value
				end
			end
		end
		-- Apply the actual setting value to UI elements
		for categoryName, categoryTable in settingsTable do
			for settingName, setting in categoryTable do
				if setting.Element then
					setting.Element:Set(getSetting(categoryName, settingName))
				end
			end
		end
		settingsInitialized = true
	end)

	if not success then 
		if writefile then
			warn('Rayfield had an issue accessing configuration saving capability.')
		end
	end
end

if debugX then
	warn('Now Loading Settings Configuration')
end

loadSettings()

if debugX then
	warn('Settings Loaded')
end

local ANALYTICS_TOKEN = "05de7f9fd320d3b8428cd1c77014a337b85b6c8efee2c5914f5ab5700c354b9a"

-- The reporter is fetched only at the moment it is about to be used, and only if the user hasn't
-- opted out and the developer hasn't set DISABLE_RAYFIELD_REQUESTS. Opting out means no request to
-- GitHub for it either, not just no event sent.
local reporter = nil
local reporterLoaded = false
local function loadReporter()
	if reporterLoaded then return reporter end
	reporterLoaded = true
	if requestsDisabled or useStudio then return nil end

	local fetchSuccess, fetchResult = pcall((game :: any).HttpGet, game, RAYFIELD_RAW .. "reporter.lua")
	if fetchSuccess and #fetchResult > 0 then
		local execSuccess, Analytics = pcall(function()
			return (loadstring(fetchResult) :: any)()
		end)
		if execSuccess and Analytics then
			pcall(function()
				reporter = Analytics.new({
					url          = "https://rayfield-collect.sirius-software-ltd.workers.dev",
					token        = ANALYTICS_TOKEN,
					product_name = "Rayfield",
					category     = "UILibrary",
				})
			end)
		end
	end
	return reporter
end

-- Whether analytics may be sent right now. A saved opt-out is only known once the settings file has
-- been applied, so until then the answer is no; an executor that can't read files has nothing saved
-- to respect, so the default applies there, and getgenv().RAYFIELD_ANALYTICS = false is the
-- player's way to opt out.
local function analyticsAllowed(): boolean
	if requestsDisabled or analyticsOptOut or useStudio then return false end
	if not getSetting("System", "usageAnalytics") then return false end
	return settingsInitialized or not (isfile and readfile)
end

-- Whether analyticsAllowed() has a final answer yet, rather than waiting on the settings file.
local function analyticsDecided(): boolean
	if requestsDisabled or analyticsOptOut or useStudio then return true end
	if not getSetting("System", "usageAnalytics") then return true end
	return settingsInitialized or not (isfile and readfile)
end

-- Sentivel heartbeats. A heartbeat monitor is a dead-man's switch: it stays green while pings keep
-- arriving and alarms once they stop. Rayfield pings its own below, and a window made with
-- Settings.Heartbeat pings the developer's own for as long as it's up. Best-effort throughout: a
-- ping never throws or blocks. Only a bad link, or a token Sentivel doesn't know, warns, since
-- either would otherwise look exactly like an outage. Secure mode silences those like any warn.
local HEARTBEAT_BASE = "https://www.sentivel.com/api/heartbeat/"

-- Seconds between a window's pings. A monitor expecting a ping every 5 minutes, with a little
-- grace, stays green for as long as anyone has the script open.
local HEARTBEAT_PERIOD = 300

-- Consecutive 404s before a loop gives up. Sentivel answers 404 for a token it doesn't know, which
-- never recovers, but one stray 404 from a bad deploy shouldn't silence every session.
local HEARTBEAT_GIVE_UP = 3

-- the loop that currently owns each ping URL. a newer window on the same link takes it over and
-- the older loop retires when it next wakes, so the link is never pinged twice over, and a window
-- rebuilt straight after Destroy isn't turned away by a loop that's still asleep
local heartbeatOwners = {}

-- A full ping URL or its bare token, to the canonical URL. nil and a reason when it isn't one.
local function resolveHeartbeat(target: any): (string?, string?)
	if type(target) ~= "string" then
		return nil, "Heartbeat takes your Sentivel ping URL or token as a string, got " .. typeof(target)
	end
	-- a real link is under 100 characters; this keeps the trim below cheap on anything absurd
	if #target > 512 then
		return nil, "Heartbeat is far too long to be a Sentivel ping URL. Copy the ping URL and try again"
	end

	-- a copy out of Discord or a browser can drag along no-break and zero-width spaces, which %s
	-- doesn't cover
	local cleaned = string.gsub(string.gsub(target, "\194\160", " "), "\226\128\139", "")
	cleaned = string.gsub(cleaned, "\239\187\191", "")
	local trimmed = string.match(cleaned, "^%s*(.-)%s*$") :: string
	if trimmed == "" then
		return nil, "Heartbeat is empty. Paste the ping URL from your Sentivel heartbeat monitor"
	end

	-- a link pasted without its scheme is still a link
	if not string.find(trimmed, "://", 1, true) and string.find(trimmed, "/", 1, true) then
		trimmed = "https://" .. trimmed
	end

	local token = trimmed
	if string.find(trimmed, "://", 1, true) then
		-- host first, on its own, so a Sentivel link that's just the wrong page is told that. the
		-- default port and a fully qualified trailing dot name the same host
		local host, rest = string.match(trimmed, "^[Hh][Tt][Tt][Pp][Ss]?://([^/?#]+)(.*)$")
		local bare = if host then string.gsub(string.gsub(string.lower(host), ":443$", ""), "%.$", "") else nil
		if bare ~= "sentivel.com" and bare ~= "www.sentivel.com" then
			return nil, "Heartbeat only pings Sentivel. Use the ping URL from your heartbeat monitor"
		end
		local found = string.match(rest or "", "^/api/heartbeat/([^/?#]+)/?$")
		if not found then
			return nil, "That Sentivel link isn't a heartbeat ping URL. It should look like " .. HEARTBEAT_BASE .. "<token>"
		end
		token = found
	end

	-- tokens are hex. the bounds are loose so a future token format still passes; a monitor id (a
	-- UUID, so it has dashes) falls outside them and is told why
	if #token < 32 or #token > 128 or not string.match(token, "^%x+$") then
		if string.match(token, "^%x+%-%x+%-%x+%-%x+%-%x+$") then
			return nil, "That looks like a monitor ID. Heartbeat needs the monitor's ping URL, not its ID"
		end
		return nil, "That doesn't look like a Sentivel heartbeat token. Copy the whole ping URL and try again"
	end

	-- always www: the bare domain answers with a redirect, one more round trip per ping. and
	-- lowercase: Sentivel issues lowercase tokens and matches them exactly
	return HEARTBEAT_BASE .. string.lower(token), nil
end

-- One ping. The HTTP status when it can be seen, otherwise nil. HttpGet goes first: the executor's
-- request function adds headers that identify the executor and the player's machine, and those
-- have no business reaching a third party. HttpGet throws on a failed request, so a 404 is read
-- out of its error. The request function is only used when HttpGet is missing or fails for
-- another reason. Yields, so call it from its own thread.
local function sendHeartbeat(url: string): number?
	local ok, err = pcall(function()
		return (game :: any):HttpGet(url)
	end)
	if ok then
		return 200
	end
	if string.find(tostring(err), "404", 1, true) then
		return 404
	end
	if requestFunc then
		local sent, response = pcall(requestFunc, { Url = url, Method = "GET" })
		-- some executors hand the status back as a string
		return if sent and type(response) == "table" then tonumber(response.StatusCode) else nil
	end
	return nil
end

-- Heartbeats count as analytics. Waits until analyticsAllowed() says yes, for up to
-- HEARTBEAT_PERIOD, while `wanted` holds. false once the answer is no, or it never came.
local function awaitAnalyticsConsent(wanted: () -> boolean): boolean
	local waited = 0
	while not analyticsAllowed() do
		if analyticsDecided() or waited >= HEARTBEAT_PERIOD or not wanted() then
			return false
		end
		task.wait(1)
		waited += 1
	end
	return true
end

-- Ping `target` every HEARTBEAT_PERIOD for as long as `alive` says so and the player's analytics
-- choice allows it. false when the link is bad (which warns), or when running in Studio, where
-- playtests aren't real runs.
local function startHeartbeat(target: any, alive: () -> boolean): boolean
	local url, reason = resolveHeartbeat(target)
	if not url then
		warn("Rayfield | " .. tostring(reason) .. ".")
		return false
	end
	if useStudio then
		return false
	end

	local resolved = url :: string
	local owner = {}
	heartbeatOwners[resolved] = owner
	-- deferred rather than spawned: spawning runs the first ping right away, and a request that
	-- blocks without yielding would hold CreateWindow up for a whole round trip
	task.defer(function()
		local function owned()
			return heartbeatOwners[resolved] == owner and alive()
		end
		-- nothing is sent until the player's analytics choice is known, and an opt-out, then or
		-- mid-session, ends the loop
		if not awaitAnalyticsConsent(owned) then
			if heartbeatOwners[resolved] == owner then
				heartbeatOwners[resolved] = nil
			end
			return
		end
		local notFound = 0
		while owned() and analyticsAllowed() do
			-- a 404 is Sentivel saying the token names no heartbeat (deleted, regenerated, or
			-- mistyped into another valid-looking one). once it keeps saying so, stop asking
			notFound = if sendHeartbeat(resolved) == 404 then notFound + 1 else 0
			if notFound >= HEARTBEAT_GIVE_UP then
				warn("Rayfield | Sentivel doesn't recognise this heartbeat, so pings have stopped. Check the ping URL.")
				break
			end
			task.wait(HEARTBEAT_PERIOD)
		end
		if heartbeatOwners[resolved] == owner then
			heartbeatOwners[resolved] = nil
		end
	end)
	return true
end

if debugX then
	warn('Moving on to continue initialisation')
end

local RayfieldLibrary = {
	Flags = {},
	Theme = {
		Default = {
			TextColor = Color3.fromRGB(240, 240, 240),

			Background = Color3.fromRGB(25, 25, 25),
			Topbar = Color3.fromRGB(34, 34, 34),
			Shadow = Color3.fromRGB(20, 20, 20),

			NotificationBackground = Color3.fromRGB(20, 20, 20),
			NotificationActionsBackground = Color3.fromRGB(230, 230, 230),

			TabBackground = Color3.fromRGB(80, 80, 80),
			TabStroke = Color3.fromRGB(85, 85, 85),
			TabBackgroundSelected = Color3.fromRGB(210, 210, 210),
			TabTextColor = Color3.fromRGB(240, 240, 240),
			SelectedTabTextColor = Color3.fromRGB(50, 50, 50),

			ElementBackground = Color3.fromRGB(35, 35, 35),
			ElementBackgroundHover = Color3.fromRGB(40, 40, 40),
			SecondaryElementBackground = Color3.fromRGB(25, 25, 25),
			ElementStroke = Color3.fromRGB(50, 50, 50),
			SecondaryElementStroke = Color3.fromRGB(40, 40, 40),

			SliderBackground = Color3.fromRGB(50, 138, 220),
			SliderProgress = Color3.fromRGB(50, 138, 220),
			SliderStroke = Color3.fromRGB(58, 163, 255),

			ToggleBackground = Color3.fromRGB(30, 30, 30),
			ToggleEnabled = Color3.fromRGB(0, 146, 214),
			ToggleDisabled = Color3.fromRGB(100, 100, 100),
			ToggleEnabledStroke = Color3.fromRGB(0, 170, 255),
			ToggleDisabledStroke = Color3.fromRGB(125, 125, 125),
			ToggleEnabledOuterStroke = Color3.fromRGB(100, 100, 100),
			ToggleDisabledOuterStroke = Color3.fromRGB(65, 65, 65),

			DropdownSelected = Color3.fromRGB(40, 40, 40),
			DropdownUnselected = Color3.fromRGB(30, 30, 30),

			InputBackground = Color3.fromRGB(30, 30, 30),
			InputStroke = Color3.fromRGB(65, 65, 65),
			PlaceholderColor = Color3.fromRGB(178, 178, 178)
		},

		Ocean = {
			TextColor = Color3.fromRGB(230, 240, 240),

			Background = Color3.fromRGB(20, 30, 30),
			Topbar = Color3.fromRGB(25, 40, 40),
			Shadow = Color3.fromRGB(15, 20, 20),

			NotificationBackground = Color3.fromRGB(25, 35, 35),
			NotificationActionsBackground = Color3.fromRGB(230, 240, 240),

			TabBackground = Color3.fromRGB(40, 60, 60),
			TabStroke = Color3.fromRGB(50, 70, 70),
			TabBackgroundSelected = Color3.fromRGB(100, 180, 180),
			TabTextColor = Color3.fromRGB(210, 230, 230),
			SelectedTabTextColor = Color3.fromRGB(20, 50, 50),

			ElementBackground = Color3.fromRGB(30, 50, 50),
			ElementBackgroundHover = Color3.fromRGB(40, 60, 60),
			SecondaryElementBackground = Color3.fromRGB(30, 45, 45),
			ElementStroke = Color3.fromRGB(45, 70, 70),
			SecondaryElementStroke = Color3.fromRGB(40, 65, 65),

			SliderBackground = Color3.fromRGB(0, 110, 110),
			SliderProgress = Color3.fromRGB(0, 140, 140),
			SliderStroke = Color3.fromRGB(0, 160, 160),

			ToggleBackground = Color3.fromRGB(30, 50, 50),
			ToggleEnabled = Color3.fromRGB(0, 130, 130),
			ToggleDisabled = Color3.fromRGB(70, 90, 90),
			ToggleEnabledStroke = Color3.fromRGB(0, 160, 160),
			ToggleDisabledStroke = Color3.fromRGB(85, 105, 105),
			ToggleEnabledOuterStroke = Color3.fromRGB(50, 100, 100),
			ToggleDisabledOuterStroke = Color3.fromRGB(45, 65, 65),

			DropdownSelected = Color3.fromRGB(30, 60, 60),
			DropdownUnselected = Color3.fromRGB(25, 40, 40),

			InputBackground = Color3.fromRGB(30, 50, 50),
			InputStroke = Color3.fromRGB(50, 70, 70),
			PlaceholderColor = Color3.fromRGB(140, 160, 160)
		},

		AmberGlow = {
			TextColor = Color3.fromRGB(255, 245, 230),

			Background = Color3.fromRGB(45, 30, 20),
			Topbar = Color3.fromRGB(55, 40, 25),
			Shadow = Color3.fromRGB(35, 25, 15),

			NotificationBackground = Color3.fromRGB(50, 35, 25),
			NotificationActionsBackground = Color3.fromRGB(245, 230, 215),

			TabBackground = Color3.fromRGB(75, 50, 35),
			TabStroke = Color3.fromRGB(90, 60, 45),
			TabBackgroundSelected = Color3.fromRGB(230, 180, 100),
			TabTextColor = Color3.fromRGB(250, 220, 200),
			SelectedTabTextColor = Color3.fromRGB(50, 30, 10),

			ElementBackground = Color3.fromRGB(60, 45, 35),
			ElementBackgroundHover = Color3.fromRGB(70, 50, 40),
			SecondaryElementBackground = Color3.fromRGB(55, 40, 30),
			ElementStroke = Color3.fromRGB(85, 60, 45),
			SecondaryElementStroke = Color3.fromRGB(75, 50, 35),

			SliderBackground = Color3.fromRGB(220, 130, 60),
			SliderProgress = Color3.fromRGB(250, 150, 75),
			SliderStroke = Color3.fromRGB(255, 170, 85),

			ToggleBackground = Color3.fromRGB(55, 40, 30),
			ToggleEnabled = Color3.fromRGB(240, 130, 30),
			ToggleDisabled = Color3.fromRGB(90, 70, 60),
			ToggleEnabledStroke = Color3.fromRGB(255, 160, 50),
			ToggleDisabledStroke = Color3.fromRGB(110, 85, 75),
			ToggleEnabledOuterStroke = Color3.fromRGB(200, 100, 50),
			ToggleDisabledOuterStroke = Color3.fromRGB(75, 60, 55),

			DropdownSelected = Color3.fromRGB(70, 50, 40),
			DropdownUnselected = Color3.fromRGB(55, 40, 30),

			InputBackground = Color3.fromRGB(60, 45, 35),
			InputStroke = Color3.fromRGB(90, 65, 50),
			PlaceholderColor = Color3.fromRGB(190, 150, 130)
		},

		Light = {
			TextColor = Color3.fromRGB(40, 40, 40),

			Background = Color3.fromRGB(245, 245, 245),
			Topbar = Color3.fromRGB(230, 230, 230),
			Shadow = Color3.fromRGB(200, 200, 200),

			NotificationBackground = Color3.fromRGB(250, 250, 250),
			NotificationActionsBackground = Color3.fromRGB(240, 240, 240),

			TabBackground = Color3.fromRGB(235, 235, 235),
			TabStroke = Color3.fromRGB(215, 215, 215),
			TabBackgroundSelected = Color3.fromRGB(255, 255, 255),
			TabTextColor = Color3.fromRGB(80, 80, 80),
			SelectedTabTextColor = Color3.fromRGB(0, 0, 0),

			ElementBackground = Color3.fromRGB(240, 240, 240),
			ElementBackgroundHover = Color3.fromRGB(225, 225, 225),
			SecondaryElementBackground = Color3.fromRGB(235, 235, 235),
			ElementStroke = Color3.fromRGB(210, 210, 210),
			SecondaryElementStroke = Color3.fromRGB(210, 210, 210),

			SliderBackground = Color3.fromRGB(150, 180, 220),
			SliderProgress = Color3.fromRGB(100, 150, 200), 
			SliderStroke = Color3.fromRGB(120, 170, 220),

			ToggleBackground = Color3.fromRGB(220, 220, 220),
			ToggleEnabled = Color3.fromRGB(0, 146, 214),
			ToggleDisabled = Color3.fromRGB(150, 150, 150),
			ToggleEnabledStroke = Color3.fromRGB(0, 170, 255),
			ToggleDisabledStroke = Color3.fromRGB(170, 170, 170),
			ToggleEnabledOuterStroke = Color3.fromRGB(100, 100, 100),
			ToggleDisabledOuterStroke = Color3.fromRGB(180, 180, 180),

			DropdownSelected = Color3.fromRGB(230, 230, 230),
			DropdownUnselected = Color3.fromRGB(220, 220, 220),

			InputBackground = Color3.fromRGB(240, 240, 240),
			InputStroke = Color3.fromRGB(180, 180, 180),
			PlaceholderColor = Color3.fromRGB(140, 140, 140)
		},

		Amethyst = {
			TextColor = Color3.fromRGB(240, 240, 240),

			Background = Color3.fromRGB(30, 20, 40),
			Topbar = Color3.fromRGB(40, 25, 50),
			Shadow = Color3.fromRGB(20, 15, 30),

			NotificationBackground = Color3.fromRGB(35, 20, 40),
			NotificationActionsBackground = Color3.fromRGB(240, 240, 250),

			TabBackground = Color3.fromRGB(60, 40, 80),
			TabStroke = Color3.fromRGB(70, 45, 90),
			TabBackgroundSelected = Color3.fromRGB(180, 140, 200),
			TabTextColor = Color3.fromRGB(230, 230, 240),
			SelectedTabTextColor = Color3.fromRGB(50, 20, 50),

			ElementBackground = Color3.fromRGB(45, 30, 60),
			ElementBackgroundHover = Color3.fromRGB(50, 35, 70),
			SecondaryElementBackground = Color3.fromRGB(40, 30, 55),
			ElementStroke = Color3.fromRGB(70, 50, 85),
			SecondaryElementStroke = Color3.fromRGB(65, 45, 80),

			SliderBackground = Color3.fromRGB(100, 60, 150),
			SliderProgress = Color3.fromRGB(130, 80, 180),
			SliderStroke = Color3.fromRGB(150, 100, 200),

			ToggleBackground = Color3.fromRGB(45, 30, 55),
			ToggleEnabled = Color3.fromRGB(120, 60, 150),
			ToggleDisabled = Color3.fromRGB(94, 47, 117),
			ToggleEnabledStroke = Color3.fromRGB(140, 80, 170),
			ToggleDisabledStroke = Color3.fromRGB(124, 71, 150),
			ToggleEnabledOuterStroke = Color3.fromRGB(90, 40, 120),
			ToggleDisabledOuterStroke = Color3.fromRGB(80, 50, 110),

			DropdownSelected = Color3.fromRGB(50, 35, 70),
			DropdownUnselected = Color3.fromRGB(35, 25, 50),

			InputBackground = Color3.fromRGB(45, 30, 60),
			InputStroke = Color3.fromRGB(80, 50, 110),
			PlaceholderColor = Color3.fromRGB(178, 150, 200)
		},

		Green = {
			TextColor = Color3.fromRGB(30, 60, 30),

			Background = Color3.fromRGB(235, 245, 235),
			Topbar = Color3.fromRGB(210, 230, 210),
			Shadow = Color3.fromRGB(200, 220, 200),

			NotificationBackground = Color3.fromRGB(240, 250, 240),
			NotificationActionsBackground = Color3.fromRGB(220, 235, 220),

			TabBackground = Color3.fromRGB(215, 235, 215),
			TabStroke = Color3.fromRGB(190, 210, 190),
			TabBackgroundSelected = Color3.fromRGB(245, 255, 245),
			TabTextColor = Color3.fromRGB(50, 80, 50),
			SelectedTabTextColor = Color3.fromRGB(20, 60, 20),

			ElementBackground = Color3.fromRGB(225, 240, 225),
			ElementBackgroundHover = Color3.fromRGB(210, 225, 210),
			SecondaryElementBackground = Color3.fromRGB(235, 245, 235), 
			ElementStroke = Color3.fromRGB(180, 200, 180),
			SecondaryElementStroke = Color3.fromRGB(180, 200, 180),

			SliderBackground = Color3.fromRGB(90, 160, 90),
			SliderProgress = Color3.fromRGB(70, 130, 70),
			SliderStroke = Color3.fromRGB(100, 180, 100),

			ToggleBackground = Color3.fromRGB(215, 235, 215),
			ToggleEnabled = Color3.fromRGB(60, 130, 60),
			ToggleDisabled = Color3.fromRGB(150, 175, 150),
			ToggleEnabledStroke = Color3.fromRGB(80, 150, 80),
			ToggleDisabledStroke = Color3.fromRGB(130, 150, 130),
			ToggleEnabledOuterStroke = Color3.fromRGB(100, 160, 100),
			ToggleDisabledOuterStroke = Color3.fromRGB(160, 180, 160),

			DropdownSelected = Color3.fromRGB(225, 240, 225),
			DropdownUnselected = Color3.fromRGB(210, 225, 210),

			InputBackground = Color3.fromRGB(235, 245, 235),
			InputStroke = Color3.fromRGB(180, 200, 180),
			PlaceholderColor = Color3.fromRGB(120, 140, 120)
		},

		Bloom = {
			TextColor = Color3.fromRGB(60, 40, 50),

			Background = Color3.fromRGB(255, 240, 245),
			Topbar = Color3.fromRGB(250, 220, 225),
			Shadow = Color3.fromRGB(230, 190, 195),

			NotificationBackground = Color3.fromRGB(255, 235, 240),
			NotificationActionsBackground = Color3.fromRGB(245, 215, 225),

			TabBackground = Color3.fromRGB(240, 210, 220),
			TabStroke = Color3.fromRGB(230, 200, 210),
			TabBackgroundSelected = Color3.fromRGB(255, 225, 235),
			TabTextColor = Color3.fromRGB(80, 40, 60),
			SelectedTabTextColor = Color3.fromRGB(50, 30, 50),

			ElementBackground = Color3.fromRGB(255, 235, 240),
			ElementBackgroundHover = Color3.fromRGB(245, 220, 230),
			SecondaryElementBackground = Color3.fromRGB(255, 235, 240), 
			ElementStroke = Color3.fromRGB(230, 200, 210),
			SecondaryElementStroke = Color3.fromRGB(230, 200, 210),

			SliderBackground = Color3.fromRGB(240, 130, 160),
			SliderProgress = Color3.fromRGB(250, 160, 180),
			SliderStroke = Color3.fromRGB(255, 180, 200),

			ToggleBackground = Color3.fromRGB(240, 210, 220),
			ToggleEnabled = Color3.fromRGB(255, 140, 170),
			ToggleDisabled = Color3.fromRGB(200, 180, 185),
			ToggleEnabledStroke = Color3.fromRGB(250, 160, 190),
			ToggleDisabledStroke = Color3.fromRGB(210, 180, 190),
			ToggleEnabledOuterStroke = Color3.fromRGB(220, 160, 180),
			ToggleDisabledOuterStroke = Color3.fromRGB(190, 170, 180),

			DropdownSelected = Color3.fromRGB(250, 220, 225),
			DropdownUnselected = Color3.fromRGB(240, 210, 220),

			InputBackground = Color3.fromRGB(255, 235, 240),
			InputStroke = Color3.fromRGB(220, 190, 200),
			PlaceholderColor = Color3.fromRGB(170, 130, 140)
		},

		DarkBlue = {
			TextColor = Color3.fromRGB(230, 230, 230),

			Background = Color3.fromRGB(20, 25, 30),
			Topbar = Color3.fromRGB(30, 35, 40),
			Shadow = Color3.fromRGB(15, 20, 25),

			NotificationBackground = Color3.fromRGB(25, 30, 35),
			NotificationActionsBackground = Color3.fromRGB(45, 50, 55),

			TabBackground = Color3.fromRGB(35, 40, 45),
			TabStroke = Color3.fromRGB(45, 50, 60),
			TabBackgroundSelected = Color3.fromRGB(40, 70, 100),
			TabTextColor = Color3.fromRGB(200, 200, 200),
			SelectedTabTextColor = Color3.fromRGB(255, 255, 255),

			ElementBackground = Color3.fromRGB(30, 35, 40),
			ElementBackgroundHover = Color3.fromRGB(40, 45, 50),
			SecondaryElementBackground = Color3.fromRGB(35, 40, 45), 
			ElementStroke = Color3.fromRGB(45, 50, 60),
			SecondaryElementStroke = Color3.fromRGB(40, 45, 55),

			SliderBackground = Color3.fromRGB(0, 90, 180),
			SliderProgress = Color3.fromRGB(0, 120, 210),
			SliderStroke = Color3.fromRGB(0, 150, 240),

			ToggleBackground = Color3.fromRGB(35, 40, 45),
			ToggleEnabled = Color3.fromRGB(0, 120, 210),
			ToggleDisabled = Color3.fromRGB(70, 70, 80),
			ToggleEnabledStroke = Color3.fromRGB(0, 150, 240),
			ToggleDisabledStroke = Color3.fromRGB(75, 75, 85),
			ToggleEnabledOuterStroke = Color3.fromRGB(20, 100, 180), 
			ToggleDisabledOuterStroke = Color3.fromRGB(55, 55, 65),

			DropdownSelected = Color3.fromRGB(30, 70, 90),
			DropdownUnselected = Color3.fromRGB(25, 30, 35),

			InputBackground = Color3.fromRGB(25, 30, 35),
			InputStroke = Color3.fromRGB(45, 50, 60), 
			PlaceholderColor = Color3.fromRGB(150, 150, 160)
		},

		Serenity = {
			TextColor = Color3.fromRGB(50, 55, 60),
			Background = Color3.fromRGB(240, 245, 250),
			Topbar = Color3.fromRGB(215, 225, 235),
			Shadow = Color3.fromRGB(200, 210, 220),

			NotificationBackground = Color3.fromRGB(210, 220, 230),
			NotificationActionsBackground = Color3.fromRGB(225, 230, 240),

			TabBackground = Color3.fromRGB(200, 210, 220),
			TabStroke = Color3.fromRGB(180, 190, 200),
			TabBackgroundSelected = Color3.fromRGB(175, 185, 200),
			TabTextColor = Color3.fromRGB(50, 55, 60),
			SelectedTabTextColor = Color3.fromRGB(30, 35, 40),

			ElementBackground = Color3.fromRGB(210, 220, 230),
			ElementBackgroundHover = Color3.fromRGB(220, 230, 240),
			SecondaryElementBackground = Color3.fromRGB(200, 210, 220),
			ElementStroke = Color3.fromRGB(190, 200, 210),
			SecondaryElementStroke = Color3.fromRGB(180, 190, 200),

			SliderBackground = Color3.fromRGB(200, 220, 235),  -- Lighter shade
			SliderProgress = Color3.fromRGB(70, 130, 180),
			SliderStroke = Color3.fromRGB(150, 180, 220),

			ToggleBackground = Color3.fromRGB(210, 220, 230),
			ToggleEnabled = Color3.fromRGB(70, 160, 210),
			ToggleDisabled = Color3.fromRGB(180, 180, 180),
			ToggleEnabledStroke = Color3.fromRGB(60, 150, 200),
			ToggleDisabledStroke = Color3.fromRGB(140, 140, 140),
			ToggleEnabledOuterStroke = Color3.fromRGB(100, 120, 140),
			ToggleDisabledOuterStroke = Color3.fromRGB(120, 120, 130),

			DropdownSelected = Color3.fromRGB(220, 230, 240),
			DropdownUnselected = Color3.fromRGB(200, 210, 220),

			InputBackground = Color3.fromRGB(220, 230, 240),
			InputStroke = Color3.fromRGB(180, 190, 200),
			PlaceholderColor = Color3.fromRGB(150, 150, 150)
		},
	}
}




-- Interface Management

local RayfieldAssetId = customAssetId or 10804731440
local Rayfield = useStudio and script.Parent:FindFirstChild('Rayfield') or game:GetObjects("rbxassetid://"..RayfieldAssetId)[1]
local buildAttempts = 0
local correctBuild = false
local warned
local globalLoaded
local rayfieldDestroyed = false -- True when RayfieldLibrary:Destroy() is called

-- Rayfield's own heartbeat. About 1 in 200 sessions take part, and each one that does pings every
-- HEARTBEAT_PERIOD for as long as Rayfield stays loaded. One ping per sampled load left gaps of
-- several minutes at quiet hours, which the monitor read as an outage; a sampled session that
-- keeps pinging covers those gaps without sampling more people. Like the reporter it waits for the
-- player's analytics choice, and sends nothing when they or the developer have turned it off.
if not requestsDisabled and not analyticsOptOut and not useStudio and math.random(200) == 1 then
	task.defer(function()
		local url = HEARTBEAT_BASE .. "81074364b461f8da81bad6fdc363c3b927f884d6fc28d806a15ee50ca1e68c78"
		if not awaitAnalyticsConsent(function() return not rayfieldDestroyed end) then
			return
		end
		-- the first ping skips the interface check: a script that hasn't opened a window on an
		-- executor without files gets here before the interface is parented
		sendHeartbeat(url)
		while true do
			task.wait(HEARTBEAT_PERIOD)
			if rayfieldDestroyed or not Rayfield or Rayfield.Parent == nil or Rayfield.Name == "Rayfield-Old" then
				break
			end
			if not analyticsAllowed() then
				break
			end
			sendHeartbeat(url)
		end
	end)
end

repeat
	if Rayfield:FindFirstChild('Build') and Rayfield.Build.Value == InterfaceBuild then
		correctBuild = true
		break
	end

	correctBuild = false

	if not warned then
		warn('Rayfield | Build Mismatch')
		print('Rayfield may encounter issues as you are running an incompatible interface version ('.. ((Rayfield:FindFirstChild('Build') and Rayfield.Build.Value) or 'No Build') ..').\n\nThis version of Rayfield is intended for interface build '..InterfaceBuild..'.')
		warned = true
	end

	local toDestroy
	toDestroy, Rayfield = Rayfield, useStudio and script.Parent:FindFirstChild('Rayfield') or game:GetObjects("rbxassetid://"..RayfieldAssetId)[1]
	if toDestroy and not useStudio then toDestroy:Destroy() end

	buildAttempts = buildAttempts + 1
until buildAttempts >= 2

Rayfield.Enabled = false

if gethui then
	Rayfield.Parent = gethui()
elseif syn and syn.protect_gui then 
	syn.protect_gui(Rayfield)
	Rayfield.Parent = CoreGui
elseif not useStudio and CoreGui:FindFirstChild("RobloxGui") then
	Rayfield.Parent = CoreGui:FindFirstChild("RobloxGui")
elseif not useStudio then
	Rayfield.Parent = CoreGui
end

-- Running a script again loads a second copy of Rayfield. The copy it replaces is torn down through
-- this event, which calls its Destroy: that removes its interface and disconnects its input
-- listeners, which would otherwise keep answering hotkeys for a window nobody can see. Builds
-- before 1.753 have no event, so those are only hidden and renamed, as before.
local TEARDOWN_EVENT = "RayfieldTeardown"

local function retireInterface(Interface: any)
	Interface.Enabled = false
	Interface.Name = "Rayfield-Old"
	local teardown = Interface:FindFirstChild(TEARDOWN_EVENT)
	if teardown and teardown:IsA("BindableEvent") then
		pcall(function()
			teardown:Fire()
		end)
	end
end

if gethui then
	for _, Interface in ipairs(gethui():GetChildren()) do
		if Interface.Name == Rayfield.Name and Interface ~= Rayfield then
			retireInterface(Interface)
		end
	end
elseif not useStudio then
	for _, Interface in ipairs(CoreGui:GetChildren()) do
		if Interface.Name == Rayfield.Name and Interface ~= Rayfield then
			retireInterface(Interface)
		end
	end
end

do
	local teardown = Instance.new("BindableEvent")
	teardown.Name = TEARDOWN_EVENT
	teardown.Event:Connect(function()
		if not rayfieldDestroyed and type(RayfieldLibrary.Destroy) == "function" then
			RayfieldLibrary:Destroy()
		end
	end)
	teardown.Parent = Rayfield
end

if secureMode and not customAssetId then
	secureNotify("default_asset", "Secure Mode", "You are using the default Rayfield asset ID. Set RAYFIELD_ASSET_ID to a custom upload to avoid detection.")
end

do
	local AssetPath = RayfieldFolder.."/Assets"
	local AssetBaseURL = "https://github.com/SiriusSoftwareLtd/Rayfield/blob/main/assets/"

	local assetFiles = {
		["111263549366178"] = AssetBaseURL.."111263549366178.png?raw=true",
		["77891951053543"] = AssetBaseURL.."77891951053543.png?raw=true",
		["78137979054938"] = AssetBaseURL.."78137979054938.png?raw=true",
		["80503127983237"] = AssetBaseURL.."80503127983237.png?raw=true",
		["10137832201"] = AssetBaseURL.."10137832201.png?raw=true",
		["10137941941"] = AssetBaseURL.."10137941941.png?raw=true",
		["11036884234"] = AssetBaseURL.."11036884234.png?raw=true",
		["11413591840"] = AssetBaseURL.."11413591840.png?raw=true",
		["11745872910"] = AssetBaseURL.."11745872910.png?raw=true",
		["12577727209"] = AssetBaseURL.."12577727209.png?raw=true",
		["18458939117"] = AssetBaseURL.."18458939117.png?raw=true",
		["3259050989"] = AssetBaseURL.."3259050989.png?raw=true",
		["3523728077"] = AssetBaseURL.."3523728077.png?raw=true",
		["3602733521"] = AssetBaseURL.."3602733521.png?raw=true",
		["IconChevronTopMedium"] = AssetBaseURL.."IconChevronTopMedium.png?raw=true",
		["4483362458"] = AssetBaseURL.."4483362458.png?raw=true",
		["5587865193"] = AssetBaseURL.."5587865193.png?raw=true",
		["IconMagnifyingGlass2"] = AssetBaseURL.."IconMagnifyingGlass2.png?raw=true",
	}

	for id, _ in assetFiles do
		customAssets[tostring(id)] = ""
	end

	local hasCustomAsset = type(getcustomasset) == "function"
	local hasFilesystem = type(writefile) == "function" and type(makefolder) == "function" and type(isfile) == "function" and type(isfolder) == "function"

	if hasCustomAsset and hasFilesystem then
		local ok, err = pcall(function()
			ensureFolder(RayfieldFolder)
			ensureFolder(AssetPath)

			-- skip ids we've already tried so a dead asset can't loop the loader forever
			local attempted = {}
			local function nextToFetch()
				for id, _ in assetFiles do
					if not attempted[id] and not isfile(AssetPath.."/"..tostring(id)..".png") then
						return id
					end
				end
				return nil
			end

			if nextToFetch() then
				task.spawn(function()
					while true do
						local id = nextToFetch()
						if not id then break end
						-- a failed request can hand back a nil/empty Body — never pass that to writefile
						local ok, res = pcall(requestFunc, {Url = assetFiles[id], Method = "GET"})
						if ok and type(res) == "table" and type(res.Body) == "string" and #res.Body > 0 then
							pcall(writefile, AssetPath.."/"..tostring(id)..".png", res.Body)
						end
						-- mark after the attempt so the poll waits for real downloads but still skips a dead asset
						attempted[id] = true
						task.wait()
					end
				end)

				while nextToFetch() do
					task.wait(0.1)
				end
			end

			for id, _ in assetFiles do
				local success, asset = pcall(getcustomasset, AssetPath.."/"..tostring(id)..".png")
				if success then
					customAssets[tostring(id)] = asset
				else
					warn("Rayfield | Failed to load custom asset: "..tostring(id).." - "..tostring(asset))
				end
			end
		end)

		if not ok then
			warn("Rayfield | Failed to load custom assets: "..tostring(err))
			secureNotify("asset_load_fail", "Rayfield", "Failed to load custom assets. UI images may not display correctly.")
		end
	else
		secureNotify("no_getcustomasset", "Rayfield", "Your executor does not support getcustomasset. Some UI images may not render correctly.")
	end


	Rayfield.Main.Shadow.Image.Image = customAssets[tostring(5587865193)]
	Rayfield.Main.Topbar.Hide.Image = customAssets[tostring(10137832201)]
	Rayfield.Main.Topbar.ChangeSize.Image = customAssets[tostring(10137941941)]
	Rayfield.Main.Topbar.Settings.Image = customAssets[tostring(80503127983237)]
	Rayfield.Main.Topbar.Icon.Image = customAssets[tostring(78137979054938)]
	Rayfield.Main.Topbar.Search.Image = customAssets["IconMagnifyingGlass2"]
	Rayfield.Main.Topbar.Search.ImageRectOffset = Vector2.new(0, 0)
	Rayfield.Main.Topbar.Search.ImageRectSize = Vector2.new(0, 0)
	Rayfield.Main.Elements.Template.Toggle.Switch.Shadow.Image = customAssets[tostring(3602733521)]
	Rayfield.Main.Elements.Template.Slider.Main.Shadow.Image = customAssets[tostring(3602733521)]
	Rayfield.Main.Elements.Template.Dropdown.Toggle.Image = customAssets["IconChevronTopMedium"]
	Rayfield.Main.Elements.Template.Dropdown.Toggle.ImageRectOffset = Vector2.new(0, 0)
	Rayfield.Main.Elements.Template.Dropdown.Toggle.ImageRectSize = Vector2.new(0, 0)
	Rayfield.Main.Elements.Template.Label.Icon.Image = customAssets[tostring(11745872910)]
	Rayfield.Main.Elements.Template.ColorPicker.CPBackground.MainCP.Image = customAssets[tostring(11413591840)]
	Rayfield.Main.Elements.Template.ColorPicker.CPBackground.MainCP.MainPoint.Image = customAssets[tostring(3259050989)]
	Rayfield.Main.Elements.Template.ColorPicker.ColorSlider.SliderPoint.Image = customAssets[tostring(3259050989)]
	Rayfield.Main.TabList.Template.Image.Image = customAssets[tostring(4483362458)]
	Rayfield.Main.Search.Search.Image = customAssets[tostring(18458939117)]
	Rayfield.Main.Search.Shadow.Image = customAssets[tostring(5587865193)]
	Rayfield.Notifications.Template.Icon.Image = customAssets[tostring(77891951053543)]
	Rayfield.Notifications.Template.Shadow.Image = customAssets[tostring(3523728077)]
	Rayfield.Loading.Banner.Image = customAssets[tostring(111263549366178)]

end -- custom asset block

local minSize = Vector2.new(1024, 768)
local useMobileSizing

if Rayfield.AbsoluteSize.X < minSize.X and Rayfield.AbsoluteSize.Y < minSize.Y then
	useMobileSizing = true
end

local useMobilePrompt = false
if UserInputService.TouchEnabled then
	useMobilePrompt = true
end


-- Object Variables

local Main = Rayfield.Main
local MPrompt = Rayfield:FindFirstChild('Prompt')
local Topbar = Main.Topbar
local Elements = Main.Elements
local LoadingFrame = Main.LoadingFrame
local TabList = Main.TabList
local dragBar = Rayfield:FindFirstChild('Drag')
local dragInteract = dragBar and dragBar.Interact or nil
local dragBarCosmetic = dragBar and dragBar.Drag or nil

local dragOffset = 255
local dragOffsetMobile = 150

Rayfield.DisplayOrder = 100
LoadingFrame.Version.Text = Release

-- Thanks to Latte Softworks for the Lucide integration for Roblox
local Icons = useStudio and require(script.Parent.icons) or loadWithTimeout(RAYFIELD_RAW .. 'icons.lua')
-- Variables

local CFileName = nil
local CLegacyFileName = nil -- the place-only file name configs had before Build 1.753, read as a fallback
local CEnabled = false
local Minimised = false
local Hidden = false
local Debounce = false
local searchOpen = false
local Notifications = Rayfield.Notifications
local keybindConnections = {} -- For storing keybind connections to disconnect when Rayfield is destroyed

local SelectedTheme = RayfieldLibrary.Theme.Default

local function ChangeTheme(Theme)
	if typeof(Theme) == 'string' then
		SelectedTheme = RayfieldLibrary.Theme[Theme]
	elseif typeof(Theme) == 'table' then
		SelectedTheme = Theme
	end

	Rayfield.Main.BackgroundColor3 = SelectedTheme.Background
	Rayfield.Main.Topbar.BackgroundColor3 = SelectedTheme.Topbar
	Rayfield.Main.Topbar.CornerRepair.BackgroundColor3 = SelectedTheme.Topbar
	Rayfield.Main.Shadow.Image.ImageColor3 = SelectedTheme.Shadow

	Rayfield.Main.Topbar.ChangeSize.ImageColor3 = SelectedTheme.TextColor
	Rayfield.Main.Topbar.Hide.ImageColor3 = SelectedTheme.TextColor
	Rayfield.Main.Topbar.Search.ImageColor3 = SelectedTheme.TextColor
	if Topbar:FindFirstChild('Settings') then
		Rayfield.Main.Topbar.Settings.ImageColor3 = SelectedTheme.TextColor
		Rayfield.Main.Topbar.Divider.BackgroundColor3 = SelectedTheme.ElementStroke
	end

	Main.Search.BackgroundColor3 = SelectedTheme.TextColor
	Main.Search.Shadow.ImageColor3 = SelectedTheme.TextColor
	Main.Search.Search.ImageColor3 = SelectedTheme.TextColor
	Main.Search.Input.PlaceholderColor3 = SelectedTheme.TextColor
	Main.Search.UIStroke.Color = SelectedTheme.SecondaryElementStroke

	if Main:FindFirstChild('Notice') then
		Main.Notice.BackgroundColor3 = SelectedTheme.Background
	end

	for _, text in ipairs(Rayfield:GetDescendants()) do
		if text.Parent.Parent ~= Notifications then
			if text:IsA('TextLabel') or text:IsA('TextBox') then text.TextColor3 = SelectedTheme.TextColor end
		end
	end

	for _, TabPage in ipairs(Elements:GetChildren()) do
		for _, Element in ipairs(TabPage:GetChildren()) do
			if Element.ClassName == "Frame" and Element.Name ~= "Placeholder" and Element.Name ~= "SectionSpacing" and Element.Name ~= "Divider" and Element.Name ~= "SectionTitle" and Element.Name ~= "SearchTitle-fsefsefesfsefesfesfThanks" then
				Element.BackgroundColor3 = SelectedTheme.ElementBackground
				Element.UIStroke.Color = SelectedTheme.ElementStroke
			end
		end
	end
end

local function getIcon(name : string): {id: number, imageRectSize: Vector2, imageRectOffset: Vector2}
	if not Icons then
		warn("Lucide Icons: Cannot use icons as icons library is not loaded")
		return
	end
	name = string.match(string.lower(name), "^%s*(.*)%s*$") :: string
	local sizedicons = Icons['48px']
	local r = sizedicons[name]
	if not r then
		error("Lucide Icons: Failed to find icon by the name of \"" .. name .. "\"", 2)
	end

	local rirs = r[2]
	local riro = r[3]

	if type(r[1]) ~= "number" or type(rirs) ~= "table" or type(riro) ~= "table" then
		error("Lucide Icons: Internal error: Invalid auto-generated asset entry")
	end

	local irs = Vector2.new(rirs[1], rirs[2])
	local iro = Vector2.new(riro[1], riro[2])

	local asset = {
		id = r[1],
		imageRectSize = irs,
		imageRectOffset = iro,
	}

	return asset
end
local function getAssetUri(id: any): string
	local assetUri = ""
	if type(id) == "number" then
		assetUri = "rbxassetid://" .. id
	elseif type(id) == "string" and not Icons then
		warn("Rayfield | Cannot use Lucide icons as icons library is not loaded")
	else
		warn("Rayfield | The icon argument must either be an icon ID (number) or a Lucide icon name (string)")
	end
	return assetUri
end

local function isCustomAsset(value)
	return type(value) == "string" and (string.find(value, "rbxasset://") == 1 or string.find(value, "rbxthumb://") == 1)
end

local function resolveIcon(icon)
	if not icon or icon == 0 then
		return "", nil, nil
	end

	if isCustomAsset(icon) then
		return icon, nil, nil
	end

	if secureMode then
		secureNotify("icon_blocked", "Secure Mode", "Element icons using asset IDs or Lucide names are blocked. Use getcustomasset() for icons to stay undetected.")
		return "", nil, nil
	end

	if typeof(icon) == "string" and Icons then
		local asset = getIcon(icon)
		return "rbxassetid://" .. asset.id, asset.imageRectOffset, asset.imageRectSize
	else
		return getAssetUri(icon), nil, nil
	end
end

local function makeDraggable(object, dragObject, enableTaptic, tapticOffset)
	local dragging = false
	local relative = nil

	local offset = Vector2.zero
	local screenGui = object:FindFirstAncestorWhichIsA("ScreenGui")
	if screenGui and screenGui.IgnoreGuiInset then
		offset += getService('GuiService'):GetGuiInset()
	end

	local function connectFunctions()
		if dragBar and enableTaptic then
			dragBar.MouseEnter:Connect(function()
				if not dragging and not Hidden then
					TweenService:Create(dragBarCosmetic, TweenInfo.new(0.25, Enum.EasingStyle.Back, Enum.EasingDirection.Out), {BackgroundTransparency = 0.5, Size = UDim2.new(0, 120, 0, 4)}):Play()
				end
			end)

			dragBar.MouseLeave:Connect(function()
				if not dragging and not Hidden then
					TweenService:Create(dragBarCosmetic, TweenInfo.new(0.25, Enum.EasingStyle.Back, Enum.EasingDirection.Out), {BackgroundTransparency = 0.7, Size = UDim2.new(0, 100, 0, 4)}):Play()
				end
			end)
		end
	end

	connectFunctions()

	dragObject.InputBegan:Connect(function(input, processed)
		if processed then return end

		local inputType = input.UserInputType.Name
		if inputType == "MouseButton1" or inputType == "Touch" then
			dragging = true

			relative = object.AbsolutePosition + object.AbsoluteSize * object.AnchorPoint - UserInputService:GetMouseLocation()
			if enableTaptic and not Hidden then
				TweenService:Create(dragBarCosmetic, TweenInfo.new(0.35, Enum.EasingStyle.Back, Enum.EasingDirection.Out), {Size = UDim2.new(0, 110, 0, 4), BackgroundTransparency = 0}):Play()
			end
		end
	end)

	local inputEnded = UserInputService.InputEnded:Connect(function(input)
		if not dragging then return end

		local inputType = input.UserInputType.Name
		if inputType == "MouseButton1" or inputType == "Touch" then
			dragging = false

			if enableTaptic and not Hidden then
				TweenService:Create(dragBarCosmetic, TweenInfo.new(0.35, Enum.EasingStyle.Back, Enum.EasingDirection.Out), {Size = UDim2.new(0, 100, 0, 4), BackgroundTransparency = 0.7}):Play()
			end
		end
	end)

	local renderStepped = RunService.RenderStepped:Connect(function()
		if dragging and not Hidden then
			local position = UserInputService:GetMouseLocation() + relative + offset
			if enableTaptic and tapticOffset then
				TweenService:Create(object, TweenInfo.new(0.4, Enum.EasingStyle.Exponential, Enum.EasingDirection.Out), {Position = UDim2.fromOffset(position.X, position.Y)}):Play()
				TweenService:Create(dragObject.Parent, TweenInfo.new(0.05, Enum.EasingStyle.Exponential, Enum.EasingDirection.Out), {Position = UDim2.fromOffset(position.X, position.Y + ((useMobileSizing and tapticOffset[2]) or tapticOffset[1]))}):Play()
			else
				if dragBar and tapticOffset then
					dragBar.Position = UDim2.fromOffset(position.X, position.Y + ((useMobileSizing and tapticOffset[2]) or tapticOffset[1]))
				end
				object.Position = UDim2.fromOffset(position.X, position.Y)
			end
		end
	end)

	object.Destroying:Connect(function()
		if inputEnded then inputEnded:Disconnect() end
		if renderStepped then renderStepped:Disconnect() end
	end)
end


local function PackColor(Color)
	return {R = Color.R * 255, G = Color.G * 255, B = Color.B * 255}
end    

local function UnpackColor(Color)
	return Color3.fromRGB(Color.R, Color.G, Color.B)
end

local function LoadConfiguration(Configuration)
	local success, Data = pcall(function() return HttpService:JSONDecode(Configuration) end)
	local changed

	if not success then warn('Rayfield had an issue decoding the configuration file, please try delete the file and reopen Rayfield.') return end

	-- Iterate through current UI elements' flags
	for FlagName, Flag in pairs(RayfieldLibrary.Flags) do
		local FlagValue = Data[FlagName]

		if (typeof(FlagValue) == 'boolean' and FlagValue == false) or FlagValue then
			task.spawn(function()
				if Flag.Type == "ColorPicker" then
					changed = true
					Flag:Set(UnpackColor(FlagValue))
				else
					if (Flag.CurrentValue or Flag.CurrentKeybind or Flag.CurrentOption or Flag.Color) ~= FlagValue then 
						changed = true
						Flag:Set(FlagValue) 	
					end
				end
			end)
		else
			warn("Rayfield | Unable to find '"..FlagName.. "' in the save file.")
			print("The error above may not be an issue if new elements have been added or not been set values.")
			--RayfieldLibrary:Notify({Title = "Rayfield Flags", Content = "Rayfield was unable to find '"..FlagName.. "' in the save file. Check sirius.menu/discord for help.", Image = 3944688398})
		end
	end

	return changed
end

local function SaveConfiguration()
	if not CEnabled or not globalLoaded then return end

	if debugX then
		print('Saving')
	end

	local Data = {}
	for i, v in pairs(RayfieldLibrary.Flags) do
		if v.Type == "ColorPicker" then
			Data[i] = PackColor(v.Color)
		else
			if typeof(v.CurrentValue) == 'boolean' then
				if v.CurrentValue == false then
					Data[i] = false
				else
					Data[i] = v.CurrentValue or v.CurrentKeybind or v.CurrentOption or v.Color
				end
			else
				Data[i] = v.CurrentValue or v.CurrentKeybind or v.CurrentOption or v.Color
			end
		end
	end

	if useStudio then
		if script.Parent:FindFirstChild('configuration') then script.Parent.configuration:Destroy() end

		local ScreenGui = Instance.new("ScreenGui")
		ScreenGui.Parent = script.Parent
		ScreenGui.Name = 'configuration'

		local TextBox = Instance.new("TextBox")
		TextBox.Parent = ScreenGui
		TextBox.Size = UDim2.new(0, 800, 0, 50)
		TextBox.AnchorPoint = Vector2.new(0.5, 0)
		TextBox.Position = UDim2.new(0.5, 0, 0, 30)
		TextBox.Text = HttpService:JSONEncode(Data)
		TextBox.ClearTextOnFocus = false
	end

	if debugX then
		warn(HttpService:JSONEncode(Data))
	end


	callSafely(writefile, ConfigurationFolder .. "/" .. CFileName .. ConfigurationExtension, tostring(HttpService:JSONEncode(Data)))
end

function RayfieldLibrary:Notify(data) -- action e.g open messages
	-- a destroyed interface has no template left to clone
	if rayfieldDestroyed then return end
	task.spawn(function()

		-- Notification Object Creation
		local newNotification = Notifications.Template:Clone()
		newNotification.Name = data.Title or 'No Title Provided'
		newNotification.Parent = Notifications
		newNotification.LayoutOrder = #Notifications:GetChildren()
		newNotification.Visible = false

		-- Set Data
		newNotification.Title.Text = data.Title or "Unknown Title"
		newNotification.Description.Text = data.Content or "Unknown Content"

		if data.Image then
			local img, rectOffset, rectSize = resolveIcon(data.Image)
			newNotification.Icon.Image = img
			if rectOffset then newNotification.Icon.ImageRectOffset = rectOffset end
			if rectSize then newNotification.Icon.ImageRectSize = rectSize end
		else
			newNotification.Icon.Image = ""
		end

		-- Set initial transparency values

		newNotification.Title.TextColor3 = SelectedTheme.TextColor
		newNotification.Description.TextColor3 = SelectedTheme.TextColor
		newNotification.BackgroundColor3 = SelectedTheme.Background
		newNotification.UIStroke.Color = SelectedTheme.TextColor
		newNotification.Icon.ImageColor3 = SelectedTheme.TextColor

		newNotification.BackgroundTransparency = 1
		newNotification.Title.TextTransparency = 1
		newNotification.Description.TextTransparency = 1
		newNotification.UIStroke.Transparency = 1
		newNotification.Shadow.ImageTransparency = 1
		newNotification.Size = UDim2.new(1, 0, 0, 800)
		newNotification.Icon.ImageTransparency = 1
		newNotification.Icon.BackgroundTransparency = 1

		task.wait()

		newNotification.Visible = true

		if data.Actions then
			warn('Rayfield | Not seeing your actions in notifications?')
			print("Notification Actions are being sunset for now, keep up to date on when they're back in the discord. (sirius.menu/discord)")
		end

		-- Calculate textbounds and set initial values
		local bounds = {newNotification.Title.TextBounds.Y, newNotification.Description.TextBounds.Y}
		newNotification.Size = UDim2.new(1, -60, 0, -Notifications:FindFirstChild("UIListLayout").Padding.Offset)

		newNotification.Icon.Size = UDim2.new(0, 32, 0, 32)
		newNotification.Icon.Position = UDim2.new(0, 20, 0.5, 0)

		TweenService:Create(newNotification, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Size = UDim2.new(1, 0, 0, math.max(bounds[1] + bounds[2] + 31, 60))}):Play()

		task.wait(0.15)
		TweenService:Create(newNotification, TweenInfo.new(0.4, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0.45}):Play()
		TweenService:Create(newNotification.Title, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {TextTransparency = 0}):Play()

		task.wait(0.05)

		TweenService:Create(newNotification.Icon, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {ImageTransparency = 0}):Play()

		task.wait(0.05)
		TweenService:Create(newNotification.Description, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {TextTransparency = 0.35}):Play()
		TweenService:Create(newNotification.UIStroke, TweenInfo.new(0.4, Enum.EasingStyle.Exponential), {Transparency = 0.95}):Play()
		TweenService:Create(newNotification.Shadow, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {ImageTransparency = 0.82}):Play()

		local waitDuration = math.min(math.max((#newNotification.Description.Text * 0.1) + 2.5, 3), 10)
		task.wait(data.Duration or waitDuration)

		newNotification.Icon.Visible = false
		TweenService:Create(newNotification, TweenInfo.new(0.4, Enum.EasingStyle.Exponential), {BackgroundTransparency = 1}):Play()
		TweenService:Create(newNotification.UIStroke, TweenInfo.new(0.4, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
		TweenService:Create(newNotification.Shadow, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {ImageTransparency = 1}):Play()
		TweenService:Create(newNotification.Title, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {TextTransparency = 1}):Play()
		TweenService:Create(newNotification.Description, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {TextTransparency = 1}):Play()

		TweenService:Create(newNotification, TweenInfo.new(1, Enum.EasingStyle.Exponential), {Size = UDim2.new(1, -90, 0, 0)}):Play()

		task.wait(1)

		TweenService:Create(newNotification, TweenInfo.new(1, Enum.EasingStyle.Exponential), {Size = UDim2.new(1, -90, 0, -Notifications:FindFirstChild("UIListLayout").Padding.Offset)}):Play()

		newNotification.Visible = false
		newNotification:Destroy()
	end)
end

local function openSearch()
	searchOpen = true

	Main.Search.BackgroundTransparency = 1
	Main.Search.Shadow.ImageTransparency = 1
	Main.Search.Input.TextTransparency = 1
	Main.Search.Search.ImageTransparency = 1
	Main.Search.UIStroke.Transparency = 1
	Main.Search.Size = UDim2.new(1, 0, 0, 80)
	Main.Search.Position = UDim2.new(0.5, 0, 0, 70)

	Main.Search.Input.Interactable = true

	Main.Search.Visible = true

	for _, tabbtn in ipairs(TabList:GetChildren()) do
		if tabbtn.ClassName == "Frame" and tabbtn.Name ~= "Placeholder" then
			tabbtn.Interact.Visible = false
			TweenService:Create(tabbtn, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {BackgroundTransparency = 1}):Play()
			TweenService:Create(tabbtn.Title, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {TextTransparency = 1}):Play()
			TweenService:Create(tabbtn.Image, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {ImageTransparency = 1}):Play()
			TweenService:Create(tabbtn.UIStroke, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
		end
	end

	Main.Search.Input:CaptureFocus()
	TweenService:Create(Main.Search.Shadow, TweenInfo.new(0.05, Enum.EasingStyle.Quint), {ImageTransparency = 0.95}):Play()
	TweenService:Create(Main.Search, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {Position = UDim2.new(0.5, 0, 0, 57), BackgroundTransparency = 0.9}):Play()
	TweenService:Create(Main.Search.UIStroke, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {Transparency = 0.8}):Play()
	TweenService:Create(Main.Search.Input, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {TextTransparency = 0.2}):Play()
	TweenService:Create(Main.Search.Search, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {ImageTransparency = 0.5}):Play()
	TweenService:Create(Main.Search, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {Size = UDim2.new(1, -35, 0, 35)}):Play()
end

local function closeSearch()
	searchOpen = false

	TweenService:Create(Main.Search, TweenInfo.new(0.35, Enum.EasingStyle.Quint), {BackgroundTransparency = 1, Size = UDim2.new(1, -55, 0, 30)}):Play()
	TweenService:Create(Main.Search.Search, TweenInfo.new(0.15, Enum.EasingStyle.Quint), {ImageTransparency = 1}):Play()
	TweenService:Create(Main.Search.Shadow, TweenInfo.new(0.15, Enum.EasingStyle.Quint), {ImageTransparency = 1}):Play()
	TweenService:Create(Main.Search.UIStroke, TweenInfo.new(0.15, Enum.EasingStyle.Quint), {Transparency = 1}):Play()
	TweenService:Create(Main.Search.Input, TweenInfo.new(0.15, Enum.EasingStyle.Quint), {TextTransparency = 1}):Play()

	for _, tabbtn in ipairs(TabList:GetChildren()) do
		if tabbtn.ClassName == "Frame" and tabbtn.Name ~= "Placeholder" then
			tabbtn.Interact.Visible = true
			if tostring(Elements.UIPageLayout.CurrentPage) == tabbtn.Title.Text then
				TweenService:Create(tabbtn, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0}):Play()
				TweenService:Create(tabbtn.Image, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {ImageTransparency = 0}):Play()
				TweenService:Create(tabbtn.Title, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {TextTransparency = 0}):Play()
				TweenService:Create(tabbtn.UIStroke, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
			else
				TweenService:Create(tabbtn, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0.7}):Play()
				TweenService:Create(tabbtn.Image, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {ImageTransparency = 0.2}):Play()
				TweenService:Create(tabbtn.Title, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {TextTransparency = 0.2}):Play()
				TweenService:Create(tabbtn.UIStroke, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {Transparency = 0.5}):Play()
			end
		end
	end

	Main.Search.Input.Text = ''
	Main.Search.Input.Interactable = false
end

-- Sets element visibility across all tab pages (used by Hide, Unhide, Maximise, Minimise)
local function setElementsVisible(show)
	for _, tab in ipairs(Elements:GetChildren()) do
		if tab.Name ~= "Template" and tab.ClassName == "ScrollingFrame" and tab.Name ~= "Placeholder" then
			for _, element in ipairs(tab:GetChildren()) do
				if element.ClassName == "Frame" then
					if element.Name ~= "SectionSpacing" and element.Name ~= "Placeholder" then
						if element.Name == "SectionTitle" or element.Name == 'SearchTitle-fsefsefesfsefesfesfThanks' then
							TweenService:Create(element.Title, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {TextTransparency = show and 0.4 or 1}):Play()
						elseif element.Name == 'Divider' then
							TweenService:Create(element.Divider, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {BackgroundTransparency = show and 0.85 or 1}):Play()
						else
							local bgTarget = element:GetAttribute("BackgroundTransparencyTarget") or 0
							local strokeTarget = element:GetAttribute("UIStrokeTransparencyTarget") or 0
							local titleTarget = element:GetAttribute("TitleTextTransparencyTarget") or 0
							TweenService:Create(element, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {BackgroundTransparency = show and bgTarget or 1}):Play()
							TweenService:Create(element.UIStroke, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {Transparency = show and strokeTarget or 1}):Play()
							TweenService:Create(element.Title, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {TextTransparency = show and titleTarget or 1}):Play()
						end
						for _, child in ipairs(element:GetChildren()) do
							if child.ClassName == "Frame" or child.ClassName == "TextLabel" or child.ClassName == "TextBox" or child.ClassName == "ImageButton" or child.ClassName == "ImageLabel" then
								child.Visible = show
							end
						end
					end
				end
			end
		end
	end
end

-- Sets tab button visibility (used by Hide, Unhide, Maximise, Minimise)
local function setTabButtonsVisible(show)
	for _, tabbtn in ipairs(TabList:GetChildren()) do
		if tabbtn.ClassName == "Frame" and tabbtn.Name ~= "Placeholder" then
			if show then
				if tostring(Elements.UIPageLayout.CurrentPage) == tabbtn.Title.Text then
					TweenService:Create(tabbtn, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0}):Play()
					TweenService:Create(tabbtn.Image, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {ImageTransparency = 0}):Play()
					TweenService:Create(tabbtn.Title, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {TextTransparency = 0}):Play()
					TweenService:Create(tabbtn.UIStroke, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
				else
					TweenService:Create(tabbtn, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0.7}):Play()
					TweenService:Create(tabbtn.Image, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {ImageTransparency = 0.2}):Play()
					TweenService:Create(tabbtn.Title, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {TextTransparency = 0.2}):Play()
					TweenService:Create(tabbtn.UIStroke, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {Transparency = 0.5}):Play()
				end
			else
				TweenService:Create(tabbtn, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {BackgroundTransparency = 1}):Play()
				TweenService:Create(tabbtn.Title, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {TextTransparency = 1}):Play()
				TweenService:Create(tabbtn.Image, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {ImageTransparency = 1}):Play()
				TweenService:Create(tabbtn.UIStroke, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
			end
		end
	end
end

local function Hide(notify: boolean?)
	if MPrompt then
		MPrompt.Title.TextColor3 = Color3.fromRGB(255, 255, 255)
		MPrompt.Position = UDim2.new(0.5, 0, 0, -50)
		MPrompt.Size = UDim2.new(0, 40, 0, 10)
		MPrompt.BackgroundTransparency = 1
		MPrompt.Title.TextTransparency = 1
		MPrompt.Visible = true
	end

	task.spawn(closeSearch)

	Debounce = true
	if notify then
		if useMobilePrompt then 
			RayfieldLibrary:Notify({Title = "Interface Hidden", Content = "The interface has been hidden, you can unhide the interface by tapping 'Show'.", Duration = 7, Image = 4400697855})
		else
			RayfieldLibrary:Notify({Title = "Interface Hidden", Content = "The interface has been hidden, you can unhide the interface by tapping " .. tostring(getSetting("General", "rayfieldOpen")) .. ".", Duration = 7, Image = 4400697855})
		end
	end

	TweenService:Create(Main, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {Size = UDim2.new(0, 470, 0, 0)}):Play()
	TweenService:Create(Main.Topbar, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {Size = UDim2.new(0, 470, 0, 45)}):Play()
	TweenService:Create(Main, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {BackgroundTransparency = 1}):Play()
	TweenService:Create(Main.Topbar, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {BackgroundTransparency = 1}):Play()
	TweenService:Create(Main.Topbar.Divider, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {BackgroundTransparency = 1}):Play()
	TweenService:Create(Main.Topbar.CornerRepair, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {BackgroundTransparency = 1}):Play()
	TweenService:Create(Main.Topbar.Title, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {TextTransparency = 1}):Play()
	TweenService:Create(Main.Shadow.Image, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {ImageTransparency = 1}):Play()
	TweenService:Create(Topbar.UIStroke, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
	if dragBarCosmetic then
		TweenService:Create(dragBarCosmetic, TweenInfo.new(0.25, Enum.EasingStyle.Back, Enum.EasingDirection.Out), {BackgroundTransparency = 1}):Play()
	end

	if useMobilePrompt and MPrompt then
		TweenService:Create(MPrompt, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {Size = UDim2.new(0, 120, 0, 30), Position = UDim2.new(0.5, 0, 0, 20), BackgroundTransparency = 0.3}):Play()
		TweenService:Create(MPrompt.Title, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {TextTransparency = 0.3}):Play()
	end

	for _, TopbarButton in ipairs(Topbar:GetChildren()) do
		if TopbarButton.ClassName == "ImageButton" then
			TweenService:Create(TopbarButton, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {ImageTransparency = 1}):Play()
		end
	end

	setTabButtonsVisible(false)

	if dragInteract then dragInteract.Visible = false end

	setElementsVisible(false)

	task.wait(0.5)
	Main.Visible = false
	Debounce = false
end

local function Maximise()
	Debounce = true
	Topbar.ChangeSize.Image = customAssets[tostring(10137941941)]

	TweenService:Create(Topbar.UIStroke, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
	TweenService:Create(Main.Shadow.Image, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {ImageTransparency = 0.6}):Play()
	TweenService:Create(Topbar.CornerRepair, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0}):Play()
	TweenService:Create(Topbar.Divider, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0}):Play()
	TweenService:Create(dragBarCosmetic, TweenInfo.new(0.25, Enum.EasingStyle.Back, Enum.EasingDirection.Out), {BackgroundTransparency = 0.7}):Play()
	TweenService:Create(Main, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {Size = useMobileSizing and UDim2.new(0, 500, 0, 275) or UDim2.new(0, 500, 0, 475)}):Play()
	TweenService:Create(Topbar, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {Size = UDim2.new(0, 500, 0, 45)}):Play()
	TabList.Visible = true
	task.wait(0.2)

	Elements.Visible = true

	setElementsVisible(true)

	task.wait(0.1)

	setTabButtonsVisible(true)

	task.wait(0.5)
	Debounce = false
end


local function Unhide()
	Debounce = true
	Main.Position = UDim2.new(0.5, 0, 0.5, 0)
	Main.Visible = true
	TweenService:Create(Main, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {Size = useMobileSizing and UDim2.new(0, 500, 0, 275) or UDim2.new(0, 500, 0, 475)}):Play()
	TweenService:Create(Main.Topbar, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {Size = UDim2.new(0, 500, 0, 45)}):Play()
	TweenService:Create(Main.Shadow.Image, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {ImageTransparency = 0.6}):Play()
	TweenService:Create(Main, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0}):Play()
	TweenService:Create(Main.Topbar, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0}):Play()
	TweenService:Create(Main.Topbar.Divider, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0}):Play()
	TweenService:Create(Main.Topbar.CornerRepair, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0}):Play()
	TweenService:Create(Main.Topbar.Title, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {TextTransparency = 0}):Play()

	if MPrompt then
		TweenService:Create(MPrompt, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {Size = UDim2.new(0, 40, 0, 10), Position = UDim2.new(0.5, 0, 0, -50), BackgroundTransparency = 1}):Play()
		TweenService:Create(MPrompt.Title, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {TextTransparency = 1}):Play()

		task.spawn(function()
			task.wait(0.5)
			MPrompt.Visible = false
		end)
	end

	if Minimised then
		task.spawn(Maximise)
	end

	dragBar.Position = useMobileSizing and UDim2.new(0.5, 0, 0.5, dragOffsetMobile) or UDim2.new(0.5, 0, 0.5, dragOffset)

	dragInteract.Visible = true

	for _, TopbarButton in ipairs(Topbar:GetChildren()) do
		if TopbarButton.ClassName == "ImageButton" then
			if TopbarButton.Name == 'Icon' then
				TweenService:Create(TopbarButton, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {ImageTransparency = 0}):Play()
			else
				TweenService:Create(TopbarButton, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {ImageTransparency = 0.8}):Play()
			end

		end
	end

	setTabButtonsVisible(true)

	setElementsVisible(true)

	TweenService:Create(dragBarCosmetic, TweenInfo.new(0.25, Enum.EasingStyle.Back, Enum.EasingDirection.Out), {BackgroundTransparency = 0.5}):Play()

	task.wait(0.5)
	Minimised = false
	Debounce = false
end

local function Minimise()
	Debounce = true
	Topbar.ChangeSize.Image = customAssets[tostring(11036884234)]

	Topbar.UIStroke.Color = SelectedTheme.ElementStroke

	task.spawn(closeSearch)

	setTabButtonsVisible(false)

	setElementsVisible(false)

	TweenService:Create(dragBarCosmetic, TweenInfo.new(0.25, Enum.EasingStyle.Back, Enum.EasingDirection.Out), {BackgroundTransparency = 1}):Play()
	TweenService:Create(Topbar.UIStroke, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {Transparency = 0}):Play()
	TweenService:Create(Main.Shadow.Image, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {ImageTransparency = 1}):Play()
	TweenService:Create(Topbar.CornerRepair, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {BackgroundTransparency = 1}):Play()
	TweenService:Create(Topbar.Divider, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {BackgroundTransparency = 1}):Play()
	TweenService:Create(Main, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {Size = UDim2.new(0, 495, 0, 45)}):Play()
	TweenService:Create(Topbar, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {Size = UDim2.new(0, 495, 0, 45)}):Play()

	task.wait(0.3)

	Elements.Visible = false
	TabList.Visible = false

	task.wait(0.2)
	Debounce = false
end

local function saveSettings() -- Save settings to config file
	local encoded
	local success, err = pcall(function()
		encoded = HttpService:JSONEncode(settingsTable)
	end)

	if success then
		if useStudio then
			if script.Parent['get.val'] then
				script.Parent['get.val'].Value = encoded
			end
		end
		callSafely(writefile, RayfieldFolder..'/settings'..ConfigurationExtension, encoded)
	end
end

local function updateSetting(category: string, setting: string, value: any)
	if not settingsInitialized then
		return
	end
	settingsTable[category][setting].Value = value
	overriddenSettings[category .. "." .. setting] = nil -- If user changes an overriden setting, remove the override
	saveSettings()

	-- Turning analytics off mid-session also stops anything already armed, like the kick watcher.
	if category == "System" and setting == "usageAnalytics" and not value and reporter and reporter.disable then
		pcall(reporter.disable, reporter)
	end
end

local function createSettings(window)
	if not (writefile and isfile and readfile and isfolder and makefolder) and not useStudio then
		if Topbar['Settings'] then Topbar.Settings.Visible = false end
		Topbar['Search'].Position = UDim2.new(1, -75, 0.5, 0)
		warn('Can\'t create settings as no file-saving functionality is available.')
		return
	end

	local newTab = window:CreateTab('Rayfield Settings', 0, true)

	if TabList['Rayfield Settings'] then
		TabList['Rayfield Settings'].LayoutOrder = 1000
	end

	if Elements['Rayfield Settings'] then
		Elements['Rayfield Settings'].LayoutOrder = 1000
	end

	-- Create sections and elements
	for categoryName, settingCategory in pairs(settingsTable) do
		newTab:CreateSection(categoryName)

		for settingName, setting in pairs(settingCategory) do
			if setting.Type == 'input' then
				setting.Element = newTab:CreateInput({
					Name = setting.Name,
					CurrentValue = setting.Value,
					PlaceholderText = setting.Placeholder,
					Ext = true,
					RemoveTextAfterFocusLost = setting.ClearOnFocus,
					Callback = function(Value)
						updateSetting(categoryName, settingName, Value)
					end,
				})
			elseif setting.Type == 'toggle' then
				setting.Element = newTab:CreateToggle({
					Name = setting.Name,
					CurrentValue = setting.Value,
					Ext = true,
					Callback = function(Value)
						updateSetting(categoryName, settingName, Value)
					end,
				})
				if setting.Description then
					newTab:CreateLabel(setting.Description)
				end
			elseif setting.Type == 'bind' then
				setting.Element = newTab:CreateKeybind({
					Name = setting.Name,
					CurrentKeybind = setting.Value,
					HoldToInteract = false,
					Ext = true,
					CallOnChange = true,
					Callback = function(Value)
						updateSetting(categoryName, settingName, Value)
					end,
				})
			end
		end
	end

	settingsCreated = true
	loadSettings()
	saveSettings()
end

local function fadeOutKeyUI(KeyMain)
	TweenService:Create(KeyMain, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundTransparency = 1}):Play()
	TweenService:Create(KeyMain, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Size = UDim2.new(0, 467, 0, 175)}):Play()
	TweenService:Create(KeyMain.Shadow.Image, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {ImageTransparency = 1}):Play()
	TweenService:Create(KeyMain.Title, TweenInfo.new(0.4, Enum.EasingStyle.Exponential), {TextTransparency = 1}):Play()
	TweenService:Create(KeyMain.Subtitle, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {TextTransparency = 1}):Play()
	TweenService:Create(KeyMain.KeyNote, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {TextTransparency = 1}):Play()
	TweenService:Create(KeyMain.Input, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {BackgroundTransparency = 1}):Play()
	TweenService:Create(KeyMain.Input.UIStroke, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
	TweenService:Create(KeyMain.Input.InputBox, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {TextTransparency = 1}):Play()
	TweenService:Create(KeyMain.NoteTitle, TweenInfo.new(0.4, Enum.EasingStyle.Exponential), {TextTransparency = 1}):Play()
	TweenService:Create(KeyMain.NoteMessage, TweenInfo.new(0.4, Enum.EasingStyle.Exponential), {TextTransparency = 1}):Play()
	TweenService:Create(KeyMain.Hide, TweenInfo.new(0.4, Enum.EasingStyle.Exponential), {ImageTransparency = 1}):Play()
end

function RayfieldLibrary:CreateWindow(Settings)
	if Rayfield:FindFirstChild('Loading') then
		if getgenv and not getgenv().rayfieldCached then
			Rayfield.Enabled = true
			Rayfield.Loading.Visible = true

			task.wait(1.4)
			Rayfield.Loading.Visible = false
		end
	end

	if getgenv then getgenv().rayfieldCached = true end

	if not correctBuild and not Settings.DisableBuildWarnings then
		task.delay(3, 
			function() 
				RayfieldLibrary:Notify({Title = 'Build Mismatch', Content = 'Rayfield may encounter issues as you are running an incompatible interface version ('.. ((Rayfield:FindFirstChild('Build') and Rayfield.Build.Value) or 'No Build') ..').\n\nThis version of Rayfield is intended for interface build '..InterfaceBuild..'.\n\nTry rejoining and then run the script twice.', Image = 4335487866, Duration = 15})		
			end)
	end

	if Settings.ToggleUIKeybind then -- Can either be a string or an Enum.KeyCode
		local keybind = Settings.ToggleUIKeybind
		if type(keybind) == "string" then
			keybind = string.upper(keybind)
			assert(pcall(function()
				return Enum.KeyCode[keybind]
			end), "ToggleUIKeybind must be a valid KeyCode")
			overrideSetting("General", "rayfieldOpen", keybind)
		elseif typeof(keybind) == "EnumItem" then
			assert(keybind.EnumType == Enum.KeyCode, "ToggleUIKeybind must be a KeyCode enum")
			overrideSetting("General", "rayfieldOpen", keybind.Name)
		else
			error("ToggleUIKeybind must be a string or KeyCode enum")
		end
	end

	ensureFolder(RayfieldFolder)

	local Passthrough = false
	Topbar.Title.Text = Settings.Name

	Main.Size = UDim2.new(0, 420, 0, 100)
	Main.Visible = true
	Main.BackgroundTransparency = 1
	if Main:FindFirstChild('Notice') then Main.Notice.Visible = false end
	Main.Shadow.Image.ImageTransparency = 1

	LoadingFrame.Title.TextTransparency = 1
	LoadingFrame.Subtitle.TextTransparency = 1

	if Settings.ShowText then
		MPrompt.Title.Text = 'Show '..Settings.ShowText
	end

	LoadingFrame.Version.TextTransparency = 1
	LoadingFrame.Title.Text = Settings.LoadingTitle or "Rayfield"
	LoadingFrame.Subtitle.Text = Settings.LoadingSubtitle or "Interface Suite"

	if Settings.LoadingTitle ~= "Rayfield Interface Suite" then
		LoadingFrame.Version.Text = "Rayfield UI"
	end

	if Settings.Icon and Settings.Icon ~= 0 and Topbar:FindFirstChild('Icon') then
		Topbar.Icon.Visible = true
		Topbar.Title.Position = UDim2.new(0, 47, 0.5, 0)

		if Settings.Icon then
			local img, rectOffset, rectSize = resolveIcon(Settings.Icon)
			Topbar.Icon.Image = img
			if rectOffset then Topbar.Icon.ImageRectOffset = rectOffset end
			if rectSize then Topbar.Icon.ImageRectSize = rectSize end
		else
			Topbar.Icon.Image = ""
		end
	end

	if dragBar then
		dragBar.Visible = false
		dragBarCosmetic.BackgroundTransparency = 1
		dragBar.Visible = true
	end

	if Settings.Theme then
		local success, result = pcall(ChangeTheme, Settings.Theme)
		if not success then
			local success, result2 = pcall(ChangeTheme, 'Default')
			if not success then
				warn('CRITICAL ERROR - NO DEFAULT THEME')
				print(result2)
			end
			warn('issue rendering theme. no theme on file')
			print(result)
		end
	end

	Topbar.Visible = false
	Elements.Visible = false
	LoadingFrame.Visible = true

	if not Settings.DisableRayfieldPrompts then
		task.spawn(function()
			while not rayfieldDestroyed do
				task.wait(math.random(180, 600))
				if rayfieldDestroyed then break end
				RayfieldLibrary:Notify({
					Title = "Rayfield Interface",
					Content = "Enjoying this UI library? Find it at sirius.menu/discord",
					Duration = 7,
					Image = 4370033185,
				})
			end
		end)
	end

	pcall(function()
		-- Without a FileName the config used to be named after the place alone, so every hub in the
		-- same game wrote over the others'. It's now the hub's name and the place. That older file is
		-- still read when the new one doesn't exist yet, so nobody's saved settings go missing.
		CLegacyFileName = nil
		if not Settings.ConfigurationSaving.FileName then
			local placeName = tostring(game.PlaceId)
			-- window names often carry characters Windows refuses in a file name, like "|" or ":",
			-- and a trailing dot or space that it drops
			local hubName = string.gsub(sanitizeFileName(Settings.Name or ""), '[:<>"|?*]', "")
			hubName = string.match(hubName, "^%s*(.-)[%s%.]*$") or ""
			if hubName ~= "" then
				Settings.ConfigurationSaving.FileName = hubName .. "-" .. placeName
				CLegacyFileName = placeName
			else
				Settings.ConfigurationSaving.FileName = placeName
			end
		end

		if Settings.ConfigurationSaving.Enabled == nil then
			Settings.ConfigurationSaving.Enabled = false
		end

		CFileName = sanitizeFileName(Settings.ConfigurationSaving.FileName)
		if CFileName == "" then
			CFileName = tostring(game.PlaceId)
		end
		if Settings.ConfigurationSaving.FolderName then
			local folderName = sanitizeFolderName(Settings.ConfigurationSaving.FolderName)
			if folderName ~= "" then
				ConfigurationFolder = folderName
			end
		end
		CEnabled = Settings.ConfigurationSaving.Enabled

		if Settings.ConfigurationSaving.Enabled then
			ensureFolder(ConfigurationFolder)
		end
	end)


	makeDraggable(Main, Topbar, false, {dragOffset, dragOffsetMobile})
	if dragBar then dragBar.Position = useMobileSizing and UDim2.new(0.5, 0, 0.5, dragOffsetMobile) or UDim2.new(0.5, 0, 0.5, dragOffset) makeDraggable(Main, dragInteract, true, {dragOffset, dragOffsetMobile}) end

	for _, TabButton in ipairs(TabList:GetChildren()) do
		if TabButton.ClassName == "Frame" and TabButton.Name ~= "Placeholder" then
			TabButton.BackgroundTransparency = 1
			TabButton.Title.TextTransparency = 1
			TabButton.Image.ImageTransparency = 1
			TabButton.UIStroke.Transparency = 1
		end
	end

	if Settings.Discord and Settings.Discord.Enabled and not useStudio and not secureMode then
		ensureFolder(RayfieldFolder.."/Discord Invites")
		local inviteFile = RayfieldFolder.."/Discord Invites".."/"..sanitizeFileName(Settings.Discord.Invite)..ConfigurationExtension

		if not callSafely(isfile, inviteFile) then
			if requestFunc then
				pcall(function()
					requestFunc({
						Url = 'http://127.0.0.1:6463/rpc?v=1',
						Method = 'POST',
						Headers = {
							['Content-Type'] = 'application/json',
							Origin = 'https://discord.com'
						},
						Body = HttpService:JSONEncode({
							cmd = 'INVITE_BROWSER',
							nonce = HttpService:GenerateGUID(false),
							args = {code = Settings.Discord.Invite}
						})
					})
				end)
			end

			if Settings.Discord.RememberJoins then -- We do logic this way so if the developer changes this setting, the user still won't be prompted, only new users
				callSafely(writefile, inviteFile,"Rayfield RememberJoins is true for this invite, this invite will not ask you to join again")
			end
		end
	end

	if (Settings.KeySystem) then
		if not Settings.KeySettings then
			Passthrough = true
			return
		end

		ensureFolder(RayfieldFolder.."/Key System")

		if typeof(Settings.KeySettings.Key) == "string" then Settings.KeySettings.Key = {Settings.KeySettings.Key} end

		if Settings.KeySettings.GrabKeyFromSite then
			for i, Key in ipairs(Settings.KeySettings.Key) do
				local Success, Response = pcall(function()
					Settings.KeySettings.Key[i] = tostring(game:HttpGet(Key):gsub("[\n\r]", " "))
					Settings.KeySettings.Key[i] = string.gsub(Settings.KeySettings.Key[i], " ", "")
				end)
				if not Success then
					print("Rayfield | "..Key.." Error " ..tostring(Response))
					warn('Check docs.sirius.menu for help with Rayfield specific development.')
				end
			end
		end

		if not Settings.KeySettings.FileName then
			Settings.KeySettings.FileName = "No file name specified"
		end
		local keyFileName = sanitizeFileName(Settings.KeySettings.FileName)
		if keyFileName == "" then
			keyFileName = "No file name specified"
		end
		local keyFile = RayfieldFolder.."/Key System".."/"..keyFileName..ConfigurationExtension

		if callSafely(isfile, keyFile) then
			for _, MKey in ipairs(Settings.KeySettings.Key) do
				local savedKeys = callSafely(readfile, keyFile)
				if savedKeys and string.find(savedKeys, tostring(MKey), 1, true) then
					Passthrough = true
				end
			end
		end

		if not Passthrough and secureMode then
			warn("Rayfield | Secure Mode: Key system requires a valid saved key. The key UI cannot be shown as it requires loading detectable assets.")
			Rayfield.Enabled = false
			return RayfieldLibrary
		end

		if not Passthrough then
			local AttemptsRemaining = Settings.KeySettings.MaxAttempts or 5
			Rayfield.Enabled = false
			local KeyUI = useStudio and script.Parent:FindFirstChild('Key') or game:GetObjects("rbxassetid://11380036235")[1]

			KeyUI.Enabled = true

			if gethui then
				KeyUI.Parent = gethui()
			elseif syn and syn.protect_gui then 
				syn.protect_gui(KeyUI)
				KeyUI.Parent = CoreGui
			elseif not useStudio and CoreGui:FindFirstChild("RobloxGui") then
				KeyUI.Parent = CoreGui:FindFirstChild("RobloxGui")
			elseif not useStudio then
				KeyUI.Parent = CoreGui
			end

			if gethui then
				for _, Interface in ipairs(gethui():GetChildren()) do
					if Interface.Name == KeyUI.Name and Interface ~= KeyUI then
						Interface.Enabled = false
						Interface.Name = "KeyUI-Old"
					end
				end
			elseif not useStudio then
				for _, Interface in ipairs(CoreGui:GetChildren()) do
					if Interface.Name == KeyUI.Name and Interface ~= KeyUI then
						Interface.Enabled = false
						Interface.Name = "KeyUI-Old"
					end
				end
			end

			local KeyMain = KeyUI.Main
			KeyMain.Title.Text = Settings.KeySettings.Title or Settings.Name
			KeyMain.Subtitle.Text = Settings.KeySettings.Subtitle or "Key System"
			KeyMain.NoteMessage.Text = Settings.KeySettings.Note or "No instructions"

			KeyMain.Size = UDim2.new(0, 467, 0, 175)
			KeyMain.BackgroundTransparency = 1
			KeyMain.Shadow.Image.ImageTransparency = 1
			KeyMain.Title.TextTransparency = 1
			KeyMain.Subtitle.TextTransparency = 1
			KeyMain.KeyNote.TextTransparency = 1
			KeyMain.Input.BackgroundTransparency = 1
			KeyMain.Input.UIStroke.Transparency = 1
			KeyMain.Input.InputBox.TextTransparency = 1
			KeyMain.NoteTitle.TextTransparency = 1
			KeyMain.NoteMessage.TextTransparency = 1
			KeyMain.Hide.ImageTransparency = 1

			TweenService:Create(KeyMain, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0}):Play()
			TweenService:Create(KeyMain, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Size = UDim2.new(0, 500, 0, 187)}):Play()
			TweenService:Create(KeyMain.Shadow.Image, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {ImageTransparency = 0.5}):Play()
			task.wait(0.05)
			TweenService:Create(KeyMain.Title, TweenInfo.new(0.4, Enum.EasingStyle.Exponential), {TextTransparency = 0}):Play()
			TweenService:Create(KeyMain.Subtitle, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {TextTransparency = 0}):Play()
			task.wait(0.05)
			TweenService:Create(KeyMain.KeyNote, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {TextTransparency = 0}):Play()
			TweenService:Create(KeyMain.Input, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0}):Play()
			TweenService:Create(KeyMain.Input.UIStroke, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {Transparency = 0}):Play()
			TweenService:Create(KeyMain.Input.InputBox, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {TextTransparency = 0}):Play()
			task.wait(0.05)
			TweenService:Create(KeyMain.NoteTitle, TweenInfo.new(0.4, Enum.EasingStyle.Exponential), {TextTransparency = 0}):Play()
			TweenService:Create(KeyMain.NoteMessage, TweenInfo.new(0.4, Enum.EasingStyle.Exponential), {TextTransparency = 0}):Play()
			task.wait(0.15)
			TweenService:Create(KeyMain.Hide, TweenInfo.new(0.4, Enum.EasingStyle.Exponential), {ImageTransparency = 0.3}):Play()


			KeyUI.Main.Input.InputBox.FocusLost:Connect(function()
				if #KeyUI.Main.Input.InputBox.Text == 0 then return end
				local KeyFound = false
				local FoundKey = ''
				for _, MKey in ipairs(Settings.KeySettings.Key) do
					--if string.find(KeyMain.Input.InputBox.Text, MKey) then
					--	KeyFound = true
					--	FoundKey = MKey
					--end


					-- stricter key check
					if KeyMain.Input.InputBox.Text == MKey then
						KeyFound = true
						FoundKey = MKey
					end
				end
				if KeyFound then
					fadeOutKeyUI(KeyMain)
					task.wait(0.51)
					Passthrough = true
					KeyMain.Visible = false
					if Settings.KeySettings.SaveKey then
						callSafely(writefile, keyFile, FoundKey)
						RayfieldLibrary:Notify({Title = "Key System", Content = "The key for this script has been saved successfully.", Image = 3605522284})
					end
				else
					if AttemptsRemaining == 0 then
						fadeOutKeyUI(KeyMain)
						task.wait(0.45)
						Players.LocalPlayer:Kick("No Attempts Remaining")
						game:Shutdown()
					end
					KeyMain.Input.InputBox.Text = ""
					AttemptsRemaining = AttemptsRemaining - 1
					TweenService:Create(KeyMain, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Size = UDim2.new(0, 467, 0, 175)}):Play()
					TweenService:Create(KeyMain, TweenInfo.new(0.4, Enum.EasingStyle.Elastic), {Position = UDim2.new(0.495,0,0.5,0)}):Play()
					task.wait(0.1)
					TweenService:Create(KeyMain, TweenInfo.new(0.4, Enum.EasingStyle.Elastic), {Position = UDim2.new(0.505,0,0.5,0)}):Play()
					task.wait(0.1)
					TweenService:Create(KeyMain, TweenInfo.new(0.4, Enum.EasingStyle.Exponential), {Position = UDim2.new(0.5,0,0.5,0)}):Play()
					TweenService:Create(KeyMain, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Size = UDim2.new(0, 500, 0, 187)}):Play()
				end
			end)

			KeyMain.Hide.MouseButton1Click:Connect(function()
				fadeOutKeyUI(KeyMain)
				task.wait(0.51)
				Passthrough = true
				RayfieldLibrary:Destroy()
				KeyUI:Destroy()
			end)
		else
			Passthrough = true
		end
	end
	if Settings.KeySystem then
		repeat task.wait() until Passthrough
		if rayfieldDestroyed then return end
	end

	-- the developer's own Sentivel heartbeat, pinged for as long as this interface is up. Started
	-- only once the key system has let the player through, so a player sat at the key prompt isn't
	-- counted as running the script. A re-executed script renames this interface "Rayfield-Old"
	-- rather than destroying it, so that ends the loop too.
	if Settings.Heartbeat ~= nil then
		startHeartbeat(Settings.Heartbeat, function()
			return not rayfieldDestroyed and Rayfield.Parent ~= nil and Rayfield.Name ~= "Rayfield-Old"
		end)
	end

	Notifications.Template.Visible = false
	Notifications.Visible = true
	Rayfield.Enabled = true

	task.wait(0.5)
	TweenService:Create(Main, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0}):Play()
	TweenService:Create(Main.Shadow.Image, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {ImageTransparency = 0.6}):Play()
	task.wait(0.1)
	TweenService:Create(LoadingFrame.Title, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {TextTransparency = 0}):Play()
	task.wait(0.05)
	TweenService:Create(LoadingFrame.Subtitle, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {TextTransparency = 0}):Play()
	task.wait(0.05)
	TweenService:Create(LoadingFrame.Version, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {TextTransparency = 0}):Play()


	Elements.Template.LayoutOrder = 100000
	Elements.Template.Visible = false

	Elements.UIPageLayout.FillDirection = Enum.FillDirection.Horizontal
	Elements.UIPageLayout.ScrollWheelInputEnabled = false
	Elements.UIPageLayout.GamepadInputEnabled = false
	Elements.UIPageLayout.TouchInputEnabled = false
	TabList.Template.Visible = false

	-- Tab
	local FirstTab = false
	local Window = {}
	function Window:CreateTab(Name, Image, Ext)
		local SDone = false
		local TabButton = TabList.Template:Clone()
		TabButton.Name = Name
		TabButton.Title.Text = Name
		TabButton.Parent = TabList
		TabButton.Title.TextWrapped = false
		TabButton.Size = UDim2.new(0, TabButton.Title.TextBounds.X + 30, 0, 30)

		if Image and Image ~= 0 then
			local img, rectOffset, rectSize = resolveIcon(Image)
			TabButton.Image.Image = img
			if rectOffset then TabButton.Image.ImageRectOffset = rectOffset end
			if rectSize then TabButton.Image.ImageRectSize = rectSize end

			TabButton.Title.AnchorPoint = Vector2.new(0, 0.5)
			TabButton.Title.Position = UDim2.new(0, 37, 0.5, 0)
			TabButton.Image.Visible = true
			TabButton.Title.TextXAlignment = Enum.TextXAlignment.Left
			TabButton.Size = UDim2.new(0, TabButton.Title.TextBounds.X + 52, 0, 30)
		end



		TabButton.BackgroundTransparency = 1
		TabButton.Title.TextTransparency = 1
		TabButton.Image.ImageTransparency = 1
		TabButton.UIStroke.Transparency = 1

		TabButton.Visible = not Ext or false

		-- Create Elements Page
		local TabPage = Elements.Template:Clone()
		TabPage.Name = Name
		TabPage.Visible = true

		TabPage.LayoutOrder = Ext and 10000 or #Elements:GetChildren()

		for _, TemplateElement in ipairs(TabPage:GetChildren()) do
			if TemplateElement.ClassName == "Frame" and TemplateElement.Name ~= "Placeholder" then
				TemplateElement:Destroy()
			end
		end

		TabPage.Parent = Elements
		if not FirstTab and not Ext then
			Elements.UIPageLayout.Animated = false
			Elements.UIPageLayout:JumpTo(TabPage)
			Elements.UIPageLayout.Animated = true
		end

		TabButton.UIStroke.Color = SelectedTheme.TabStroke

		if Elements.UIPageLayout.CurrentPage == TabPage then
			TabButton.BackgroundColor3 = SelectedTheme.TabBackgroundSelected
			TabButton.Image.ImageColor3 = SelectedTheme.SelectedTabTextColor
			TabButton.Title.TextColor3 = SelectedTheme.SelectedTabTextColor
		else
			TabButton.BackgroundColor3 = SelectedTheme.TabBackground
			TabButton.Image.ImageColor3 = SelectedTheme.TabTextColor
			TabButton.Title.TextColor3 = SelectedTheme.TabTextColor
		end


		-- Animate
		task.wait(0.1)
		if FirstTab or Ext then
			TabButton.BackgroundColor3 = SelectedTheme.TabBackground
			TabButton.Image.ImageColor3 = SelectedTheme.TabTextColor
			TabButton.Title.TextColor3 = SelectedTheme.TabTextColor
			TweenService:Create(TabButton, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0.7}):Play()
			TweenService:Create(TabButton.Title, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {TextTransparency = 0.2}):Play()
			TweenService:Create(TabButton.Image, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {ImageTransparency = 0.2}):Play()
			TweenService:Create(TabButton.UIStroke, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {Transparency = 0.5}):Play()
		elseif not Ext then
			FirstTab = Name
			TabButton.BackgroundColor3 = SelectedTheme.TabBackgroundSelected
			TabButton.Image.ImageColor3 = SelectedTheme.SelectedTabTextColor
			TabButton.Title.TextColor3 = SelectedTheme.SelectedTabTextColor
			TweenService:Create(TabButton.Image, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {ImageTransparency = 0}):Play()
			TweenService:Create(TabButton, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0}):Play()
			TweenService:Create(TabButton.Title, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {TextTransparency = 0}):Play()
		end


		TabButton.Interact.MouseButton1Click:Connect(function()
			if Minimised then return end
			TweenService:Create(TabButton, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0}):Play()
			TweenService:Create(TabButton.UIStroke, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
			TweenService:Create(TabButton.Title, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {TextTransparency = 0}):Play()
			TweenService:Create(TabButton.Image, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {ImageTransparency = 0}):Play()
			TweenService:Create(TabButton, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.TabBackgroundSelected}):Play()
			TweenService:Create(TabButton.Title, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {TextColor3 = SelectedTheme.SelectedTabTextColor}):Play()
			TweenService:Create(TabButton.Image, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {ImageColor3 = SelectedTheme.SelectedTabTextColor}):Play()

			for _, OtherTabButton in ipairs(TabList:GetChildren()) do
				if OtherTabButton.Name ~= "Template" and OtherTabButton.ClassName == "Frame" and OtherTabButton ~= TabButton and OtherTabButton.Name ~= "Placeholder" then
					TweenService:Create(OtherTabButton, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.TabBackground}):Play()
					TweenService:Create(OtherTabButton.Title, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {TextColor3 = SelectedTheme.TabTextColor}):Play()
					TweenService:Create(OtherTabButton.Image, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {ImageColor3 = SelectedTheme.TabTextColor}):Play()
					TweenService:Create(OtherTabButton, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0.7}):Play()
					TweenService:Create(OtherTabButton.Title, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {TextTransparency = 0.2}):Play()
					TweenService:Create(OtherTabButton.Image, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {ImageTransparency = 0.2}):Play()
					TweenService:Create(OtherTabButton.UIStroke, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {Transparency = 0.5}):Play()
				end
			end

			if Elements.UIPageLayout.CurrentPage ~= TabPage then
				Elements.UIPageLayout:JumpTo(TabPage)
			end
		end)

		local Tab = {}

		-- Button
		function Tab:CreateButton(ButtonSettings)
			local ButtonValue = {}

			local Button = Elements.Template.Button:Clone()
			Button.Name = ButtonSettings.Name
			Button.Title.Text = ButtonSettings.Name
			Button.Visible = true
			Button.Parent = TabPage

			Button.BackgroundTransparency = 1
			Button.UIStroke.Transparency = 1
			Button.Title.TextTransparency = 1

			TweenService:Create(Button, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0}):Play()
			TweenService:Create(Button.UIStroke, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {Transparency = 0}):Play()
			TweenService:Create(Button.Title, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {TextTransparency = 0}):Play()	


			Button.Interact.MouseButton1Click:Connect(function()
				local Success, Response = pcall(ButtonSettings.Callback)
				-- Prevents animation from trying to play if the button's callback called RayfieldLibrary:Destroy()
				if rayfieldDestroyed then
					return
				end
				if not Success then
					TweenService:Create(Button, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = Color3.fromRGB(85, 0, 0)}):Play()
					TweenService:Create(Button.ElementIndicator, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {TextTransparency = 1}):Play()
					TweenService:Create(Button.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
					Button.Title.Text = "Callback Error"
					print("Rayfield | "..ButtonSettings.Name.." Callback Error " ..tostring(Response))
					warn('Check docs.sirius.menu for help with Rayfield specific development.')
					task.wait(0.5)
					Button.Title.Text = ButtonSettings.Name
					TweenService:Create(Button, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackground}):Play()
					TweenService:Create(Button.ElementIndicator, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {TextTransparency = 0.9}):Play()
					TweenService:Create(Button.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 0}):Play()
				else
					if not ButtonSettings.Ext then
						SaveConfiguration(ButtonSettings.Name..'\n')
					end
					TweenService:Create(Button, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackgroundHover}):Play()
					TweenService:Create(Button.ElementIndicator, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {TextTransparency = 1}):Play()
					TweenService:Create(Button.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
					task.wait(0.2)
					TweenService:Create(Button, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackground}):Play()
					TweenService:Create(Button.ElementIndicator, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {TextTransparency = 0.9}):Play()
					TweenService:Create(Button.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 0}):Play()
				end
			end)

			Button.MouseEnter:Connect(function()
				TweenService:Create(Button, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackgroundHover}):Play()
				TweenService:Create(Button.ElementIndicator, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {TextTransparency = 0.7}):Play()
			end)

			Button.MouseLeave:Connect(function()
				TweenService:Create(Button, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackground}):Play()
				TweenService:Create(Button.ElementIndicator, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {TextTransparency = 0.9}):Play()
			end)

			function ButtonValue:Set(NewButton)
				Button.Title.Text = NewButton
				Button.Name = NewButton
			end

			return ButtonValue
		end

		-- ColorPicker
		function Tab:CreateColorPicker(ColorPickerSettings) -- by Throit
			ColorPickerSettings.Type = "ColorPicker"
			local ColorPicker = Elements.Template.ColorPicker:Clone()
			local Background = ColorPicker.CPBackground
			local Display = Background.Display
			local Main = Background.MainCP
			local Slider = ColorPicker.ColorSlider
			ColorPicker.ClipsDescendants = true
			ColorPicker.Name = ColorPickerSettings.Name
			ColorPicker.Title.Text = ColorPickerSettings.Name
			ColorPicker.Visible = true
			ColorPicker.Parent = TabPage
			ColorPicker.Size = UDim2.new(1, -10, 0, 45)
			Background.Size = UDim2.new(0, 39, 0, 22)
			Display.BackgroundTransparency = 0
			Main.MainPoint.ImageTransparency = 1
			ColorPicker.Interact.Size = UDim2.new(1, 0, 1, 0)
			ColorPicker.Interact.Position = UDim2.new(0.5, 0, 0.5, 0)
			ColorPicker.RGB.Position = UDim2.new(0, 17, 0, 70)
			ColorPicker.HexInput.Position = UDim2.new(0, 17, 0, 90)
			Main.ImageTransparency = 1
			Background.BackgroundTransparency = 1

			for _, rgbinput in ipairs(ColorPicker.RGB:GetChildren()) do
				if rgbinput:IsA("Frame") then
					rgbinput.BackgroundColor3 = SelectedTheme.InputBackground
					rgbinput.UIStroke.Color = SelectedTheme.InputStroke
				end
			end

			ColorPicker.HexInput.BackgroundColor3 = SelectedTheme.InputBackground
			ColorPicker.HexInput.UIStroke.Color = SelectedTheme.InputStroke

			local opened = false 
			local mouse = Players.LocalPlayer:GetMouse()
			local mainDragging = false 
			local sliderDragging = false 
			ColorPicker.Interact.MouseButton1Down:Connect(function()
				task.spawn(function()
					TweenService:Create(ColorPicker, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackgroundHover}):Play()
					TweenService:Create(ColorPicker.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
					task.wait(0.2)
					TweenService:Create(ColorPicker, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackground}):Play()
					TweenService:Create(ColorPicker.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 0}):Play()
				end)

				if not opened then
					opened = true 
					TweenService:Create(Background, TweenInfo.new(0.45, Enum.EasingStyle.Exponential), {Size = UDim2.new(0, 18, 0, 15)}):Play()
					task.wait(0.1)
					TweenService:Create(ColorPicker, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Size = UDim2.new(1, -10, 0, 120)}):Play()
					TweenService:Create(Background, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Size = UDim2.new(0, 173, 0, 86)}):Play()
					TweenService:Create(Display, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundTransparency = 1}):Play()
					TweenService:Create(ColorPicker.Interact, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Position = UDim2.new(0.289, 0, 0.5, 0)}):Play()
					TweenService:Create(ColorPicker.RGB, TweenInfo.new(0.8, Enum.EasingStyle.Exponential), {Position = UDim2.new(0, 17, 0, 40)}):Play()
					TweenService:Create(ColorPicker.HexInput, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {Position = UDim2.new(0, 17, 0, 73)}):Play()
					TweenService:Create(ColorPicker.Interact, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Size = UDim2.new(0.574, 0, 1, 0)}):Play()
					TweenService:Create(Main.MainPoint, TweenInfo.new(0.2, Enum.EasingStyle.Exponential), {ImageTransparency = 0}):Play()
					TweenService:Create(Main, TweenInfo.new(0.2, Enum.EasingStyle.Exponential), {ImageTransparency = SelectedTheme ~= RayfieldLibrary.Theme.Default and 0.25 or 0.1}):Play()
					TweenService:Create(Background, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0}):Play()
				else
					opened = false
					TweenService:Create(ColorPicker, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Size = UDim2.new(1, -10, 0, 45)}):Play()
					TweenService:Create(Background, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Size = UDim2.new(0, 39, 0, 22)}):Play()
					TweenService:Create(ColorPicker.Interact, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Size = UDim2.new(1, 0, 1, 0)}):Play()
					TweenService:Create(ColorPicker.Interact, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Position = UDim2.new(0.5, 0, 0.5, 0)}):Play()
					TweenService:Create(ColorPicker.RGB, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Position = UDim2.new(0, 17, 0, 70)}):Play()
					TweenService:Create(ColorPicker.HexInput, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {Position = UDim2.new(0, 17, 0, 90)}):Play()
					TweenService:Create(Display, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0}):Play()
					TweenService:Create(Main.MainPoint, TweenInfo.new(0.2, Enum.EasingStyle.Exponential), {ImageTransparency = 1}):Play()
					TweenService:Create(Main, TweenInfo.new(0.2, Enum.EasingStyle.Exponential), {ImageTransparency = 1}):Play()
					TweenService:Create(Background, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundTransparency = 1}):Play()
				end

			end)

			local colorPickerInputConnection = UserInputService.InputEnded:Connect(function(input, gameProcessed) if input.UserInputType == Enum.UserInputType.MouseButton1 or input.UserInputType == Enum.UserInputType.Touch then
					mainDragging = false
					sliderDragging = false
				end end)
			Main.MouseButton1Down:Connect(function()
				if opened then
					mainDragging = true 
				end
			end)
			Main.MainPoint.MouseButton1Down:Connect(function()
				if opened then
					mainDragging = true 
				end
			end)
			Slider.MouseButton1Down:Connect(function()
				sliderDragging = true 
			end)
			Slider.SliderPoint.MouseButton1Down:Connect(function()
				sliderDragging = true 
			end)
			local h,s,v = ColorPickerSettings.Color:ToHSV()
			local color = Color3.fromHSV(h,s,v) 
			local hex = string.format("#%02X%02X%02X",color.R*0xFF,color.G*0xFF,color.B*0xFF)
			ColorPicker.HexInput.InputBox.Text = hex
			local function setDisplay()
				--Main
				Main.MainPoint.Position = UDim2.new(s,-Main.MainPoint.AbsoluteSize.X/2,1-v,-Main.MainPoint.AbsoluteSize.Y/2)
				Main.MainPoint.ImageColor3 = Color3.fromHSV(h,s,v)
				Background.BackgroundColor3 = Color3.fromHSV(h,1,1)
				Display.BackgroundColor3 = Color3.fromHSV(h,s,v)
				--Slider 
				local x = h * Slider.AbsoluteSize.X
				Slider.SliderPoint.Position = UDim2.new(0,x-Slider.SliderPoint.AbsoluteSize.X/2,0.5,0)
				Slider.SliderPoint.ImageColor3 = Color3.fromHSV(h,1,1)
				local color = Color3.fromHSV(h,s,v) 
				local r,g,b = math.floor((color.R*255)+0.5),math.floor((color.G*255)+0.5),math.floor((color.B*255)+0.5)
				ColorPicker.RGB.RInput.InputBox.Text = tostring(r)
				ColorPicker.RGB.GInput.InputBox.Text = tostring(g)
				ColorPicker.RGB.BInput.InputBox.Text = tostring(b)
				hex = string.format("#%02X%02X%02X",color.R*0xFF,color.G*0xFF,color.B*0xFF)
				ColorPicker.HexInput.InputBox.Text = hex
			end
			setDisplay()
			ColorPicker.HexInput.InputBox.FocusLost:Connect(function()
				if not pcall(function()
						local r, g, b = string.match(ColorPicker.HexInput.InputBox.Text, "^#?(%w%w)(%w%w)(%w%w)$")
						local rgbColor = Color3.fromRGB(tonumber(r, 16),tonumber(g, 16), tonumber(b, 16))
						h,s,v = rgbColor:ToHSV()
						hex = ColorPicker.HexInput.InputBox.Text
						setDisplay()
						ColorPickerSettings.Color = rgbColor
					end) 
				then 
					ColorPicker.HexInput.InputBox.Text = hex 
				end
				pcall(function()ColorPickerSettings.Callback(Color3.fromHSV(h,s,v))end)
				local r,g,b = math.floor((h*255)+0.5),math.floor((s*255)+0.5),math.floor((v*255)+0.5)
				ColorPickerSettings.Color = Color3.fromRGB(r,g,b)
				if not ColorPickerSettings.Ext then
					SaveConfiguration()
				end
			end)
			--RGB
			local function rgbBoxes(box,toChange)
				local value = tonumber(box.Text) 
				local color = Color3.fromHSV(h,s,v) 
				local oldR,oldG,oldB = math.floor((color.R*255)+0.5),math.floor((color.G*255)+0.5),math.floor((color.B*255)+0.5)
				local save 
				if toChange == "R" then save = oldR;oldR = value elseif toChange == "G" then save = oldG;oldG = value else save = oldB;oldB = value end
				if value then 
					value = math.clamp(value,0,255)
					h,s,v = Color3.fromRGB(oldR,oldG,oldB):ToHSV()

					setDisplay()
				else 
					box.Text = tostring(save)
				end
				local r,g,b = math.floor((h*255)+0.5),math.floor((s*255)+0.5),math.floor((v*255)+0.5)
				ColorPickerSettings.Color = Color3.fromRGB(r,g,b)
				if not ColorPickerSettings.Ext then
					SaveConfiguration(ColorPickerSettings.Flag..'\n'..tostring(ColorPickerSettings.Color))
				end
			end
			ColorPicker.RGB.RInput.InputBox.FocusLost:connect(function()
				rgbBoxes(ColorPicker.RGB.RInput.InputBox,"R")
				pcall(function()ColorPickerSettings.Callback(Color3.fromHSV(h,s,v))end)
			end)
			ColorPicker.RGB.GInput.InputBox.FocusLost:connect(function()
				rgbBoxes(ColorPicker.RGB.GInput.InputBox,"G")
				pcall(function()ColorPickerSettings.Callback(Color3.fromHSV(h,s,v))end)
			end)
			ColorPicker.RGB.BInput.InputBox.FocusLost:connect(function()
				rgbBoxes(ColorPicker.RGB.BInput.InputBox,"B")
				pcall(function()ColorPickerSettings.Callback(Color3.fromHSV(h,s,v))end)
			end)

			local colorPickerRenderConnection = RunService.RenderStepped:connect(function()
				if mainDragging then
					local localX = math.clamp(mouse.X-Main.AbsolutePosition.X,0,Main.AbsoluteSize.X)
					local localY = math.clamp(mouse.Y-Main.AbsolutePosition.Y,0,Main.AbsoluteSize.Y)
					Main.MainPoint.Position = UDim2.new(0,localX-Main.MainPoint.AbsoluteSize.X/2,0,localY-Main.MainPoint.AbsoluteSize.Y/2)
					s = localX / Main.AbsoluteSize.X
					v = 1 - (localY / Main.AbsoluteSize.Y)
					Display.BackgroundColor3 = Color3.fromHSV(h,s,v)
					Main.MainPoint.ImageColor3 = Color3.fromHSV(h,s,v)
					Background.BackgroundColor3 = Color3.fromHSV(h,1,1)
					local color = Color3.fromHSV(h,s,v) 
					local r,g,b = math.floor((color.R*255)+0.5),math.floor((color.G*255)+0.5),math.floor((color.B*255)+0.5)
					ColorPicker.RGB.RInput.InputBox.Text = tostring(r)
					ColorPicker.RGB.GInput.InputBox.Text = tostring(g)
					ColorPicker.RGB.BInput.InputBox.Text = tostring(b)
					ColorPicker.HexInput.InputBox.Text = string.format("#%02X%02X%02X",color.R*0xFF,color.G*0xFF,color.B*0xFF)
					pcall(function()ColorPickerSettings.Callback(Color3.fromHSV(h,s,v))end)
					ColorPickerSettings.Color = Color3.fromRGB(r,g,b)
					if not ColorPickerSettings.Ext then
						SaveConfiguration()
					end
				end
				if sliderDragging then 
					local localX = math.clamp(mouse.X-Slider.AbsolutePosition.X,0,Slider.AbsoluteSize.X)
					h = localX / Slider.AbsoluteSize.X
					Display.BackgroundColor3 = Color3.fromHSV(h,s,v)
					Slider.SliderPoint.Position = UDim2.new(0,localX-Slider.SliderPoint.AbsoluteSize.X/2,0.5,0)
					Slider.SliderPoint.ImageColor3 = Color3.fromHSV(h,1,1)
					Background.BackgroundColor3 = Color3.fromHSV(h,1,1)
					Main.MainPoint.ImageColor3 = Color3.fromHSV(h,s,v)
					local color = Color3.fromHSV(h,s,v) 
					local r,g,b = math.floor((color.R*255)+0.5),math.floor((color.G*255)+0.5),math.floor((color.B*255)+0.5)
					ColorPicker.RGB.RInput.InputBox.Text = tostring(r)
					ColorPicker.RGB.GInput.InputBox.Text = tostring(g)
					ColorPicker.RGB.BInput.InputBox.Text = tostring(b)
					ColorPicker.HexInput.InputBox.Text = string.format("#%02X%02X%02X",color.R*0xFF,color.G*0xFF,color.B*0xFF)
					pcall(function()ColorPickerSettings.Callback(Color3.fromHSV(h,s,v))end)
					ColorPickerSettings.Color = Color3.fromRGB(r,g,b)
					if not ColorPickerSettings.Ext then
						SaveConfiguration()
					end
				end
			end)

			ColorPicker.Destroying:Connect(function()
				if colorPickerRenderConnection then
					colorPickerRenderConnection:Disconnect()
				end
				if colorPickerInputConnection then
					colorPickerInputConnection:Disconnect()
				end
			end)

			if Settings.ConfigurationSaving then
				if Settings.ConfigurationSaving.Enabled and ColorPickerSettings.Flag then
					RayfieldLibrary.Flags[ColorPickerSettings.Flag] = ColorPickerSettings
				end
			end

			function ColorPickerSettings:Set(RGBColor)
				ColorPickerSettings.Color = RGBColor
				h,s,v = ColorPickerSettings.Color:ToHSV()
				color = Color3.fromHSV(h,s,v)
				setDisplay()
			end

			ColorPicker.MouseEnter:Connect(function()
				TweenService:Create(ColorPicker, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackgroundHover}):Play()
			end)

			ColorPicker.MouseLeave:Connect(function()
				TweenService:Create(ColorPicker, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackground}):Play()
			end)

			Rayfield.Main:GetPropertyChangedSignal('BackgroundColor3'):Connect(function()
				for _, rgbinput in ipairs(ColorPicker.RGB:GetChildren()) do
					if rgbinput:IsA("Frame") then
						rgbinput.BackgroundColor3 = SelectedTheme.InputBackground
						rgbinput.UIStroke.Color = SelectedTheme.InputStroke
					end
				end

				ColorPicker.HexInput.BackgroundColor3 = SelectedTheme.InputBackground
				ColorPicker.HexInput.UIStroke.Color = SelectedTheme.InputStroke
			end)

			return ColorPickerSettings
		end

		-- Section
		function Tab:CreateSection(SectionName)

			local SectionValue = {}

			if SDone then
				local SectionSpace = Elements.Template.SectionSpacing:Clone()
				SectionSpace.Visible = true
				SectionSpace.Parent = TabPage
			end

			local Section = Elements.Template.SectionTitle:Clone()
			Section.Title.Text = SectionName
			Section.Visible = true
			Section.Parent = TabPage

			Section.Title.TextTransparency = 1
			TweenService:Create(Section.Title, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {TextTransparency = 0.4}):Play()

			function SectionValue:Set(NewSection)
				Section.Title.Text = NewSection
			end

			SDone = true

			return SectionValue
		end

		-- Divider
		function Tab:CreateDivider()
			local DividerValue = {}

			local Divider = Elements.Template.Divider:Clone()
			Divider.Visible = true
			Divider.Parent = TabPage

			Divider.Divider.BackgroundTransparency = 1
			TweenService:Create(Divider.Divider, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0.85}):Play()

			function DividerValue:Set(Value)
				Divider.Visible = Value
			end

			return DividerValue
		end

		-- Label
		function Tab:CreateLabel(LabelText : string, Icon: number, Color : Color3, IgnoreTheme : boolean)
			local LabelValue = {}

			local Label = Elements.Template.Label:Clone()
			Label.Title.Text = LabelText
			Label.Visible = true
			Label.Parent = TabPage

			Label.BackgroundColor3 = Color or SelectedTheme.SecondaryElementBackground
			Label.UIStroke.Color = Color or SelectedTheme.SecondaryElementStroke

			if Icon then
				local img, rectOffset, rectSize = resolveIcon(Icon)
				Label.Icon.Image = img
				if rectOffset then Label.Icon.ImageRectOffset = rectOffset end
				if rectSize then Label.Icon.ImageRectSize = rectSize end
			else
				Label.Icon.Image = ""
			end

			if Icon and Label:FindFirstChild('Icon') then
				Label.Title.Position = UDim2.new(0, 45, 0.5, 0)
				Label.Title.Size = UDim2.new(1, -100, 0, 14)
				Label.Icon.Visible = true
			end

			Label.Icon.ImageTransparency = 1
			Label.BackgroundTransparency = 1
			Label.UIStroke.Transparency = 1
			Label.Title.TextTransparency = 1

			Label:SetAttribute("BackgroundTransparencyTarget", Color and 0.8 or 0)
			Label:SetAttribute("UIStrokeTransparencyTarget", Color and 0.7 or 0)
			Label:SetAttribute("TitleTextTransparencyTarget", Color and 0.2 or 0)

			TweenService:Create(Label, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {BackgroundTransparency = Color and 0.8 or 0}):Play()
			TweenService:Create(Label.UIStroke, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {Transparency = Color and 0.7 or 0}):Play()
			TweenService:Create(Label.Icon, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {ImageTransparency = 0.2}):Play()
			TweenService:Create(Label.Title, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {TextTransparency = Color and 0.2 or 0}):Play()

			function LabelValue:Set(NewLabel, Icon, Color)
				Label.Title.Text = NewLabel

				if Color then
					Label.BackgroundColor3 = Color or SelectedTheme.SecondaryElementBackground
					Label.UIStroke.Color = Color or SelectedTheme.SecondaryElementStroke
				end

				if Icon and Label:FindFirstChild('Icon') then
					Label.Title.Position = UDim2.new(0, 45, 0.5, 0)
					Label.Title.Size = UDim2.new(1, -100, 0, 14)

					local img, rectOffset, rectSize = resolveIcon(Icon)
					Label.Icon.Image = img
					if rectOffset then Label.Icon.ImageRectOffset = rectOffset end
					if rectSize then Label.Icon.ImageRectSize = rectSize end

					Label.Icon.Visible = true
				end
			end

			Rayfield.Main:GetPropertyChangedSignal('BackgroundColor3'):Connect(function()
				Label.BackgroundColor3 = IgnoreTheme and (Color or Label.BackgroundColor3) or SelectedTheme.SecondaryElementBackground
				Label.UIStroke.Color = IgnoreTheme and (Color or Label.BackgroundColor3) or SelectedTheme.SecondaryElementStroke
			end)

			return LabelValue
		end

		-- Paragraph
		function Tab:CreateParagraph(ParagraphSettings)
			local ParagraphValue = {}

			local Paragraph = Elements.Template.Paragraph:Clone()
			Paragraph.Title.Text = ParagraphSettings.Title
			Paragraph.Content.Text = ParagraphSettings.Content
			Paragraph.Visible = true
			Paragraph.Parent = TabPage

			Paragraph.BackgroundTransparency = 1
			Paragraph.UIStroke.Transparency = 1
			Paragraph.Title.TextTransparency = 1
			Paragraph.Content.TextTransparency = 1

			Paragraph.BackgroundColor3 = SelectedTheme.SecondaryElementBackground
			Paragraph.UIStroke.Color = SelectedTheme.SecondaryElementStroke

			TweenService:Create(Paragraph, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0}):Play()
			TweenService:Create(Paragraph.UIStroke, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {Transparency = 0}):Play()
			TweenService:Create(Paragraph.Title, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {TextTransparency = 0}):Play()	
			TweenService:Create(Paragraph.Content, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {TextTransparency = 0}):Play()	

			function ParagraphValue:Set(NewParagraphSettings)
				Paragraph.Title.Text = NewParagraphSettings.Title
				Paragraph.Content.Text = NewParagraphSettings.Content
			end

			Rayfield.Main:GetPropertyChangedSignal('BackgroundColor3'):Connect(function()
				Paragraph.BackgroundColor3 = SelectedTheme.SecondaryElementBackground
				Paragraph.UIStroke.Color = SelectedTheme.SecondaryElementStroke
			end)

			return ParagraphValue
		end

		-- Input
		function Tab:CreateInput(InputSettings)
			local Input = Elements.Template.Input:Clone()
			Input.Name = InputSettings.Name
			Input.Title.Text = InputSettings.Name
			Input.Visible = true
			Input.Parent = TabPage

			Input.BackgroundTransparency = 1
			Input.UIStroke.Transparency = 1
			Input.Title.TextTransparency = 1

			Input.InputFrame.InputBox.Text = InputSettings.CurrentValue or ''

			Input.InputFrame.BackgroundColor3 = SelectedTheme.InputBackground
			Input.InputFrame.UIStroke.Color = SelectedTheme.InputStroke

			TweenService:Create(Input, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0}):Play()
			TweenService:Create(Input.UIStroke, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {Transparency = 0}):Play()
			TweenService:Create(Input.Title, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {TextTransparency = 0}):Play()	

			Input.InputFrame.InputBox.PlaceholderText = InputSettings.PlaceholderText
			Input.InputFrame.Size = UDim2.new(0, Input.InputFrame.InputBox.TextBounds.X + 24, 0, 30)

			Input.InputFrame.InputBox.FocusLost:Connect(function()
				local Success, Response = pcall(function()
					InputSettings.Callback(Input.InputFrame.InputBox.Text)
					InputSettings.CurrentValue = Input.InputFrame.InputBox.Text
				end)

				if not Success then
					TweenService:Create(Input, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = Color3.fromRGB(85, 0, 0)}):Play()
					TweenService:Create(Input.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
					Input.Title.Text = "Callback Error"
					print("Rayfield | "..InputSettings.Name.." Callback Error " ..tostring(Response))
					warn('Check docs.sirius.menu for help with Rayfield specific development.')
					task.wait(0.5)
					Input.Title.Text = InputSettings.Name
					TweenService:Create(Input, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackground}):Play()
					TweenService:Create(Input.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 0}):Play()
				end

				if InputSettings.RemoveTextAfterFocusLost then
					Input.InputFrame.InputBox.Text = ""
				end

				if not InputSettings.Ext then
					SaveConfiguration()
				end
			end)

			Input.MouseEnter:Connect(function()
				TweenService:Create(Input, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackgroundHover}):Play()
			end)

			Input.MouseLeave:Connect(function()
				TweenService:Create(Input, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackground}):Play()
			end)

			Input.InputFrame.InputBox:GetPropertyChangedSignal("Text"):Connect(function()
				TweenService:Create(Input.InputFrame, TweenInfo.new(0.55, Enum.EasingStyle.Exponential, Enum.EasingDirection.Out), {Size = UDim2.new(0, Input.InputFrame.InputBox.TextBounds.X + 24, 0, 30)}):Play()
			end)

			function InputSettings:Set(text)
				Input.InputFrame.InputBox.Text = text
				InputSettings.CurrentValue = text

				local Success, Response = pcall(function()
					InputSettings.Callback(text)
				end)

				if not InputSettings.Ext then
					SaveConfiguration()
				end
			end

			if Settings.ConfigurationSaving then
				if Settings.ConfigurationSaving.Enabled and InputSettings.Flag then
					RayfieldLibrary.Flags[InputSettings.Flag] = InputSettings
				end
			end

			Rayfield.Main:GetPropertyChangedSignal('BackgroundColor3'):Connect(function()
				Input.InputFrame.BackgroundColor3 = SelectedTheme.InputBackground
				Input.InputFrame.UIStroke.Color = SelectedTheme.InputStroke
			end)

			return InputSettings
		end

		-- Dropdown
		function Tab:CreateDropdown(DropdownSettings)
			local Dropdown = Elements.Template.Dropdown:Clone()
			if string.find(DropdownSettings.Name,"closed") then
				Dropdown.Name = "Dropdown"
			else
				Dropdown.Name = DropdownSettings.Name
			end
			Dropdown.Title.Text = DropdownSettings.Name
			Dropdown.Visible = true
			Dropdown.Parent = TabPage

			Dropdown.List.Visible = false
			if DropdownSettings.CurrentOption then
				if type(DropdownSettings.CurrentOption) == "string" then
					DropdownSettings.CurrentOption = {DropdownSettings.CurrentOption}
				end
				if not DropdownSettings.MultipleOptions and type(DropdownSettings.CurrentOption) == "table" then
					DropdownSettings.CurrentOption = {DropdownSettings.CurrentOption[1]}
				end
			else
				DropdownSettings.CurrentOption = {}
			end

			if DropdownSettings.MultipleOptions then
				if DropdownSettings.CurrentOption and type(DropdownSettings.CurrentOption) == "table" then
					if #DropdownSettings.CurrentOption == 1 then
						Dropdown.Selected.Text = DropdownSettings.CurrentOption[1]
					elseif #DropdownSettings.CurrentOption == 0 then
						Dropdown.Selected.Text = "None"
					else
						Dropdown.Selected.Text = "Various"
					end
				else
					DropdownSettings.CurrentOption = {}
					Dropdown.Selected.Text = "None"
				end
			else
				Dropdown.Selected.Text = DropdownSettings.CurrentOption[1] or "None"
			end

			Dropdown.Toggle.ImageColor3 = SelectedTheme.TextColor
			TweenService:Create(Dropdown, TweenInfo.new(0.4, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackground}):Play()

			Dropdown.BackgroundTransparency = 1
			Dropdown.UIStroke.Transparency = 1
			Dropdown.Title.TextTransparency = 1

			Dropdown.Size = UDim2.new(1, -10, 0, 45)

			TweenService:Create(Dropdown, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0}):Play()
			TweenService:Create(Dropdown.UIStroke, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {Transparency = 0}):Play()
			TweenService:Create(Dropdown.Title, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {TextTransparency = 0}):Play()	

			for _, ununusedoption in ipairs(Dropdown.List:GetChildren()) do
				if ununusedoption.ClassName == "Frame" and ununusedoption.Name ~= "Placeholder" then
					ununusedoption:Destroy()
				end
			end

			Dropdown.Toggle.Rotation = 180

			Dropdown.Interact.MouseButton1Click:Connect(function()
				TweenService:Create(Dropdown, TweenInfo.new(0.4, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackgroundHover}):Play()
				TweenService:Create(Dropdown.UIStroke, TweenInfo.new(0.4, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
				task.wait(0.1)
				TweenService:Create(Dropdown, TweenInfo.new(0.4, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackground}):Play()
				TweenService:Create(Dropdown.UIStroke, TweenInfo.new(0.4, Enum.EasingStyle.Exponential), {Transparency = 0}):Play()
				if Debounce then return end
				if Dropdown.List.Visible then
					Debounce = true
					TweenService:Create(Dropdown, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {Size = UDim2.new(1, -10, 0, 45)}):Play()
					for _, DropdownOpt in ipairs(Dropdown.List:GetChildren()) do
						if DropdownOpt.ClassName == "Frame" and DropdownOpt.Name ~= "Placeholder" then
							TweenService:Create(DropdownOpt, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {BackgroundTransparency = 1}):Play()
							TweenService:Create(DropdownOpt.UIStroke, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
							TweenService:Create(DropdownOpt.Title, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {TextTransparency = 1}):Play()
						end
					end
					TweenService:Create(Dropdown.List, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {ScrollBarImageTransparency = 1}):Play()
					TweenService:Create(Dropdown.Toggle, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {Rotation = 180}):Play()	
					task.wait(0.35)
					Dropdown.List.Visible = false
					Debounce = false
				else
					TweenService:Create(Dropdown, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {Size = UDim2.new(1, -10, 0, 180)}):Play()
					Dropdown.List.Visible = true
					TweenService:Create(Dropdown.List, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {ScrollBarImageTransparency = 0.7}):Play()
					TweenService:Create(Dropdown.Toggle, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {Rotation = 0}):Play()	
					for _, DropdownOpt in ipairs(Dropdown.List:GetChildren()) do
						if DropdownOpt.ClassName == "Frame" and DropdownOpt.Name ~= "Placeholder" then
							if DropdownOpt.Name ~= Dropdown.Selected.Text then
								TweenService:Create(DropdownOpt.UIStroke, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {Transparency = 0}):Play()
							end
							TweenService:Create(DropdownOpt, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0}):Play()
							TweenService:Create(DropdownOpt.Title, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {TextTransparency = 0}):Play()
						end
					end
				end
			end)

			Dropdown.MouseEnter:Connect(function()
				if not Dropdown.List.Visible then
					TweenService:Create(Dropdown, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackgroundHover}):Play()
				end
			end)

			Dropdown.MouseLeave:Connect(function()
				TweenService:Create(Dropdown, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackground}):Play()
			end)

			local function SetDropdownOptions()
				for _, Option in ipairs(DropdownSettings.Options) do
					local DropdownOption = Elements.Template.Dropdown.List.Template:Clone()
					DropdownOption.Name = Option
					DropdownOption.Title.Text = Option
					DropdownOption.Parent = Dropdown.List
					DropdownOption.Visible = true

					DropdownOption.BackgroundTransparency = 1
					DropdownOption.UIStroke.Transparency = 1
					DropdownOption.Title.TextTransparency = 1

					--local Dropdown = Tab:CreateDropdown({
					--	Name = "Dropdown Example",
					--	Options = {"Option 1","Option 2"},
					--	CurrentOption = {"Option 1"},
					--  MultipleOptions = true,
					--	Flag = "Dropdown1",
					--	Callback = function(TableOfOptions)

					--	end,
					--})


					DropdownOption.Interact.ZIndex = 50
					DropdownOption.Interact.MouseButton1Click:Connect(function()
						if not DropdownSettings.MultipleOptions and table.find(DropdownSettings.CurrentOption, Option) then 
							return
						end

						if table.find(DropdownSettings.CurrentOption, Option) then
							table.remove(DropdownSettings.CurrentOption, table.find(DropdownSettings.CurrentOption, Option))
							if DropdownSettings.MultipleOptions then
								if #DropdownSettings.CurrentOption == 1 then
									Dropdown.Selected.Text = DropdownSettings.CurrentOption[1]
								elseif #DropdownSettings.CurrentOption == 0 then
									Dropdown.Selected.Text = "None"
								else
									Dropdown.Selected.Text = "Various"
								end
							else
								Dropdown.Selected.Text = DropdownSettings.CurrentOption[1]
							end
						else
							if not DropdownSettings.MultipleOptions then
								table.clear(DropdownSettings.CurrentOption)
							end
							table.insert(DropdownSettings.CurrentOption, Option)
							if DropdownSettings.MultipleOptions then
								if #DropdownSettings.CurrentOption == 1 then
									Dropdown.Selected.Text = DropdownSettings.CurrentOption[1]
								elseif #DropdownSettings.CurrentOption == 0 then
									Dropdown.Selected.Text = "None"
								else
									Dropdown.Selected.Text = "Various"
								end
							else
								Dropdown.Selected.Text = DropdownSettings.CurrentOption[1]
							end
							TweenService:Create(DropdownOption.UIStroke, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
							TweenService:Create(DropdownOption, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.DropdownSelected}):Play()
							Debounce = true
						end


						local Success, Response = pcall(function()
							DropdownSettings.Callback(DropdownSettings.CurrentOption)
						end)

						if not Success then
							TweenService:Create(Dropdown, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = Color3.fromRGB(85, 0, 0)}):Play()
							TweenService:Create(Dropdown.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
							Dropdown.Title.Text = "Callback Error"
							print("Rayfield | "..DropdownSettings.Name.." Callback Error " ..tostring(Response))
							warn('Check docs.sirius.menu for help with Rayfield specific development.')
							task.wait(0.5)
							Dropdown.Title.Text = DropdownSettings.Name
							TweenService:Create(Dropdown, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackground}):Play()
							TweenService:Create(Dropdown.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 0}):Play()
						end

						for _, droption in ipairs(Dropdown.List:GetChildren()) do
							if droption.ClassName == "Frame" and droption.Name ~= "Placeholder" and not table.find(DropdownSettings.CurrentOption, droption.Name) then
								TweenService:Create(droption, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.DropdownUnselected}):Play()
							end
						end
						if not DropdownSettings.MultipleOptions then
							task.wait(0.1)
							TweenService:Create(Dropdown, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {Size = UDim2.new(1, -10, 0, 45)}):Play()
							for _, DropdownOpt in ipairs(Dropdown.List:GetChildren()) do
								if DropdownOpt.ClassName == "Frame" and DropdownOpt.Name ~= "Placeholder" then
									TweenService:Create(DropdownOpt, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {BackgroundTransparency = 1}):Play()
									TweenService:Create(DropdownOpt.UIStroke, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
									TweenService:Create(DropdownOpt.Title, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {TextTransparency = 1}):Play()
								end
							end
							TweenService:Create(Dropdown.List, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {ScrollBarImageTransparency = 1}):Play()
							TweenService:Create(Dropdown.Toggle, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {Rotation = 180}):Play()	
							task.wait(0.35)
							Dropdown.List.Visible = false
						end
						Debounce = false
						if not DropdownSettings.Ext then
							SaveConfiguration()
						end
					end)

					Rayfield.Main:GetPropertyChangedSignal('BackgroundColor3'):Connect(function()
						DropdownOption.UIStroke.Color = SelectedTheme.ElementStroke
					end)
				end
			end
			SetDropdownOptions()

			for _, droption in ipairs(Dropdown.List:GetChildren()) do
				if droption.ClassName == "Frame" and droption.Name ~= "Placeholder" then
					if not table.find(DropdownSettings.CurrentOption, droption.Name) then
						droption.BackgroundColor3 = SelectedTheme.DropdownUnselected
					else
						droption.BackgroundColor3 = SelectedTheme.DropdownSelected
					end

					Rayfield.Main:GetPropertyChangedSignal('BackgroundColor3'):Connect(function()
						if not table.find(DropdownSettings.CurrentOption, droption.Name) then
							droption.BackgroundColor3 = SelectedTheme.DropdownUnselected
						else
							droption.BackgroundColor3 = SelectedTheme.DropdownSelected
						end
					end)
				end
			end

			function DropdownSettings:Set(NewOption)
				DropdownSettings.CurrentOption = NewOption

				if typeof(DropdownSettings.CurrentOption) == "string" then
					DropdownSettings.CurrentOption = {DropdownSettings.CurrentOption}
				end

				if not DropdownSettings.MultipleOptions then
					DropdownSettings.CurrentOption = {DropdownSettings.CurrentOption[1]}
				end

				if DropdownSettings.MultipleOptions then
					if #DropdownSettings.CurrentOption == 1 then
						Dropdown.Selected.Text = DropdownSettings.CurrentOption[1]
					elseif #DropdownSettings.CurrentOption == 0 then
						Dropdown.Selected.Text = "None"
					else
						Dropdown.Selected.Text = "Various"
					end
				else
					Dropdown.Selected.Text = DropdownSettings.CurrentOption[1]
				end


				local Success, Response = pcall(function()
					DropdownSettings.Callback(NewOption)
				end)
				if not Success then
					TweenService:Create(Dropdown, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = Color3.fromRGB(85, 0, 0)}):Play()
					TweenService:Create(Dropdown.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
					Dropdown.Title.Text = "Callback Error"
					print("Rayfield | "..DropdownSettings.Name.." Callback Error " ..tostring(Response))
					warn('Check docs.sirius.menu for help with Rayfield specific development.')
					task.wait(0.5)
					Dropdown.Title.Text = DropdownSettings.Name
					TweenService:Create(Dropdown, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackground}):Play()
					TweenService:Create(Dropdown.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 0}):Play()
				end

				for _, droption in ipairs(Dropdown.List:GetChildren()) do
					if droption.ClassName == "Frame" and droption.Name ~= "Placeholder" then
						if not table.find(DropdownSettings.CurrentOption, droption.Name) then
							droption.BackgroundColor3 = SelectedTheme.DropdownUnselected
						else
							droption.BackgroundColor3 = SelectedTheme.DropdownSelected
						end
					end
				end
				--SaveConfiguration()
			end

			function DropdownSettings:Refresh(optionsTable: table) -- updates a dropdown with new options from optionsTable
				DropdownSettings.Options = optionsTable
				for _, option in Dropdown.List:GetChildren() do
					if option.ClassName == "Frame" and option.Name ~= "Placeholder" then
						option:Destroy()
					end
				end
				SetDropdownOptions()

				-- Apply selected/unselected background colors to new options
				for _, droption in ipairs(Dropdown.List:GetChildren()) do
					if droption.ClassName == "Frame" and droption.Name ~= "Placeholder" then
						if not table.find(DropdownSettings.CurrentOption, droption.Name) then
							droption.BackgroundColor3 = SelectedTheme.DropdownUnselected
						else
							droption.BackgroundColor3 = SelectedTheme.DropdownSelected
						end
					end
				end

				-- If the dropdown is currently open, make new options visible immediately
				if Dropdown.List.Visible then
					for _, DropdownOpt in ipairs(Dropdown.List:GetChildren()) do
						if DropdownOpt.ClassName == "Frame" and DropdownOpt.Name ~= "Placeholder" then
							DropdownOpt.BackgroundTransparency = 0
							DropdownOpt.Title.TextTransparency = 0
							if not table.find(DropdownSettings.CurrentOption, DropdownOpt.Name) then
								DropdownOpt.UIStroke.Transparency = 0
							end
						end
					end
				end
			end

			if Settings.ConfigurationSaving then
				if Settings.ConfigurationSaving.Enabled and DropdownSettings.Flag then
					RayfieldLibrary.Flags[DropdownSettings.Flag] = DropdownSettings
				end
			end

			Rayfield.Main:GetPropertyChangedSignal('BackgroundColor3'):Connect(function()
				Dropdown.Toggle.ImageColor3 = SelectedTheme.TextColor
				TweenService:Create(Dropdown, TweenInfo.new(0.4, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackground}):Play()
			end)

			return DropdownSettings
		end

		-- Keybind
		function Tab:CreateKeybind(KeybindSettings)
			local CheckingForKey = false
			local Keybind = Elements.Template.Keybind:Clone()
			Keybind.Name = KeybindSettings.Name
			Keybind.Title.Text = KeybindSettings.Name
			Keybind.Visible = true
			Keybind.Parent = TabPage

			Keybind.BackgroundTransparency = 1
			Keybind.UIStroke.Transparency = 1
			Keybind.Title.TextTransparency = 1

			Keybind.KeybindFrame.BackgroundColor3 = SelectedTheme.InputBackground
			Keybind.KeybindFrame.UIStroke.Color = SelectedTheme.InputStroke

			TweenService:Create(Keybind, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0}):Play()
			TweenService:Create(Keybind.UIStroke, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {Transparency = 0}):Play()
			TweenService:Create(Keybind.Title, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {TextTransparency = 0}):Play()	

			Keybind.KeybindFrame.KeybindBox.Text = KeybindSettings.CurrentKeybind
			Keybind.KeybindFrame.Size = UDim2.new(0, Keybind.KeybindFrame.KeybindBox.TextBounds.X + 24, 0, 30)

			Keybind.KeybindFrame.KeybindBox.Focused:Connect(function()
				CheckingForKey = true
				Keybind.KeybindFrame.KeybindBox.Text = ""
			end)
			Keybind.KeybindFrame.KeybindBox.FocusLost:Connect(function()
				CheckingForKey = false
				if Keybind.KeybindFrame.KeybindBox.Text == nil or Keybind.KeybindFrame.KeybindBox.Text == "" then
					Keybind.KeybindFrame.KeybindBox.Text = KeybindSettings.CurrentKeybind
					if not KeybindSettings.Ext then
						SaveConfiguration()
					end
				end
			end)

			Keybind.MouseEnter:Connect(function()
				TweenService:Create(Keybind, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackgroundHover}):Play()
			end)

			Keybind.MouseLeave:Connect(function()
				TweenService:Create(Keybind, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackground}):Play()
			end)

			local connection = UserInputService.InputBegan:Connect(function(input, processed)
				if rayfieldDestroyed then return end
				if CheckingForKey then
					if input.KeyCode ~= Enum.KeyCode.Unknown then
						local SplitMessage = string.split(tostring(input.KeyCode), ".")
						local NewKeyNoEnum = SplitMessage[3]
						Keybind.KeybindFrame.KeybindBox.Text = tostring(NewKeyNoEnum)
						KeybindSettings.CurrentKeybind = tostring(NewKeyNoEnum)
						Keybind.KeybindFrame.KeybindBox:ReleaseFocus()
						if not KeybindSettings.Ext then
							SaveConfiguration()
						end

						if KeybindSettings.CallOnChange then
							KeybindSettings.Callback(tostring(NewKeyNoEnum))
						end
					end
				elseif not KeybindSettings.CallOnChange and KeybindSettings.CurrentKeybind ~= nil and (input.KeyCode == Enum.KeyCode[KeybindSettings.CurrentKeybind] and not processed) then -- Test
					local Held = true
					local Connection
					Connection = input.Changed:Connect(function(prop)
						if prop == "UserInputState" then
							Connection:Disconnect()
							Held = false
						end
					end)

					if not KeybindSettings.HoldToInteract then
						local Success, Response = pcall(KeybindSettings.Callback)
						if not Success then
							TweenService:Create(Keybind, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = Color3.fromRGB(85, 0, 0)}):Play()
							TweenService:Create(Keybind.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
							Keybind.Title.Text = "Callback Error"
							print("Rayfield | "..KeybindSettings.Name.." Callback Error " ..tostring(Response))
							warn('Check docs.sirius.menu for help with Rayfield specific development.')
							task.wait(0.5)
							Keybind.Title.Text = KeybindSettings.Name
							TweenService:Create(Keybind, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackground}):Play()
							TweenService:Create(Keybind.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 0}):Play()
						end
					else
						task.wait(0.25)
						if Held then
							local Loop; Loop = RunService.Stepped:Connect(function()
								if not Held then
									KeybindSettings.Callback(false) -- maybe pcall this
									Loop:Disconnect()
								else
									KeybindSettings.Callback(true) -- maybe pcall this
								end
							end)
						end
					end
				end
			end)
			table.insert(keybindConnections, connection)

			Keybind.KeybindFrame.KeybindBox:GetPropertyChangedSignal("Text"):Connect(function()
				TweenService:Create(Keybind.KeybindFrame, TweenInfo.new(0.55, Enum.EasingStyle.Exponential, Enum.EasingDirection.Out), {Size = UDim2.new(0, Keybind.KeybindFrame.KeybindBox.TextBounds.X + 24, 0, 30)}):Play()
			end)

			function KeybindSettings:Set(NewKeybind)
				Keybind.KeybindFrame.KeybindBox.Text = tostring(NewKeybind)
				KeybindSettings.CurrentKeybind = tostring(NewKeybind)
				Keybind.KeybindFrame.KeybindBox:ReleaseFocus()
				if not KeybindSettings.Ext then
					SaveConfiguration()
				end

				if KeybindSettings.CallOnChange then
					KeybindSettings.Callback(tostring(NewKeybind))
				end
			end

			if Settings.ConfigurationSaving then
				if Settings.ConfigurationSaving.Enabled and KeybindSettings.Flag then
					RayfieldLibrary.Flags[KeybindSettings.Flag] = KeybindSettings
				end
			end

			Rayfield.Main:GetPropertyChangedSignal('BackgroundColor3'):Connect(function()
				Keybind.KeybindFrame.BackgroundColor3 = SelectedTheme.InputBackground
				Keybind.KeybindFrame.UIStroke.Color = SelectedTheme.InputStroke
			end)

			return KeybindSettings
		end

		-- Toggle
		function Tab:CreateToggle(ToggleSettings)
			local ToggleValue = {}

			local Toggle = Elements.Template.Toggle:Clone()
			Toggle.Name = ToggleSettings.Name
			Toggle.Title.Text = ToggleSettings.Name
			Toggle.Visible = true
			Toggle.Parent = TabPage

			Toggle.BackgroundTransparency = 1
			Toggle.UIStroke.Transparency = 1
			Toggle.Title.TextTransparency = 1
			Toggle.Switch.BackgroundColor3 = SelectedTheme.ToggleBackground

			if SelectedTheme ~= RayfieldLibrary.Theme.Default then
				Toggle.Switch.Shadow.Visible = false
			end

			TweenService:Create(Toggle, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0}):Play()
			TweenService:Create(Toggle.UIStroke, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {Transparency = 0}):Play()
			TweenService:Create(Toggle.Title, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {TextTransparency = 0}):Play()	

			if ToggleSettings.CurrentValue == true then
				Toggle.Switch.Indicator.Position = UDim2.new(1, -20, 0.5, 0)
				Toggle.Switch.Indicator.UIStroke.Color = SelectedTheme.ToggleEnabledStroke
				Toggle.Switch.Indicator.BackgroundColor3 = SelectedTheme.ToggleEnabled
				Toggle.Switch.UIStroke.Color = SelectedTheme.ToggleEnabledOuterStroke
			else
				Toggle.Switch.Indicator.Position = UDim2.new(1, -40, 0.5, 0)
				Toggle.Switch.Indicator.UIStroke.Color = SelectedTheme.ToggleDisabledStroke
				Toggle.Switch.Indicator.BackgroundColor3 = SelectedTheme.ToggleDisabled
				Toggle.Switch.UIStroke.Color = SelectedTheme.ToggleDisabledOuterStroke
			end

			Toggle.MouseEnter:Connect(function()
				TweenService:Create(Toggle, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackgroundHover}):Play()
			end)

			Toggle.MouseLeave:Connect(function()
				TweenService:Create(Toggle, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackground}):Play()
			end)

			Toggle.Interact.MouseButton1Click:Connect(function()
				if ToggleSettings.CurrentValue == true then
					ToggleSettings.CurrentValue = false
					TweenService:Create(Toggle, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackgroundHover}):Play()
					TweenService:Create(Toggle.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
					TweenService:Create(Toggle.Switch.Indicator, TweenInfo.new(0.45, Enum.EasingStyle.Quart, Enum.EasingDirection.Out), {Position = UDim2.new(1, -40, 0.5, 0)}):Play()
					TweenService:Create(Toggle.Switch.Indicator.UIStroke, TweenInfo.new(0.55, Enum.EasingStyle.Exponential, Enum.EasingDirection.Out), {Color = SelectedTheme.ToggleDisabledStroke}):Play()
					TweenService:Create(Toggle.Switch.Indicator, TweenInfo.new(0.8, Enum.EasingStyle.Exponential, Enum.EasingDirection.Out), {BackgroundColor3 = SelectedTheme.ToggleDisabled}):Play()
					TweenService:Create(Toggle.Switch.UIStroke, TweenInfo.new(0.55, Enum.EasingStyle.Exponential, Enum.EasingDirection.Out), {Color = SelectedTheme.ToggleDisabledOuterStroke}):Play()
					TweenService:Create(Toggle, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackground}):Play()
					TweenService:Create(Toggle.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 0}):Play()	
				else
					ToggleSettings.CurrentValue = true
					TweenService:Create(Toggle, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackgroundHover}):Play()
					TweenService:Create(Toggle.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
					TweenService:Create(Toggle.Switch.Indicator, TweenInfo.new(0.5, Enum.EasingStyle.Quart, Enum.EasingDirection.Out), {Position = UDim2.new(1, -20, 0.5, 0)}):Play()
					TweenService:Create(Toggle.Switch.Indicator.UIStroke, TweenInfo.new(0.55, Enum.EasingStyle.Exponential, Enum.EasingDirection.Out), {Color = SelectedTheme.ToggleEnabledStroke}):Play()
					TweenService:Create(Toggle.Switch.Indicator, TweenInfo.new(0.8, Enum.EasingStyle.Exponential, Enum.EasingDirection.Out), {BackgroundColor3 = SelectedTheme.ToggleEnabled}):Play()
					TweenService:Create(Toggle.Switch.UIStroke, TweenInfo.new(0.55, Enum.EasingStyle.Exponential, Enum.EasingDirection.Out), {Color = SelectedTheme.ToggleEnabledOuterStroke}):Play()
					TweenService:Create(Toggle, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackground}):Play()
					TweenService:Create(Toggle.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 0}):Play()		
				end

				local Success, Response = pcall(function()
					if debugX then warn('Running toggle \''..ToggleSettings.Name..'\' (Interact)') end

					ToggleSettings.Callback(ToggleSettings.CurrentValue)
				end)

				if not Success then
					TweenService:Create(Toggle, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = Color3.fromRGB(85, 0, 0)}):Play()
					TweenService:Create(Toggle.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
					Toggle.Title.Text = "Callback Error"
					print("Rayfield | "..ToggleSettings.Name.." Callback Error " ..tostring(Response))
					warn('Check docs.sirius.menu for help with Rayfield specific development.')
					task.wait(0.5)
					Toggle.Title.Text = ToggleSettings.Name
					TweenService:Create(Toggle, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackground}):Play()
					TweenService:Create(Toggle.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 0}):Play()
				end

				if not ToggleSettings.Ext then
					SaveConfiguration()
				end
			end)

			function ToggleSettings:Set(NewToggleValue)
				if NewToggleValue == true then
					ToggleSettings.CurrentValue = true
					TweenService:Create(Toggle, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackgroundHover}):Play()
					TweenService:Create(Toggle.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
					TweenService:Create(Toggle.Switch.Indicator, TweenInfo.new(0.5, Enum.EasingStyle.Quart, Enum.EasingDirection.Out), {Position = UDim2.new(1, -20, 0.5, 0)}):Play()
					TweenService:Create(Toggle.Switch.Indicator, TweenInfo.new(0.4, Enum.EasingStyle.Quart, Enum.EasingDirection.Out), {Size = UDim2.new(0,12,0,12)}):Play()
					TweenService:Create(Toggle.Switch.Indicator.UIStroke, TweenInfo.new(0.55, Enum.EasingStyle.Exponential, Enum.EasingDirection.Out), {Color = SelectedTheme.ToggleEnabledStroke}):Play()
					TweenService:Create(Toggle.Switch.Indicator, TweenInfo.new(0.8, Enum.EasingStyle.Exponential, Enum.EasingDirection.Out), {BackgroundColor3 = SelectedTheme.ToggleEnabled}):Play()
					TweenService:Create(Toggle.Switch.UIStroke, TweenInfo.new(0.55, Enum.EasingStyle.Exponential, Enum.EasingDirection.Out), {Color = SelectedTheme.ToggleEnabledOuterStroke}):Play()
					TweenService:Create(Toggle.Switch.Indicator, TweenInfo.new(0.45, Enum.EasingStyle.Quart, Enum.EasingDirection.Out), {Size = UDim2.new(0,17,0,17)}):Play()	
					TweenService:Create(Toggle, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackground}):Play()
					TweenService:Create(Toggle.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 0}):Play()	
				else
					ToggleSettings.CurrentValue = false
					TweenService:Create(Toggle, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackgroundHover}):Play()
					TweenService:Create(Toggle.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
					TweenService:Create(Toggle.Switch.Indicator, TweenInfo.new(0.45, Enum.EasingStyle.Quart, Enum.EasingDirection.Out), {Position = UDim2.new(1, -40, 0.5, 0)}):Play()
					TweenService:Create(Toggle.Switch.Indicator, TweenInfo.new(0.4, Enum.EasingStyle.Quart, Enum.EasingDirection.Out), {Size = UDim2.new(0,12,0,12)}):Play()
					TweenService:Create(Toggle.Switch.Indicator.UIStroke, TweenInfo.new(0.55, Enum.EasingStyle.Exponential, Enum.EasingDirection.Out), {Color = SelectedTheme.ToggleDisabledStroke}):Play()
					TweenService:Create(Toggle.Switch.Indicator, TweenInfo.new(0.8, Enum.EasingStyle.Exponential, Enum.EasingDirection.Out), {BackgroundColor3 = SelectedTheme.ToggleDisabled}):Play()
					TweenService:Create(Toggle.Switch.UIStroke, TweenInfo.new(0.55, Enum.EasingStyle.Exponential, Enum.EasingDirection.Out), {Color = SelectedTheme.ToggleDisabledOuterStroke}):Play()
					TweenService:Create(Toggle.Switch.Indicator, TweenInfo.new(0.4, Enum.EasingStyle.Quart, Enum.EasingDirection.Out), {Size = UDim2.new(0,17,0,17)}):Play()
					TweenService:Create(Toggle, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackground}):Play()
					TweenService:Create(Toggle.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 0}):Play()	
				end

				local Success, Response = pcall(function()
					if debugX then warn('Running toggle \''..ToggleSettings.Name..'\' (:Set)') end

					ToggleSettings.Callback(ToggleSettings.CurrentValue)
				end)

				if not Success then
					TweenService:Create(Toggle, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = Color3.fromRGB(85, 0, 0)}):Play()
					TweenService:Create(Toggle.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
					Toggle.Title.Text = "Callback Error"
					print("Rayfield | "..ToggleSettings.Name.." Callback Error " ..tostring(Response))
					warn('Check docs.sirius.menu for help with Rayfield specific development.')
					task.wait(0.5)
					Toggle.Title.Text = ToggleSettings.Name
					TweenService:Create(Toggle, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackground}):Play()
					TweenService:Create(Toggle.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 0}):Play()
				end

				if not ToggleSettings.Ext then
					SaveConfiguration()
				end
			end

			if not ToggleSettings.Ext then
				if Settings.ConfigurationSaving then
					if Settings.ConfigurationSaving.Enabled and ToggleSettings.Flag then
						RayfieldLibrary.Flags[ToggleSettings.Flag] = ToggleSettings
					end
				end
			end


			Rayfield.Main:GetPropertyChangedSignal('BackgroundColor3'):Connect(function()
				Toggle.Switch.BackgroundColor3 = SelectedTheme.ToggleBackground

				if SelectedTheme ~= RayfieldLibrary.Theme.Default then
					Toggle.Switch.Shadow.Visible = false
				end

				task.wait()

				if not ToggleSettings.CurrentValue then
					Toggle.Switch.Indicator.UIStroke.Color = SelectedTheme.ToggleDisabledStroke
					Toggle.Switch.Indicator.BackgroundColor3 = SelectedTheme.ToggleDisabled
					Toggle.Switch.UIStroke.Color = SelectedTheme.ToggleDisabledOuterStroke
				else
					Toggle.Switch.Indicator.UIStroke.Color = SelectedTheme.ToggleEnabledStroke
					Toggle.Switch.Indicator.BackgroundColor3 = SelectedTheme.ToggleEnabled
					Toggle.Switch.UIStroke.Color = SelectedTheme.ToggleEnabledOuterStroke
				end
			end)

			return ToggleSettings
		end

		-- Slider
		function Tab:CreateSlider(SliderSettings)
			local SLDragging = false
			local Slider = Elements.Template.Slider:Clone()
			Slider.Name = SliderSettings.Name
			Slider.Title.Text = SliderSettings.Name
			Slider.Visible = true
			Slider.Parent = TabPage

			Slider.BackgroundTransparency = 1
			Slider.UIStroke.Transparency = 1
			Slider.Title.TextTransparency = 1

			if SelectedTheme ~= RayfieldLibrary.Theme.Default then
				Slider.Main.Shadow.Visible = false
			end

			Slider.Main.BackgroundColor3 = SelectedTheme.SliderBackground
			Slider.Main.UIStroke.Color = SelectedTheme.SliderStroke
			Slider.Main.Progress.UIStroke.Color = SelectedTheme.SliderStroke
			Slider.Main.Progress.BackgroundColor3 = SelectedTheme.SliderProgress

			TweenService:Create(Slider, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0}):Play()
			TweenService:Create(Slider.UIStroke, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {Transparency = 0}):Play()
			TweenService:Create(Slider.Title, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {TextTransparency = 0}):Play()	

			Slider.Main.Progress.Size =	UDim2.new(0, Slider.Main.AbsoluteSize.X * ((SliderSettings.CurrentValue - SliderSettings.Range[1]) / (SliderSettings.Range[2] - SliderSettings.Range[1])) > 5 and Slider.Main.AbsoluteSize.X * ((SliderSettings.CurrentValue - SliderSettings.Range[1]) / (SliderSettings.Range[2] - SliderSettings.Range[1])) or 5, 1, 0)

			if not SliderSettings.Suffix then
				Slider.Main.Information.Text = tostring(SliderSettings.CurrentValue)
			else
				Slider.Main.Information.Text = tostring(SliderSettings.CurrentValue) .. " " .. SliderSettings.Suffix
			end

			Slider.MouseEnter:Connect(function()
				TweenService:Create(Slider, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackgroundHover}):Play()
			end)

			Slider.MouseLeave:Connect(function()
				TweenService:Create(Slider, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackground}):Play()
			end)

			Slider.Main.Interact.InputBegan:Connect(function(Input)
				if Input.UserInputType == Enum.UserInputType.MouseButton1 or Input.UserInputType == Enum.UserInputType.Touch then 
					TweenService:Create(Slider.Main.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
					TweenService:Create(Slider.Main.Progress.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
					SLDragging = true 
				end 
			end)

			Slider.Main.Interact.InputEnded:Connect(function(Input) 
				if Input.UserInputType == Enum.UserInputType.MouseButton1 or Input.UserInputType == Enum.UserInputType.Touch then 
					TweenService:Create(Slider.Main.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 0.4}):Play()
					TweenService:Create(Slider.Main.Progress.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 0.3}):Play()
					SLDragging = false 
				end 
			end)

			Slider.Main.Interact.MouseButton1Down:Connect(function(X)
				local Current = Slider.Main.Progress.AbsolutePosition.X + Slider.Main.Progress.AbsoluteSize.X
				local Start = Current
				local Location = X
				local Loop; Loop = RunService.Stepped:Connect(function()
					if SLDragging then
						Location = UserInputService:GetMouseLocation().X
						Current = Current + 0.025 * (Location - Start)

						if Location < Slider.Main.AbsolutePosition.X then
							Location = Slider.Main.AbsolutePosition.X
						elseif Location > Slider.Main.AbsolutePosition.X + Slider.Main.AbsoluteSize.X then
							Location = Slider.Main.AbsolutePosition.X + Slider.Main.AbsoluteSize.X
						end

						if Current < Slider.Main.AbsolutePosition.X + 5 then
							Current = Slider.Main.AbsolutePosition.X + 5
						elseif Current > Slider.Main.AbsolutePosition.X + Slider.Main.AbsoluteSize.X then
							Current = Slider.Main.AbsolutePosition.X + Slider.Main.AbsoluteSize.X
						end

						if Current <= Location and (Location - Start) < 0 then
							Start = Location
						elseif Current >= Location and (Location - Start) > 0 then
							Start = Location
						end
						TweenService:Create(Slider.Main.Progress, TweenInfo.new(0.45, Enum.EasingStyle.Exponential, Enum.EasingDirection.Out), {Size = UDim2.new(0, Current - Slider.Main.AbsolutePosition.X, 1, 0)}):Play()
						local NewValue = SliderSettings.Range[1] + (Location - Slider.Main.AbsolutePosition.X) / Slider.Main.AbsoluteSize.X * (SliderSettings.Range[2] - SliderSettings.Range[1])

						NewValue = math.floor(NewValue / SliderSettings.Increment + 0.5) * (SliderSettings.Increment * 10000000) / 10000000
						NewValue = math.clamp(NewValue, SliderSettings.Range[1], SliderSettings.Range[2])

						if not SliderSettings.Suffix then
							Slider.Main.Information.Text = tostring(NewValue)
						else
							Slider.Main.Information.Text = tostring(NewValue) .. " " .. SliderSettings.Suffix
						end

						if SliderSettings.CurrentValue ~= NewValue then
							local Success, Response = pcall(function()
								SliderSettings.Callback(NewValue)
							end)
							if not Success then
								TweenService:Create(Slider, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = Color3.fromRGB(85, 0, 0)}):Play()
								TweenService:Create(Slider.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
								Slider.Title.Text = "Callback Error"
								print("Rayfield | "..SliderSettings.Name.." Callback Error " ..tostring(Response))
								warn('Check docs.sirius.menu for help with Rayfield specific development.')
								task.wait(0.5)
								Slider.Title.Text = SliderSettings.Name
								TweenService:Create(Slider, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackground}):Play()
								TweenService:Create(Slider.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 0}):Play()
							end

							SliderSettings.CurrentValue = NewValue
							if not SliderSettings.Ext then
								SaveConfiguration()
							end
						end
					else
						TweenService:Create(Slider.Main.Progress, TweenInfo.new(0.3, Enum.EasingStyle.Exponential, Enum.EasingDirection.Out), {Size = UDim2.new(0, Location - Slider.Main.AbsolutePosition.X > 5 and Location - Slider.Main.AbsolutePosition.X or 5, 1, 0)}):Play()
						Loop:Disconnect()
					end
				end)
			end)

			function SliderSettings:Set(NewVal)
				local NewVal = math.clamp(NewVal, SliderSettings.Range[1], SliderSettings.Range[2])

				TweenService:Create(Slider.Main.Progress, TweenInfo.new(0.45, Enum.EasingStyle.Exponential, Enum.EasingDirection.Out), {Size = UDim2.new(0, Slider.Main.AbsoluteSize.X * ((NewVal - SliderSettings.Range[1]) / (SliderSettings.Range[2] - SliderSettings.Range[1])) > 5 and Slider.Main.AbsoluteSize.X * ((NewVal - SliderSettings.Range[1]) / (SliderSettings.Range[2] - SliderSettings.Range[1])) or 5, 1, 0)}):Play()
				Slider.Main.Information.Text = tostring(NewVal) .. " " .. (SliderSettings.Suffix or "")

				local Success, Response = pcall(function()
					SliderSettings.Callback(NewVal)
				end)

				if not Success then
					TweenService:Create(Slider, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = Color3.fromRGB(85, 0, 0)}):Play()
					TweenService:Create(Slider.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 1}):Play()
					Slider.Title.Text = "Callback Error"
					print("Rayfield | "..SliderSettings.Name.." Callback Error " ..tostring(Response))
					warn('Check docs.sirius.menu for help with Rayfield specific development.')
					task.wait(0.5)
					Slider.Title.Text = SliderSettings.Name
					TweenService:Create(Slider, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.ElementBackground}):Play()
					TweenService:Create(Slider.UIStroke, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {Transparency = 0}):Play()
				end

				SliderSettings.CurrentValue = NewVal
				if not SliderSettings.Ext then
					SaveConfiguration()
				end
			end

			if Settings.ConfigurationSaving then
				if Settings.ConfigurationSaving.Enabled and SliderSettings.Flag then
					RayfieldLibrary.Flags[SliderSettings.Flag] = SliderSettings
				end
			end

			Rayfield.Main:GetPropertyChangedSignal('BackgroundColor3'):Connect(function()
				if SelectedTheme ~= RayfieldLibrary.Theme.Default then
					Slider.Main.Shadow.Visible = false
				end

				Slider.Main.BackgroundColor3 = SelectedTheme.SliderBackground
				Slider.Main.UIStroke.Color = SelectedTheme.SliderStroke
				Slider.Main.Progress.UIStroke.Color = SelectedTheme.SliderStroke
				Slider.Main.Progress.BackgroundColor3 = SelectedTheme.SliderProgress
			end)

			return SliderSettings
		end

		Rayfield.Main:GetPropertyChangedSignal('BackgroundColor3'):Connect(function()
			TabButton.UIStroke.Color = SelectedTheme.TabStroke

			if Elements.UIPageLayout.CurrentPage == TabPage then
				TabButton.BackgroundColor3 = SelectedTheme.TabBackgroundSelected
				TabButton.Image.ImageColor3 = SelectedTheme.SelectedTabTextColor
				TabButton.Title.TextColor3 = SelectedTheme.SelectedTabTextColor
			else
				TabButton.BackgroundColor3 = SelectedTheme.TabBackground
				TabButton.Image.ImageColor3 = SelectedTheme.TabTextColor
				TabButton.Title.TextColor3 = SelectedTheme.TabTextColor
			end
		end)

		return Tab
	end

	Elements.Visible = true


	task.wait(1.1)
	TweenService:Create(Main, TweenInfo.new(0.7, Enum.EasingStyle.Exponential, Enum.EasingDirection.InOut), {Size = UDim2.new(0, 390, 0, 90)}):Play()
	task.wait(0.3)
	TweenService:Create(LoadingFrame.Title, TweenInfo.new(0.2, Enum.EasingStyle.Exponential), {TextTransparency = 1}):Play()
	TweenService:Create(LoadingFrame.Subtitle, TweenInfo.new(0.2, Enum.EasingStyle.Exponential), {TextTransparency = 1}):Play()
	TweenService:Create(LoadingFrame.Version, TweenInfo.new(0.2, Enum.EasingStyle.Exponential), {TextTransparency = 1}):Play()
	task.wait(0.1)
	TweenService:Create(Main, TweenInfo.new(0.6, Enum.EasingStyle.Exponential, Enum.EasingDirection.Out), {Size = useMobileSizing and UDim2.new(0, 500, 0, 275) or UDim2.new(0, 500, 0, 475)}):Play()
	TweenService:Create(Main.Shadow.Image, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {ImageTransparency = 0.6}):Play()

	Topbar.BackgroundTransparency = 1
	Topbar.Divider.Size = UDim2.new(0, 0, 0, 1)
	Topbar.Divider.BackgroundColor3 = SelectedTheme.ElementStroke
	Topbar.CornerRepair.BackgroundTransparency = 1
	Topbar.Title.TextTransparency = 1
	Topbar.Search.ImageTransparency = 1
	if Topbar:FindFirstChild('Settings') then
		Topbar.Settings.ImageTransparency = 1
	end
	Topbar.ChangeSize.ImageTransparency = 1
	Topbar.Hide.ImageTransparency = 1


	task.wait(0.5)
	Topbar.Visible = true
	TweenService:Create(Topbar, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0}):Play()
	TweenService:Create(Topbar.CornerRepair, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0}):Play()
	task.wait(0.1)
	TweenService:Create(Topbar.Divider, TweenInfo.new(1, Enum.EasingStyle.Exponential), {Size = UDim2.new(1, 0, 0, 1)}):Play()
	TweenService:Create(Topbar.Title, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {TextTransparency = 0}):Play()
	task.wait(0.05)
	TweenService:Create(Topbar.Search, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {ImageTransparency = 0.8}):Play()
	task.wait(0.05)
	if Topbar:FindFirstChild('Settings') then
		TweenService:Create(Topbar.Settings, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {ImageTransparency = 0.8}):Play()
		task.wait(0.05)
	end
	TweenService:Create(Topbar.ChangeSize, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {ImageTransparency = 0.8}):Play()
	task.wait(0.05)
	TweenService:Create(Topbar.Hide, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {ImageTransparency = 0.8}):Play()
	task.wait(0.3)

	if dragBar then
		TweenService:Create(dragBarCosmetic, TweenInfo.new(0.6, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0.7}):Play()
	end

	function Window.ModifyTheme(NewTheme)
		local success = pcall(ChangeTheme, NewTheme)
		if not success then
			RayfieldLibrary:Notify({Title = 'Unable to Change Theme', Content = 'We are unable find a theme on file.', Image = 4400704299})
		else
			RayfieldLibrary:Notify({Title = 'Theme Changed', Content = 'Successfully changed theme to '..(typeof(NewTheme) == 'string' and NewTheme or 'Custom Theme')..'.', Image = 4483362748})
		end
	end

	local success, result = pcall(function()
		createSettings(Window)
	end)

	if not success then warn('Rayfield had an issue creating settings.') end

	-- Report after createSettings so loadSettings() has run and usageAnalytics reflects the user's saved preference
	if analyticsAllowed() and loadReporter() then
		local themeName = "Default"
		if Settings.Theme then
			if type(Settings.Theme) == "string" then
				themeName = Settings.Theme
			elseif type(Settings.Theme) == "table" then
				themeName = "Custom"
			end
		end

		local discordInvite = nil
		if Settings.Discord and Settings.Discord.Enabled and Settings.Discord.Invite and Settings.Discord.Invite ~= "" then
			local raw = tostring(Settings.Discord.Invite)
			-- Normalize: strip URL prefixes to extract just the invite code
			discordInvite = (raw:match("discord%.gg/([%w%-]+)") or raw:match("discord%.com/invite/([%w%-]+)") or raw):sub(1, 32)
		end

		local sampleSend = false

		-- Random Sampling Test
		if not Settings.ScriptID and math.random() > 0.4 then
			sampleSend = true
		end

		--if Settings.ScriptID then
			reporter:windowCreated({
				script_name        = Settings.Name or "Unknown",
				script_version     = Release,
				interface_version  = InterfaceBuild,
				theme              = themeName,
				is_mobile          = useMobileSizing and true or false,
				has_key_system     = Settings.KeySystem and true or false,
				discord_invite     = discordInvite,
				config_saving      = (Settings.ConfigurationSaving and Settings.ConfigurationSaving.Enabled) and true or false,
				script_id          = Settings.ScriptID or sampleSend and 'sid_tzfyxawonjx9' or nil,
				verification_token = Settings.VerificationToken,
			})
		--end
	end

	return Window
end

local function setVisibility(visibility: boolean, notify: boolean?)
	if Debounce then return end
	if visibility then
		Hidden = false
		Unhide()
	else
		Hidden = true
		Hide(notify)
	end
end

function RayfieldLibrary:SetVisibility(visibility: boolean)
	setVisibility(visibility, false)
end

function RayfieldLibrary:IsVisible(): boolean
	return not Hidden
end

local hideHotkeyConnection -- Has to be initialized here since the connection is made later in the script
function RayfieldLibrary:Destroy()
	rayfieldDestroyed = true
	-- stops the kick watcher the reporter armed, so nothing is sent for a window that's gone
	if reporter and reporter.disable then
		pcall(reporter.disable, reporter)
	end
	if hideHotkeyConnection then
		hideHotkeyConnection:Disconnect()
	end
	for _, connection in keybindConnections do
		connection:Disconnect()
	end
	Rayfield:Destroy()
end

Topbar.ChangeSize.MouseButton1Click:Connect(function()
	if Debounce then return end
	if Minimised then
		Minimised = false
		Maximise()
	else
		Minimised = true
		Minimise()
	end
end)

Main.Search.Input:GetPropertyChangedSignal('Text'):Connect(function()
	if #Main.Search.Input.Text > 0 then
		if not Elements.UIPageLayout.CurrentPage:FindFirstChild('SearchTitle-fsefsefesfsefesfesfThanks') then 
			local searchTitle = Elements.Template.SectionTitle:Clone()
			searchTitle.Parent = Elements.UIPageLayout.CurrentPage
			searchTitle.Name = 'SearchTitle-fsefsefesfsefesfesfThanks'
			searchTitle.LayoutOrder = -100
			searchTitle.Title.Text = "Results from '"..Elements.UIPageLayout.CurrentPage.Name.."'"
			searchTitle.Visible = true
		end
	else
		local searchTitle = Elements.UIPageLayout.CurrentPage:FindFirstChild('SearchTitle-fsefsefesfsefesfesfThanks')

		if searchTitle then
			searchTitle:Destroy()
		end
	end

	for _, element in ipairs(Elements.UIPageLayout.CurrentPage:GetChildren()) do
		if element.ClassName ~= 'UIListLayout' and element.Name ~= 'Placeholder' and element.Name ~= 'SearchTitle-fsefsefesfsefesfesfThanks' then
			if element.Name == 'SectionTitle' then
				if #Main.Search.Input.Text == 0 then
					element.Visible = true
				else
					element.Visible = false
				end
			else
				if string.lower(element.Name):find(string.lower(Main.Search.Input.Text), 1, true) then
					element.Visible = true
				else
					element.Visible = false
				end
			end
		end
	end
end)

Main.Search.Input.FocusLost:Connect(function(enterPressed)
	if #Main.Search.Input.Text == 0 and searchOpen then
		task.wait(0.12)
		closeSearch()
	end
end)

Topbar.Search.MouseButton1Click:Connect(function()
	task.spawn(function()
		if searchOpen then
			closeSearch()
		else
			openSearch()
		end
	end)
end)

if Topbar:FindFirstChild('Settings') then
	Topbar.Settings.MouseButton1Click:Connect(function()
		task.spawn(function()
			for _, OtherTabButton in ipairs(TabList:GetChildren()) do
				if OtherTabButton.Name ~= "Template" and OtherTabButton.ClassName == "Frame" and OtherTabButton.Name ~= "Placeholder" then
					TweenService:Create(OtherTabButton, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {BackgroundColor3 = SelectedTheme.TabBackground}):Play()
					TweenService:Create(OtherTabButton.Title, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {TextColor3 = SelectedTheme.TabTextColor}):Play()
					TweenService:Create(OtherTabButton.Image, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {ImageColor3 = SelectedTheme.TabTextColor}):Play()
					TweenService:Create(OtherTabButton, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {BackgroundTransparency = 0.7}):Play()
					TweenService:Create(OtherTabButton.Title, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {TextTransparency = 0.2}):Play()
					TweenService:Create(OtherTabButton.Image, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {ImageTransparency = 0.2}):Play()
					TweenService:Create(OtherTabButton.UIStroke, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {Transparency = 0.5}):Play()
				end
			end

			Elements.UIPageLayout:JumpTo(Elements['Rayfield Settings'])
		end)
	end)

end


Topbar.Hide.MouseButton1Click:Connect(function()
	setVisibility(Hidden, not useMobileSizing)
end)

hideHotkeyConnection = UserInputService.InputBegan:Connect(function(input, processed)
	if rayfieldDestroyed then return end
	if (input.KeyCode == Enum.KeyCode[getSetting("General", "rayfieldOpen")]) and not processed then
		if Debounce then return end
		if Hidden then
			Hidden = false
			Unhide()
		else
			Hidden = true
			Hide()
		end
	end
end)

if MPrompt then
	MPrompt.Interact.MouseButton1Click:Connect(function()
		if Debounce then return end
		if Hidden then
			Hidden = false
			Unhide()
		end
	end)
end

for _, TopbarButton in ipairs(Topbar:GetChildren()) do
	if TopbarButton.ClassName == "ImageButton" and TopbarButton.Name ~= 'Icon' then
		TopbarButton.MouseEnter:Connect(function()
			TweenService:Create(TopbarButton, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {ImageTransparency = 0}):Play()
		end)

		TopbarButton.MouseLeave:Connect(function()
			TweenService:Create(TopbarButton, TweenInfo.new(0.7, Enum.EasingStyle.Exponential), {ImageTransparency = 0.8}):Play()
		end)
	end
end


function RayfieldLibrary:LoadConfiguration()
	local config

	if debugX then
		warn('Loading Configuration')
	end

	if useStudio then
		config = [[{"Toggle1adwawd":true,"ColorPicker1awd":{"B":255,"G":255,"R":255},"Slider1dawd":100,"ColorPicfsefker1":{"B":255,"G":255,"R":255},"Slidefefsr1":80,"dawdawd":"","Input1":"hh","Keybind1":"B","Dropdown1":["Ocean"]}]]
	end

	if CEnabled then
		local notified
		local loaded

		local success, result = pcall(function()
			if useStudio and config then
				loaded = LoadConfiguration(config)
				return
			end

			if isfile then 
				local configPath = ConfigurationFolder .. "/" .. CFileName .. ConfigurationExtension
				if CLegacyFileName and not callSafely(isfile, configPath) then
					local legacyPath = ConfigurationFolder .. "/" .. CLegacyFileName .. ConfigurationExtension
					if callSafely(isfile, legacyPath) then
						configPath = legacyPath
					end
				end
				if callSafely(isfile, configPath) then
					loaded = LoadConfiguration(callSafely(readfile, configPath))
				end
			else
				notified = true
				RayfieldLibrary:Notify({Title = "Rayfield Configurations", Content = "We couldn't enable Configuration Saving as you are not using software with filesystem support.", Image = 4384402990})
			end
		end)

		if success and loaded and not notified then
			RayfieldLibrary:Notify({Title = "Rayfield Configurations", Content = "The configuration file for this script has been loaded from a previous session.", Image = 4384403532})
		elseif not success and not notified then
			warn('Rayfield Configurations Error | '..tostring(result))
			RayfieldLibrary:Notify({Title = "Rayfield Configurations", Content = "We've encountered an issue loading your configuration correctly.\n\nCheck the Developer Console for more information.", Image = 4384402990})
		end
	end

	globalLoaded = true
end



if useStudio then
	-- run w/ studio
	-- Feel free to place your own script here to see how it'd work in Roblox Studio before running it on your execution software.


	--local Window = RayfieldLibrary:CreateWindow({
	--	Name = "Rayfield Example Window",
	--	LoadingTitle = "Rayfield Interface Suite",
	--	Theme = 'Default',
	--	Icon = 0,
	--	LoadingSubtitle = "by Sirius",
	--	ConfigurationSaving = {
	--		Enabled = true,
	--		FolderName = nil, -- Create a custom folder for your hub/game
	--		FileName = "Big Hub52"
	--	},
	--	Discord = {
	--		Enabled = false,
	--		Invite = "noinvitelink", -- The Discord invite code, do not include discord.gg/. E.g. discord.gg/ABCD would be ABCD
	--		RememberJoins = true -- Set this to false to make them join the discord every time they load it up
	--	},
	--	KeySystem = false, -- Set this to true to use our key system
	--	KeySettings = {
	--		Title = "Untitled",
	--		Subtitle = "Key System",
	--		Note = "No method of obtaining the key is provided",
	--		FileName = "Key", -- It is recommended to use something unique as other scripts using Rayfield may overwrite your key file
	--		SaveKey = true, -- The user's key will be saved, but if you change the key, they will be unable to use your script
	--		GrabKeyFromSite = false, -- If this is true, set Key below to the RAW site you would like Rayfield to get the key from
	--		Key = {"Hello"} -- List of keys that will be accepted by the system, can be RAW file links (pastebin, github etc) or simple strings ("hello","key22")
	--	}
	--})

	--local Tab = Window:CreateTab("Tab Example", 'key-round') -- Title, Image
	--local Tab2 = Window:CreateTab("Tab Example 2", 4483362458) -- Title, Image

	--local Section = Tab2:CreateSection("Section")


	--local ColorPicker = Tab2:CreateColorPicker({
	--	Name = "Color Picker",
	--	Color = Color3.fromRGB(255,255,255),
	--	Flag = "ColorPicfsefker1", -- A flag is the identifier for the configuration file, make sure every element has a different flag if you're using configuration saving to ensure no overlaps
	--	Callback = function(Value)
	--		-- The function that takes place every time the color picker is moved/changed
	--		-- The variable (Value) is a Color3fromRGB value based on which color is selected
	--	end
	--})

	--local Slider = Tab2:CreateSlider({
	--	Name = "Slider Example",
	--	Range = {0, 100},
	--	Increment = 10,
	--	Suffix = "Bananas",
	--	CurrentValue = 40,
	--	Flag = "Slidefefsr1", -- A flag is the identifier for the configuration file, make sure every element has a different flag if you're using configuration saving to ensure no overlaps
	--	Callback = function(Value)
	--		-- The function that takes place when the slider changes
	--		-- The variable (Value) is a number which correlates to the value the slider is currently at
	--	end,
	--})

	--local Input = Tab2:CreateInput({
	--	Name = "Input Example",
	--	CurrentValue = '',
	--	PlaceholderText = "Input Placeholder",
	--	Flag = 'dawdawd',
	--	RemoveTextAfterFocusLost = false,
	--	Callback = function(Text)
	--		-- The function that takes place when the input is changed
	--		-- The variable (Text) is a string for the value in the text box
	--	end,
	--})


	----RayfieldLibrary:Notify({Title = "Rayfield Interface", Content = "Welcome to Rayfield. These - are the brand new notification design for Rayfield, with custom sizing and Rayfield calculated wait times.", Image = 4483362458})

	--local Section = Tab:CreateSection("Section Example")

	--local Button = Tab:CreateButton({
	--	Name = "Change Theme",
	--	Callback = function()
	--		-- The function that takes place when the button is pressed
	--		Window.ModifyTheme('DarkBlue')
	--	end,
	--})

	--local Toggle = Tab:CreateToggle({
	--	Name = "Toggle Example",
	--	CurrentValue = false,
	--	Flag = "Toggle1adwawd", -- A flag is the identifier for the configuration file, make sure every element has a different flag if you're using configuration saving to ensure no overlaps
	--	Callback = function(Value)
	--		-- The function that takes place when the toggle is pressed
	--		-- The variable (Value) is a boolean on whether the toggle is true or false
	--	end,
	--})

	--local ColorPicker = Tab:CreateColorPicker({
	--	Name = "Color Picker",
	--	Color = Color3.fromRGB(255,255,255),
	--	Flag = "ColorPicker1awd", -- A flag is the identifier for the configuration file, make sure every element has a different flag if you're using configuration saving to ensure no overlaps
	--	Callback = function(Value)
	--		-- The function that takes place every time the color picker is moved/changed
	--		-- The variable (Value) is a Color3fromRGB value based on which color is selected
	--	end
	--})

	--local Slider = Tab:CreateSlider({
	--	Name = "Slider Example",
	--	Range = {0, 100},
	--	Increment = 10,
	--	Suffix = "Bananas",
	--	CurrentValue = 40,
	--	Flag = "Slider1dawd", -- A flag is the identifier for the configuration file, make sure every element has a different flag if you're using configuration saving to ensure no overlaps
	--	Callback = function(Value)
	--		-- The function that takes place when the slider changes
	--		-- The variable (Value) is a number which correlates to the value the slider is currently at
	--	end,
	--})

	--local Input = Tab:CreateInput({
	--	Name = "Input Example",
	--	CurrentValue = "Helo",
	--	PlaceholderText = "Adaptive Input",
	--	RemoveTextAfterFocusLost = false,
	--	Flag = 'Input1',
	--	Callback = function(Text)
	--		-- The function that takes place when the input is changed
	--		-- The variable (Text) is a string for the value in the text box
	--	end,
	--})

	--local thoptions = {}
	--for themename, theme in pairs(RayfieldLibrary.Theme) do
	--	table.insert(thoptions, themename)
	--end

	--local Dropdown = Tab:CreateDropdown({
	--	Name = "Theme",
	--	Options = thoptions,
	--	CurrentOption = {"Default"},
	--	MultipleOptions = false,
	--	Flag = "Dropdown1", -- A flag is the identifier for the configuration file, make sure every element has a different flag if you're using configuration saving to ensure no overlaps
	--	Callback = function(Options)
	--		--Window.ModifyTheme(Options[1])
	--		-- The function that takes place when the selected option is changed
	--		-- The variable (Options) is a table of strings for the current selected options
	--	end,
	--})


	--Window.ModifyTheme({
	--	TextColor = Color3.fromRGB(50, 55, 60),
	--	Background = Color3.fromRGB(240, 245, 250),
	--	Topbar = Color3.fromRGB(215, 225, 235),
	--	Shadow = Color3.fromRGB(200, 210, 220),

	--	NotificationBackground = Color3.fromRGB(210, 220, 230),
	--	NotificationActionsBackground = Color3.fromRGB(225, 230, 240),

	--	TabBackground = Color3.fromRGB(200, 210, 220),
	--	TabStroke = Color3.fromRGB(180, 190, 200),
	--	TabBackgroundSelected = Color3.fromRGB(175, 185, 200),
	--	TabTextColor = Color3.fromRGB(50, 55, 60),
	--	SelectedTabTextColor = Color3.fromRGB(30, 35, 40),

	--	ElementBackground = Color3.fromRGB(210, 220, 230),
	--	ElementBackgroundHover = Color3.fromRGB(220, 230, 240),
	--	SecondaryElementBackground = Color3.fromRGB(200, 210, 220),
	--	ElementStroke = Color3.fromRGB(190, 200, 210),
	--	SecondaryElementStroke = Color3.fromRGB(180, 190, 200),

	--	SliderBackground = Color3.fromRGB(200, 220, 235),  -- Lighter shade
	--	SliderProgress = Color3.fromRGB(70, 130, 180),
	--	SliderStroke = Color3.fromRGB(150, 180, 220),

	--	ToggleBackground = Color3.fromRGB(210, 220, 230),
	--	ToggleEnabled = Color3.fromRGB(70, 160, 210),
	--	ToggleDisabled = Color3.fromRGB(180, 180, 180),
	--	ToggleEnabledStroke = Color3.fromRGB(60, 150, 200),
	--	ToggleDisabledStroke = Color3.fromRGB(140, 140, 140),
	--	ToggleEnabledOuterStroke = Color3.fromRGB(100, 120, 140),
	--	ToggleDisabledOuterStroke = Color3.fromRGB(120, 120, 130),

	--	DropdownSelected = Color3.fromRGB(220, 230, 240),
	--	DropdownUnselected = Color3.fromRGB(200, 210, 220),

	--	InputBackground = Color3.fromRGB(220, 230, 240),
	--	InputStroke = Color3.fromRGB(180, 190, 200),
	--	PlaceholderColor = Color3.fromRGB(150, 150, 150)
	--})

	--local Keybind = Tab:CreateKeybind({
	--	Name = "Keybind Example",
	--	CurrentKeybind = "Q",
	--	HoldToInteract = false,
	--	Flag = "Keybind1", -- A flag is the identifier for the configuration file, make sure every element has a different flag if you're using configuration saving to ensure no overlaps
	--	Callback = function(Keybind)
	--		-- The function that takes place when the keybind is pressed
	--		-- The variable (Keybind) is a boolean for whether the keybind is being held or not (HoldToInteract needs to be true)
	--	end,
	--})

	--local Label = Tab:CreateLabel("Label Example")

	--local Label2 = Tab:CreateLabel("Warning", 4483362458, Color3.fromRGB(255, 159, 49),  true)

	--local Paragraph = Tab:CreateParagraph({Title = "Paragraph Example", Content = "Paragraph ExampleParagraph ExampleParagraph ExampleParagraph ExampleParagraph ExampleParagraph ExampleParagraph ExampleParagraph ExampleParagraph ExampleParagraph ExampleParagraph ExampleParagraph ExampleParagraph ExampleParagraph Example"})
end

if CEnabled and Main:FindFirstChild('Notice') then
	Main.Notice.BackgroundTransparency = 1
	Main.Notice.Title.TextTransparency = 1
	Main.Notice.Size = UDim2.new(0, 0, 0, 0)
	Main.Notice.Position = UDim2.new(0.5, 0, 0, -100)
	Main.Notice.Visible = true


	TweenService:Create(Main.Notice, TweenInfo.new(0.5, Enum.EasingStyle.Exponential, Enum.EasingDirection.InOut), {Size = UDim2.new(0, 280, 0, 35), Position = UDim2.new(0.5, 0, 0, -50), BackgroundTransparency = 0.5}):Play()
	TweenService:Create(Main.Notice.Title, TweenInfo.new(0.5, Enum.EasingStyle.Exponential), {TextTransparency = 0.1}):Play()
end
-- AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA why :(
--if not useStudio then
--	task.spawn(loadWithTimeout, "https://raw.githubusercontent.com/SiriusSoftwareLtd/Sirius/refs/heads/request/boost.lua")
--end

task.delay(4, function()
	RayfieldLibrary.LoadConfiguration()
	if Main:FindFirstChild('Notice') and Main.Notice.Visible then
		TweenService:Create(Main.Notice, TweenInfo.new(0.5, Enum.EasingStyle.Exponential, Enum.EasingDirection.InOut), {Size = UDim2.new(0, 100, 0, 25), Position = UDim2.new(0.5, 0, 0, -100), BackgroundTransparency = 1}):Play()
		TweenService:Create(Main.Notice.Title, TweenInfo.new(0.3, Enum.EasingStyle.Exponential), {TextTransparency = 1}):Play()

		task.wait(0.5)
		Main.Notice.Visible = false
	end
end)

return RayfieldLibrary

]=======]

local function patchRayfield(src)
    -- Rayfield leak patch (seed farm v10.95): SetDropdownOptions
    -- connects a theme handler for EVERY dropdown option that keeps
    -- indexing the option frame forever. Refresh destroys old option
    -- frames, so any later theme change errors "UIStroke is not a
    -- valid member of Frame" once per stale option. Guard both
    -- leaked handlers. Fail-open: if an anchor ever changes
    -- upstream, the unpatched library loads.
    local patched = false
    local a1 = "DropdownOption.UIStroke.Color = SelectedTheme.ElementStroke"
    if src:find(a1, 1, true) then
        src = src:gsub(
            "DropdownOption%.UIStroke%.Color = SelectedTheme%.ElementStroke",
            'local __s = DropdownOption:FindFirstChild("UIStroke"); '
                .. 'if __s then __s.Color = SelectedTheme.ElementStroke end',
            1)
        patched = true
    end
    local TAB = string.char(9)
    local a2 = "GetPropertyChangedSignal('BackgroundColor3')"
        .. ":Connect(function()\n" .. TAB:rep(6)
        .. "if not table.find(DropdownSettings.CurrentOption, droption.Name) then"
    local p2 = src:find(a2, 1, true)
    if p2 then
        local r2 = "GetPropertyChangedSignal('BackgroundColor3')"
            .. ":Connect(function()\n" .. TAB:rep(6)
            .. "if not droption.Parent then return end\n" .. TAB:rep(6)
            .. "if not table.find(DropdownSettings.CurrentOption, droption.Name) then"
        src = src:sub(1, p2 - 1) .. r2 .. src:sub(p2 + #a2)
        patched = true
    end
    return src, patched
end

local function loadFromSource(src, label)
    local patchedSrc, patched = patchRayfield(src)
    local chunk, cerr = loadstring(patchedSrc)
    if not chunk and patched then
        chunk, cerr = loadstring(src) -- pristine fallback
    end
    if not chunk then
        print("[TrainerCatch] rayfield (" .. label .. ") compile failed: "
            .. tostring(cerr))
        return nil
    end
    print("[TrainerCatch] rayfield leak patch: "
        .. (patched and "applied" or "anchor missed - unpatched")
        .. " (" .. label .. ")")
    local ok, result = pcall(chunk)
    if not ok or not result then
        print("[TrainerCatch] rayfield (" .. label .. ") execute failed: "
            .. tostring(result))
        return nil
    end
    return result
end

local Rayfield = nil
-- stage A: live download (2 attempts, exact error printed)
for attempt = 1, 2 do
    local okHttp, srcOrErr = pcall(function()
        return game:HttpGet("https://sirius.menu/rayfield")
    end)
    if okHttp and type(srcOrErr) == "string" and #srcOrErr > 1000 then
        Rayfield = loadFromSource(srcOrErr, "download")
        if Rayfield then break end
    else
        print("[TrainerCatch] rayfield download attempt " .. attempt
            .. " failed: " .. tostring(srcOrErr))
    end
    if attempt < 2 then task.wait(2) end
end
-- stage B: embedded copy
if not Rayfield then
    print("[TrainerCatch] using embedded rayfield copy")
    Rayfield = loadFromSource(EMBEDDED_RAYFIELD, "embedded")
end
if not Rayfield then
    error("[TrainerCatch] Rayfield failed to load (download + embedded) - GUI unavailable")
end


local Window = Rayfield:CreateWindow({
    Name = "🐂 Trainer + Catch v2.20",
    LoadingTitle = "Trainer + Catch v2.20",
    LoadingSubtitle = "Tame a Bull - Rayfield edition",
    ShowText = "Trainer + Catch",
    Theme = "Default",
    ToggleUIKeybind = "K",
    DisableRayfieldPrompts = true,
    ConfigurationSaving = { Enabled = false },
    KeySystem = false,
})
if getgenv then getgenv().__BullCatchWindow = Window end

local CatchTab = Window:CreateTab("🐂 Catch", nil)
local TrainerTab = Window:CreateTab("🏋️ Trainer", nil)
local PlayerTab = Window:CreateTab("🚶 Player", nil)
local EspTab = Window:CreateTab("👁️ ESP", nil) -- v2.20: created with the other tabs, not at end of file

-- ---------- Catch ----------
catchStatusPara = CatchTab:CreateParagraph({
    Title = "Auto Catch Status",
    Content = catchStatusText,
})

CatchTab:CreateToggle({
    Name = "AUTO CATCH",
    CurrentValue = false,
    Callback = function(value)
        autoCatch = value
        if not value then
            riding = false
            simDone = false
            setCatchStatus("Idle")
        end
    end,
})

CatchTab:CreateDropdown({
    Name = "Rarity Filter (none picked = all)",
    Options = RARITY_ORDER,
    CurrentOption = {},
    MultipleOptions = true,
    Callback = function(options)
        if not options or #options == 0 then
            rarityFilter = nil
        else
            local set = {}
            for _, r in ipairs(options) do
                if RARITY_SET[r] then set[r] = true end
            end
            rarityFilter = next(set) and set or nil
        end
    end,
})

-- v2.8 filter controls: name + mutation multi-picks (option lists grow as
-- new kinds/mutations are seen on live bulls) and a min-weight text box.
local function kindOptions()
    local byLower = {}
    for name in pairs(seenKinds) do
        local low = string.lower(name)
        local cur = byLower[low]
        if not cur or (string.match(name, "^%u") and not string.match(cur, "^%u")) then
            byLower[low] = name
        end
    end
    local out = {}
    for _, name in pairs(byLower) do table.insert(out, name) end
    table.sort(out)
    return out
end

local function mutationOptions()
    local out = {}
    for name in pairs(knownMutations) do table.insert(out, name) end
    table.sort(out)
    return out
end

local function refreshDropdown(dd, options, picks)
    if not dd then return end
    pcall(function()
        if type(dd.Refresh) == "function" then
            dd:Refresh(options)
        else
            dd:Set(options)
        end
    end)
    if picks and #picks > 0 then
        local copy = {}
        for _, p in ipairs(picks) do table.insert(copy, p) end
        pcall(function() dd:Set(copy) end)
    end
end

nameDropdown = CatchTab:CreateDropdown({
    Name = "Name Filter (none picked = all)",
    Options = kindOptions(),
    CurrentOption = {},
    MultipleOptions = true,
    Callback = function(options)
        namePicks = options or {}
        if not options or #options == 0 then
            nameFilter = nil
        else
            local set = {}
            for _, nm in ipairs(options) do
                set[string.lower(nm)] = true
            end
            nameFilter = set
        end
        print("[AutoCatch] name filter: "
            .. (nameFilter and table.concat(namePicks, ", ") or "any"))
    end,
})

mutationDropdown = CatchTab:CreateDropdown({
    Name = "Mutation Filter (none picked = all)",
    Options = mutationOptions(),
    CurrentOption = {},
    MultipleOptions = true,
    Callback = function(options)
        mutationPicks = options or {}
        if not options or #options == 0 then
            mutationFilter = nil
        else
            local set = {}
            for _, nm in ipairs(options) do
                set[string.lower(nm)] = true
            end
            mutationFilter = set
        end
        print("[AutoCatch] mutation filter: "
            .. (mutationFilter and table.concat(mutationPicks, ", ")
                or "any"))
    end,
})

local weightBoxOk = pcall(function()
    CatchTab:CreateInput({
        Name = "Min Weight kg (blank = any)",
        PlaceholderText = "e.g. 1500 or 1.5K",
        RemoveTextAfterFocusLost = false,
        Callback = function(text)
            local v = parseKgText(text)
            if v then
                weightMinKg = v
                print("[AutoCatch] min weight filter: "
                    .. string.format("%.0f", v) .. " kg")
            else
                weightMinKg = nil
                if text and string.gsub(text, "%s", "") ~= "" then
                    print("[AutoCatch] weight '" .. tostring(text)
                        .. "' not understood - filter cleared")
                else
                    print("[AutoCatch] min weight filter cleared")
                end
            end
        end,
    })
end)
if not weightBoxOk then
    print("[TrainerCatch] weight text box unavailable in this build")
end

CatchTab:CreateToggle({
    Name = "Match ANY filter (OR mode)",
    CurrentValue = false,
    Callback = function(v)
        orMode = v
        print("[AutoCatch] filter mode: " .. (v and "OR - any "
            .. "matching filter counts" or "AND - every active "
            .. "filter must match"))
    end,
})

CatchTab:CreateDropdown({
    Name = "Target Priority",
    Options = PRIORITY_MODES,
    CurrentOption = { "Nearest" },
    MultipleOptions = false,
    Callback = function(options)
        priorityMode = (options and options[1]) or "Nearest"
        print("[AutoCatch] target priority: " .. priorityMode)
    end,
})

-- Keep the name/mutation option lists current as new bulls are seen.
task.spawn(function()
    local lastKindSig = table.concat(kindOptions(), "|")
    local lastMutSig = table.concat(mutationOptions(), "|")
    while true do
        task.wait(5)
        local ko = kindOptions()
        local ks = table.concat(ko, "|")
        if ks ~= lastKindSig then
            lastKindSig = ks
            refreshDropdown(nameDropdown, ko, namePicks)
        end
        local mo = mutationOptions()
        local ms = table.concat(mo, "|")
        if ms ~= lastMutSig then
            lastMutSig = ms
            refreshDropdown(mutationDropdown, mo, mutationPicks)
        end
    end
end)

CatchTab:CreateDropdown({
    Name = "Teleport to Zone",
    Options = zoneNames,
    CurrentOption = {},
    MultipleOptions = false,
    Callback = function(options)
        local name = options and options[1]
        if not name then return end
        for i, zn in ipairs(zoneNames) do
            if zn == name then
                teleportToZone(i)
                break
            end
        end
    end,
})

CatchTab:CreateDropdown({
    Name = "Run to Zone",
    Options = zoneNames,
    CurrentOption = {},
    MultipleOptions = false,
    Callback = function(options)
        local name = options and options[1]
        if not name then return end
        for i, zn in ipairs(zoneNames) do
            if zn == name then
                startRunToZone(i)
                break
            end
        end
    end,
})

CatchTab:CreateButton({
    Name = "⏹ Stop Run",
    Callback = function()
        stopRun(false)
    end,
})

CatchTab:CreateParagraph({
    Title = "How it works",
    Content = "AUTO CATCH lassos the nearest wild bull matching your filters "
        .. "(rarity, name, mutation, min weight - a bull must pass them all), "
        .. "then steers the ride with the game's own RideSim; the WASD input "
        .. "mirror keeps the on-screen ride in sync. The console prints full "
        .. "ride telemetry plus a VERDICT line per ride.",
})

-- ---------- Trainer ----------
trainStatusPara = TrainerTab:CreateParagraph({
    Title = "Trainer Status",
    Content = trainStatusText,
})

local tapToggle = TrainerTab:CreateToggle({
    Name = "AUTO TAP",
    CurrentValue = false,
    Callback = function(value)
        autoTap = value
        setTrainStatus(value and "Tapping screen center..." or "Trainer idle")
    end,
})

local reactToggle = TrainerTab:CreateToggle({
    Name = "AUTO REACT",
    CurrentValue = false,
    Callback = function(value)
        autoReact = value
    end,
})

-- ---------- Trainer: AUTO TRAIN ----------
-- Picks the best bull in your pen (highest level, biggest size on a tie),
-- teleports beside it, starts the session through the game's own Train
-- prompt (raw Blink START as fallback), then flips AUTO TAP + AUTO REACT
-- on so the session actually trains.
local TrainingR = RS:FindFirstChild("Training_BLINK_RELIABLE_REMOTE")
if not TrainingR then
    for _, c in ipairs(RS:GetChildren()) do
        if c:IsA("RemoteEvent") and string.find(c.Name, "Training")
            and string.find(c.Name, "RELIABLE") then
            TrainingR = c
            break
        end
    end
end

local autoTrain = false

local RATE_SUFFIX = { K = 1e3, M = 1e6, B = 1e9, T = 1e12 }

-- the bull's own nameplate shows its earnings ("$47.9/s") - read it straight
-- off the tag instead of guessing a formula
parseRate = function(model)
    for _, d in ipairs(model:GetDescendants()) do
        if d:IsA("TextLabel") or d:IsA("TextButton") then
            local num, suf = string.match(d.Text or "", "%$([%d%.,]+)([KMBT]?)/s")
            if num then
                local v = tonumber((string.gsub(num, ",", "")))
                if v then
                    return v * (RATE_SUFFIX[suf] or 1),
                        "$" .. num .. suf .. "/s"
                end
            end
        end
    end
    return nil, nil
end

-- "Best" = most money per second (Daniel's definition). Falls back to the
-- breed's base income from Breeds when a tag can't be read; level, then
-- size, break ties. Prints the whole ranking to the console.
local lastPickSource = nil

local function ranchViewBulls()
    local out = {}
    local rv = workspace:FindFirstChild("RanchView")
    if not rv then return out end
    local mine = rv:FindFirstChild(tostring(Player.UserId))
    if not mine then return out end
    for _, m in ipairs(mine:GetChildren()) do
        if m:IsA("Model") then
            local level = m:GetAttribute("Level")
            local kind = m:GetAttribute("Kind")
            for _, d in ipairs(m:GetDescendants()) do
                if d:IsA("TextLabel") or d:IsA("TextButton") then
                    local txt = d.Text or ""
                    if not level then
                        local lv = string.match(txt, "Lv%s*(%d+)")
                        if lv then level = tonumber(lv) end
                    end
                    if not kind and (seenKinds[txt] or kindRarity[txt]) then
                        kind = txt
                    end
                    if level and kind then break end
                end
            end
            local rate, rateText = parseRate(m)
            table.insert(out, {
                guid = m.Name,
                model = m,
                rate = rate,
                rateText = rateText,
                level = level or 0,
                kind = kind,
            })
        end
    end
    return out
end

local function pickBestPenBull()
    local models = {}
    local bullIdModels = 0
    for _, m in ipairs(workspace:GetDescendants()) do
        if m:IsA("Model") then
            local id = m:GetAttribute("BullId")
            if id then
                bullIdModels = bullIdModels + 1
                if myBullInfo[id] then models[id] = m end
            end
            if not models[m.Name] and myBullInfo[m.Name] then
                models[m.Name] = m
            end
            if not models[id] then
                for attrName, attrVal in pairs(m:GetAttributes()) do
                    if type(attrVal) == "string" and myBullInfo[attrVal] then
                        models[attrVal] = m
                        break
                    end
                end
            end
        end
    end
    local penCount = 0
    for _ in pairs(myBullInfo) do penCount = penCount + 1 end
    local matched = 0
    for _ in pairs(models) do matched = matched + 1 end
    print(("[TrainerCatch][AutoTrain] census: pen bulls known=%d, "
        .. "BullId models in world=%d, pen models matched=%d, "
        .. "state events=%d"):format(
        penCount, bullIdModels, matched, stateEventCount))
    local nonW = {}
    for _, m in ipairs(workspace:GetDescendants()) do
        if m:IsA("Model") and m:GetAttribute("BullId")
            and not string.match(m.Name, "^W%d+$") then
            table.insert(nonW, m.Name .. "|BullId="
                .. tostring(m:GetAttribute("BullId")) .. "|Kind="
                .. tostring(m:GetAttribute("Kind")))
            if #nonW >= 4 then break end
        end
    end
    if #nonW > 0 then
        print("[AutoTrain] non-wild BullId models: "
            .. table.concat(nonW, " ; "))
    end
    local rvBulls = ranchViewBulls()
    if #rvBulls > 0 then
        lastPickSource = "ranchview"
        print(("[TrainerCatch][AutoTrain] RanchView pen bulls: %d")
            :format(#rvBulls))
        local best = nil
        for _, b in ipairs(rvBulls) do
            print(("[TrainerCatch][AutoTrain] pen %s -> %s Lv%d"):format(
                string.sub(b.guid, 1, 8),
                b.rateText or "rate pending", b.level))
            if not best
                or (b.rate or -1) > (best.rate or -1)
                or ((b.rate or -1) == (best.rate or -1)
                    and b.level > best.level) then
                best = b
            end
        end
        return best.guid, { kind = nil, level = best.level, size = nil },
            best.model, best.rateText
    end
    lastPickSource = "state"
    if penCount == 0 then
        -- no State data at all: fall back to pen-looking models already in
        -- the world (BullId models that aren't wild W##### spawns)
        local cGuid, cInfo, cModel, cRate, cRateText =
            nil, nil, nil, nil, nil
        for _, m in ipairs(workspace:GetDescendants()) do
            if m:IsA("Model") and m:GetAttribute("BullId")
                and not string.match(m.Name, "^W%d+$") then
                local kind = m:GetAttribute("Kind")
                local rate, rateText = parseRate(m)
                if not rate and kind and BreedsMod
                    and type(BreedsMod.kind) == "function" then
                    local ok, entry = pcall(BreedsMod.kind, kind)
                    if ok and type(entry) == "table"
                        and type(entry.income) == "number" then
                        rate = entry.income
                        rateText = "base $" .. entry.income .. "/s"
                    end
                end
                print(("[TrainerCatch][AutoTrain] world pen candidate %s "
                    .. "kind=%s -> %s"):format(m.Name, tostring(kind),
                    rateText or "no $/s found"))
                if not cGuid or (rate or -1) > (cRate or -1) then
                    cGuid = m:GetAttribute("BullId")
                    cInfo = {
                        kind = kind,
                        level = m:GetAttribute("Level") or 0,
                        size = nil,
                    }
                    cModel, cRate, cRateText = m, rate, rateText
                end
            end
        end
        if cGuid then
            print("[TrainerCatch][AutoTrain] using world pen candidate "
                .. tostring(cInfo.kind))
            return cGuid, cInfo, cModel, cRateText
        end
    end
    local bestGuid, bestInfo, bestModel, bestRate, bestRateText =
        nil, nil, nil, nil, nil
    for guid, info in pairs(myBullInfo) do
        local model = models[guid]
        local rate, rateText = nil, nil
        if model then rate, rateText = parseRate(model) end
        if not rate and BreedsMod and type(BreedsMod.kind) == "function"
            and info.kind then
            local ok, entry = pcall(BreedsMod.kind, info.kind)
            if ok and type(entry) == "table"
                and type(entry.income) == "number" then
                rate = entry.income
                rateText = "base $" .. entry.income .. "/s"
            end
        end
        print(("[TrainerCatch][AutoTrain] pen bull %s Lv%s size=%.2f -> %s")
            :format(info.kind or "?", tostring(info.level), info.size or 0,
                rateText or "no $/s found"))
        local better = false
        if not bestGuid then
            better = true
        elseif (rate or -1) > (bestRate or -1) then
            better = true
        elseif rate == bestRate then
            if (info.level or 0) > (bestInfo.level or 0) then
                better = true
            elseif info.level == bestInfo.level
                and (info.size or 0) > (bestInfo.size or 0) then
                better = true
            end
        end
        if better then
            bestGuid, bestInfo, bestModel, bestRate, bestRateText =
                guid, info, model, rate, rateText
        end
    end
    return bestGuid, bestInfo, bestModel, bestRateText
end

local function trainingSessionLive()
    local root = findTrainingRoot()
    return root ~= nil and guiChainVisible(root)
end

local function fireTrainStart(guid)
    if not TrainingR then return false end
    callIdCounter = (callIdCounter + 1) % 256
    local b = buffer.create(3 + #guid)
    buffer.writeu8(b, 0, 0)
    buffer.writeu8(b, 1, callIdCounter)
    buffer.writeu8(b, 2, #guid)
    buffer.writestring(b, 3, guid)
    local ok, err = pcall(function() TrainingR:FireServer(b, {}) end)
    print("[TrainerCatch][AutoTrain] START fired guid=" .. guid
        .. " ok=" .. tostring(ok)
        .. (ok and "" or (" err=" .. tostring(err))))
    return ok
end

local trainingAssistOn = false
local engageCancel = false
local engaging = false

-- v2.11 specific pen bull picker: when set, AUTO TRAIN engages this bull
-- instead of the best $/s one.
local penPickGuid = nil

local function findPenModel(guid)
    for _, m in ipairs(workspace:GetDescendants()) do
        if m:IsA("Model") then
            if m:GetAttribute("BullId") == guid or m.Name == guid then
                return m
            end
            for _, v in pairs(m:GetAttributes()) do
                if v == guid then return m end
            end
        end
    end
    return nil
end

local function pickSpecificBull(guid)
    for _, b in ipairs(ranchViewBulls()) do
        if b.guid == guid then
            return guid, { kind = b.kind, level = b.level, size = nil },
                b.model, b.rateText
        end
    end
    local info = myBullInfo[guid]
    if info then
        local m = findPenModel(guid)
        if m then
            local _, rt = parseRate(m)
            return guid, info, m, rt
        end
    end
    return nil
end

local function engageTraining()
    local guid, info, model, rateText
    if penPickGuid then
        guid, info, model, rateText = pickSpecificBull(penPickGuid)
        if not guid then
            setTrainStatus("🏋️ Picked bull not found - is your ranch "
                .. "loaded? (stand near your pen)")
            print("[TrainerCatch][AutoTrain] picked bull "
                .. string.sub(penPickGuid, 1, 8) .. " not found in world")
            return false
        end
        print("[TrainerCatch][AutoTrain] engaging PICKED bull "
            .. string.sub(guid, 1, 8))
    else
        guid, info, model, rateText = pickBestPenBull()
    end
    if not penPickGuid and guid and model
        and lastPickSource == "ranchview" and not rateText then
        local list = ranchViewBulls()
        if #list > 0 then
            local sum = Vector3.zero
            for _, b in ipairs(list) do
                sum = sum + b.model:GetPivot().Position
            end
            local root = hrp()
            if root then
                root.CFrame = CFrame.new(sum / #list + Vector3.new(0, 3, 0))
            end
            print("[TrainerCatch][AutoTrain] at pen - waiting for income "
                .. "tags, then re-picking")
            task.wait(1.4)
            guid, info, model, rateText = pickBestPenBull()
        end
    end
    if not guid then
        setTrainStatus("🏋️ No pen bulls known yet - wait a few seconds")
        return false
    end
    local label = ("%s Lv%s (size %.2f)"):format(
        info.kind or "Bull", tostring(info.level), info.size or 0)
    if rateText then label = label .. " " .. rateText end
    if not model then
        -- the guid-keyed model wasn't found; anchor on a same-kind model
        -- carrying a $/s tag, nearest to you (START still uses the guid)
        local char0 = Player.Character
        local root0 = char0 and char0:FindFirstChild("HumanoidRootPart")
        local anchor, anchorDist = nil, math.huge
        if root0 then
            for _, m in ipairs(workspace:GetDescendants()) do
                if m:IsA("Model") and m:GetAttribute("Kind") == info.kind
                    and parseRate(m) then
                    local d = (m:GetPivot().Position - root0.Position).Magnitude
                    if d < anchorDist then
                        anchor, anchorDist = m, d
                    end
                end
            end
        end
        if anchor then
            model = anchor
            print("[TrainerCatch][AutoTrain] anchor: guid model missing, "
                .. "using nearest " .. tostring(info.kind) .. " model ("
                .. math.floor(anchorDist) .. "m)")
        else
            setTrainStatus("🏋️ Best bull (" .. label
                .. ") not loaded in world")
            print("[TrainerCatch][AutoTrain] no anchor model for "
                .. tostring(info.kind) .. " - cannot go to the bull")
            return false
        end
    end
    local pos = model:GetPivot().Position
    -- v2.17: prompt helpers - the Train prompt only works within
    -- PromptDistance (8 studs), so anchor beside the prompt itself.
    local function promptWorldPos(prompt)
        local par = prompt.Parent
        if par then
            if par:IsA("Attachment") then return par.WorldPosition end
            if par:IsA("BasePart") then return par.Position end
        end
        return nil
    end
    local function findTrainPrompt()
        for _, d in ipairs(model:GetDescendants()) do
            if d:IsA("ProximityPrompt") then return d end
        end
        local prompt, bestD = nil, 12
        for _, d in ipairs(workspace:GetDescendants()) do
            if d:IsA("ProximityPrompt") and d.Parent
                and d.Parent:IsA("BasePart") then
                local dist = (d.Parent.Position - pos).Magnitude
                if dist < bestD then bestD, prompt = dist, d end
            end
        end
        return prompt
    end
    local live = false
    local prompted = false
    for attempt = 1, 3 do
        if engageCancel then break end
        local char = Player.Character
        local rootPart = char and char:FindFirstChild("HumanoidRootPart")
        local prompt = fireproximityprompt and findTrainPrompt() or nil
        local anchor = (prompt and promptWorldPos(prompt)) or pos
        if rootPart and anchor then
            rootPart.CFrame = CFrame.new(anchor + Vector3.new(5, 2, 0))
        end
        setTrainStatus("🏋️ Going to best bull: " .. label)
        task.wait(0.6)
        -- range check: player must be within 8 of the prompt, else
        -- the server refuses TooFar; step in closer and re-check.
        if rootPart and anchor then
            local d = (rootPart.Position - anchor).Magnitude
            if d > 8 then
                rootPart.CFrame = CFrame.new(anchor + Vector3.new(2, 2, 0))
                task.wait(0.5)
            end
        end
        prompted = false
        if prompt then
            local ok = pcall(function() fireproximityprompt(prompt) end)
            prompted = ok
            print("[TrainerCatch][AutoTrain] Train prompt fired ok="
                .. tostring(ok) .. " attempt=" .. attempt)
        end
        if not prompted then
            fireTrainStart(guid)
        end
        for _ = 1, 6 do
            task.wait(0.5)
            if trainingSessionLive() then live = true break end
        end
        if not live and prompted then
            fireTrainStart(guid)
            for _ = 1, 6 do
                task.wait(0.5)
                if trainingSessionLive() then live = true break end
            end
        end
        if live then break end
        print("[TrainerCatch][AutoTrain] engage attempt " .. attempt
            .. " did not start - retrying")
        task.wait(1)
    end
    if live and not engageCancel then
        trainingAssistOn = true
        if tapToggle then pcall(function() tapToggle:Set(true) end) end
        if reactToggle then pcall(function() reactToggle:Set(true) end) end
        setTrainStatus("🏋️ Training " .. label)
        return true
    end
    engageCancel = false
    if not live then
        print("[TrainerCatch][AutoTrain] session did not start (prompt="
            .. tostring(prompted) .. ") - staying at the bull")
        setTrainStatus("🏋️ At best bull (" .. label
            .. ") - session didn't start")
    end
    return false
end

local function disengageTraining()
    if engaging then engageCancel = true end
    if not trainingAssistOn then return end
    trainingAssistOn = false
    if tapToggle then pcall(function() tapToggle:Set(false) end) end
    if reactToggle then pcall(function() reactToggle:Set(false) end) end
    setTrainStatus("Trainer idle")
end

-- engage request for the AUTO TRAIN toggle
local function requestEngage()
    if trainingAssistOn or engaging then return end
    engaging = true
    task.spawn(function()
        engageTraining()
        engaging = false
    end)
end

local trainToggle
trainToggle = TrainerTab:CreateToggle({
    Name = "AUTO TRAIN",
    CurrentValue = false,
    Callback = function(value)
        autoTrain = value
        if value then
            requestEngage()
        else
            disengageTraining()
        end
    end,
})

-- Pen Bull picker: "[Best $/s (auto)]" keeps the classic behavior; picking
-- a bull pins AUTO TRAIN to it. The list follows your pen (RanchView +
-- State-known bulls) and refreshes as bulls come and go.
do
    -- Idle Train Cycle (v2.16): Daniel's order - train when idle,
    -- and when a bull hits the catch list: stop the trio, run to
    -- the start position FIRST (catch loop paused via cycleStaging
    -- while staging), then catch. After the bull is caught, trio
    -- back ON - AUTO TRAIN teleports beside the pen bull, which is
    -- the return to plot to train. New target -> cycle repeats.
    -- The cycle toggle itself is the master switch: it pauses
    -- training on any target whether AUTO CATCH is on (auto catch)
    -- or off (you catch manually while training stays paused).
    -- It only flips the trio on transitions, so a manual trio change
    -- sticks until the next transition; turn the cycle off to take
    -- full manual control back.
    local START_POS = Vector3.new(-1.03, 0.5, 6.07)
    local cycleOn = false
    local cycleMode = "train" -- "train" | "stage" | "catch"
    local trioOn = nil
    local function setTrio(on)
        if trioOn == on then return end
        trioOn = on
        pcall(function() trainToggle:Set(on) end)
        pcall(function() tapToggle:Set(on) end)
        pcall(function() reactToggle:Set(on) end)
        print("[IdleCycle] training trio " .. (on and "ON" or "OFF"))
    end
    -- v2.18: instant spawn trigger. The 1s supervisor poll was the
    -- only spawn watch, so a selected bull could sit up to a second
    -- (plus a full workspace scan) before training paused. Now a new
    -- wild bull model pauses training immediately, at any distance -
    -- findTarget already sweeps the whole workspace, so range was
    -- never the limit. The 1s poll stays as backup for bulls whose
    -- attributes arrive late.
    workspace.DescendantAdded:Connect(function(inst)
        if not cycleOn or cycleMode ~= "train" then return end
        if not inst:IsA("Model") then return end
        local id = inst:GetAttribute("BullId")
        if type(id) ~= "string" then return end
        if myBulls[id] then return end
        if inst:GetAttribute("Rider") ~= nil then return end
        local exp = blacklist[id]
        if exp and exp > os.clock() then return end
        -- attributes may populate just after the model appears
        task.delay(0.2, function()
            if not cycleOn or cycleMode ~= "train" then return end
            local target = nil
            pcall(function() target = findTarget() end)
            if target then
                cycleMode = "stage"
                setTrio(false)
                cycleStaging = true
                print("[IdleCycle] spawn detected ("
                    .. tostring(target.kind)
                    .. ") - training stopped instantly")
            end
        end)
    end)
    TrainerTab:CreateToggle({
        Name = "AUTO TRAIN WHEN IDLE",
        CurrentValue = false,
        Callback = function(v)
            cycleOn = v
            if not v then cycleStaging = false end
            print("[IdleCycle] " .. (v and "ON" or "OFF"))
            if not v then return end
            cycleMode = "train"
            trioOn = nil
            task.spawn(function()
                while cycleOn do
                        local target = nil
                        pcall(function() target = findTarget() end)
                        if cycleMode == "train" and target then
                            cycleMode = "stage"
                            setTrio(false)
                            cycleStaging = true
                            print("[IdleCycle] training stopped - "
                                .. "running to start before catch")
                        elseif cycleMode == "stage" then
                            if not target then
                                cycleStaging = false
                                cycleMode = "train"
                                setTrio(true)
                                print("[IdleCycle] target gone while "
                                    .. "staging - back to training")
                            else
                                local char = Player.Character
                                local root = char and char:FindFirstChild(
                                    "HumanoidRootPart")
                                local hum = char and char
                                    :FindFirstChildOfClass("Humanoid")
                                if root and hum then
                                    local dx = START_POS.X
                                        - root.Position.X
                                    local dz = START_POS.Z
                                        - root.Position.Z
                                    if math.sqrt(dx * dx + dz * dz) <= 8 then
                                        cycleStaging = false
                                        cycleMode = "catch"
                                        print("[IdleCycle] at start - "
                                            .. "catching")
                                    else
                                        pcall(function()
                                            hum:MoveTo(START_POS)
                                        end)
                                    end
                                end
                            end
                        elseif cycleMode == "catch" and not target then
                            cycleMode = "train"
                            setTrio(true)
                            print("[IdleCycle] bull caught - back to "
                                .. "plot to train")
                        elseif cycleMode == "train" and not target then
                            setTrio(true)
                        end
                    task.wait(1)
                end
            end)
        end,
    })
end

local PEN_AUTO_LABEL = "[Best $/s (auto)]"
local penPickLabel = PEN_AUTO_LABEL
local penLabelToGuid = {}
local penDropdown

local function penBullLabel(kind, level, rateText, guid)
    return string.format("%s Lv%s%s #%s", kind or "Bull",
        tostring(level or "?"), rateText and (" " .. rateText) or "",
        string.sub(guid, 1, 8))
end

local function buildPenOptions()
    penLabelToGuid = {}
    local out = { PEN_AUTO_LABEL }
    local seen = {}
    for _, b in ipairs(ranchViewBulls()) do
        seen[b.guid] = true
        local label = penBullLabel(b.kind, b.level, b.rateText, b.guid)
        penLabelToGuid[label] = b.guid
        table.insert(out, label)
    end
    for guid, info in pairs(myBullInfo) do
        if not seen[guid] then
            local label = penBullLabel(info.kind, info.level, nil, guid)
            penLabelToGuid[label] = guid
            table.insert(out, label)
        end
    end
    return out
end

penDropdown = TrainerTab:CreateDropdown({
    Name = "Pen Bull (train target)",
    Options = buildPenOptions(),
    CurrentOption = { PEN_AUTO_LABEL },
    MultipleOptions = false,
    Callback = function(options)
        local label = options and options[1]
        if not label or label == PEN_AUTO_LABEL then
            penPickGuid = nil
            penPickLabel = PEN_AUTO_LABEL
            print("[TrainerCatch][AutoTrain] pen target: best $/s (auto)")
        else
            penPickGuid = penLabelToGuid[label]
            penPickLabel = label
            print("[TrainerCatch][AutoTrain] pen target: " .. label)
        end
        if autoTrain then
            disengageTraining()
            requestEngage()
        end
    end,
})

task.spawn(function()
    local lastSig = table.concat(buildPenOptions(), "|")
    while true do
        task.wait(5)
        local options = buildPenOptions()
        local sig = table.concat(options, "|")
        if sig ~= lastSig then
            lastSig = sig
            -- labels carry level/rate, which change as the bull trains;
            -- follow the pick by GUID, not by label text
            if penPickGuid then
                local foundLabel = nil
                for label, g in pairs(penLabelToGuid) do
                    if g == penPickGuid then
                        foundLabel = label
                        break
                    end
                end
                if foundLabel then
                    penPickLabel = foundLabel
                else
                    penPickGuid = nil
                    penPickLabel = PEN_AUTO_LABEL
                    print("[TrainerCatch][AutoTrain] picked bull left "
                        .. "the pen - back to best $/s (auto)")
                end
            end
            refreshDropdown(penDropdown, options, { penPickLabel })
        end
    end
end)

-- ---------- Player: WalkSpeed ----------
local speedOn, speedValue = false, 16

PlayerTab:CreateToggle({
    Name = "WalkSpeed",
    CurrentValue = false,
    Callback = function(value)
        speedOn = value
        if not value then
            local char = Player.Character
            local hum = char and char:FindFirstChildOfClass("Humanoid")
            if hum then hum.WalkSpeed = 16 end
        end
    end,
})

PlayerTab:CreateSlider({
    Name = "Walk Speed",
    Range = { 0, 500 },
    Increment = 1,
    Suffix = " studs",
    CurrentValue = 16,
    Callback = function(value)
        speedValue = value
    end,
})

-- the game keeps resetting WalkSpeed, so pin it every frame while ON
RunService.Heartbeat:Connect(function()
    if not speedOn then return end
    local char = Player.Character
    local hum = char and char:FindFirstChildOfClass("Humanoid")
    if hum and hum.WalkSpeed ~= speedValue then
        hum.WalkSpeed = speedValue
    end
end)

-- ---------- Player: Noclip ----------
local noclipOn = false
local noclipParts = {}

PlayerTab:CreateToggle({
    Name = "Noclip",
    CurrentValue = false,
    Callback = function(value)
        noclipOn = value
        if not value then
            for part, was in pairs(noclipParts) do
                if part and part.Parent then part.CanCollide = was end
            end
            table.clear(noclipParts)
        end
    end,
})

RunService.Stepped:Connect(function()
    if not noclipOn then return end
    local char = Player.Character
    if not char then return end
    for _, part in ipairs(char:GetDescendants()) do
        if part:IsA("BasePart") then
            if noclipParts[part] == nil then
                noclipParts[part] = part.CanCollide
            end
            part.CanCollide = false
        end
    end
end)

-- ---------- Player: Instant Proximity Prompt ----------
local instantProxOn = false
local proxOriginals = {}
local proxConn = nil

local function fixPrompt(prompt)
    if prompt:IsA("ProximityPrompt") then
        if proxOriginals[prompt] == nil then
            proxOriginals[prompt] = prompt.HoldDuration
        end
        if instantProxOn then prompt.HoldDuration = 0 end
    end
end

PlayerTab:CreateToggle({
    Name = "Instant Proximity Prompt",
    CurrentValue = false,
    Callback = function(value)
        instantProxOn = value
        if value then
            for _, d in ipairs(workspace:GetDescendants()) do
                fixPrompt(d)
            end
            if not proxConn then
                proxConn = workspace.DescendantAdded:Connect(fixPrompt)
            end
        else
            if proxConn then
                proxConn:Disconnect()
                proxConn = nil
            end
            for prompt, dur in pairs(proxOriginals) do
                if prompt and prompt.Parent then
                    prompt.HoldDuration = dur
                end
            end
            table.clear(proxOriginals)
        end
    end,
})

-- ---------- Player: Infinite Jump + Anti-AFK (v2.19) ----------
local infJumpOn = false

PlayerTab:CreateToggle({
    Name = "Infinite Jump",
    CurrentValue = false,
    Callback = function(value)
        infJumpOn = value
    end,
})

UserInputService.JumpRequest:Connect(function()
    if not infJumpOn then return end
    local char = Player.Character
    local hum = char and char:FindFirstChildOfClass("Humanoid")
    if hum then hum:ChangeState(Enum.HumanoidStateType.Jumping) end
end)

local antiAfkOn = false

PlayerTab:CreateToggle({
    Name = "Anti-AFK",
    CurrentValue = false,
    Callback = function(value)
        antiAfkOn = value
    end,
})

Player.Idled:Connect(function()
    if not antiAfkOn then return end
    pcall(function()
        local vu = game:GetService("VirtualUser")
        vu:CaptureController()
        vu:ClickButton2(Vector2.new(0, 0))
    end)
end)

--------------------------------------------------------------------------------
-- ESP tab (v2.19): wild bulls only (not owned, not ridden). Filters AND:
-- variant + rarity + min weight; a dropdown on All / a blank weight box
-- means that filter is ignored. Weight unknown + a threshold set = hidden
-- (can't confirm it's above the line).
--------------------------------------------------------------------------------
-- EspTab created up top with Catch/Trainer/Player (v2.20)
local espOn = false
local espVariant = "All" -- All | Normal | Gold | Diamond
local espRarity = "All" -- All | a rarity from RARITY_ORDER
local espMinKg = nil -- number, nil = any weight
local espGuis = {} -- bull model -> BillboardGui

-- Variant: explicit Variant attribute first, then Gold/Diamond tokens in
-- mutation/trait attributes, then the model name, then nameplate labels.
-- Anything else is Normal.
local function variantOfModel(model)
    for name, value in pairs(model:GetAttributes()) do
        local ln = string.lower(name)
        if type(value) == "string" and string.find(ln, "variant") then
            local v = string.lower(value)
            if string.find(v, "diamond") then return "Diamond" end
            if string.find(v, "gold") then return "Gold" end
            return "Normal"
        end
        if type(value) == "boolean" and value then
            if ln == "gold" or ln == "isgold" then return "Gold" end
            if ln == "diamond" or ln == "isdiamond" then return "Diamond" end
        end
    end
    local muts = mutationsOfModel(model)
    if muts["diamond"] then return "Diamond" end
    if muts["gold"] then return "Gold" end
    local mn = string.lower(model.Name)
    if string.find(mn, "diamond") then return "Diamond" end
    if string.find(mn, "gold") then return "Gold" end
    for _, d in ipairs(model:GetDescendants()) do
        if (d:IsA("TextLabel") or d:IsA("TextButton")) and d.Text then
            local t = string.lower(d.Text)
            if string.find(t, "diamond") then return "Diamond" end
            if string.find(t, "gold") then return "Gold" end
        end
    end
    return "Normal"
end

local function formatKg(kg)
    if kg == nil then return "?" end
    local units = { { 1e12, "T" }, { 1e9, "B" }, { 1e6, "M" }, { 1e3, "K" } }
    for _, u in ipairs(units) do
        if kg >= u[1] then
            local s = string.format("%.1f", kg / u[1])
            s = string.gsub(s, "%.0$", "")
            return s .. u[2]
        end
    end
    return string.format("%.0f", kg)
end

local RARITY_COLOR = {
    Common = Color3.fromRGB(255, 255, 255),
    Uncommon = Color3.fromRGB(95, 255, 95),
    Rare = Color3.fromRGB(85, 170, 255),
    Epic = Color3.fromRGB(200, 85, 255),
    Legendary = Color3.fromRGB(255, 170, 0),
    Mythic = Color3.fromRGB(255, 85, 170),
    Secret = Color3.fromRGB(255, 255, 0),
    Godly = Color3.fromRGB(255, 0, 0),
}

local function espPartFor(model)
    if model.PrimaryPart and model.PrimaryPart:IsA("BasePart") then
        return model.PrimaryPart
    end
    local hrp = model:FindFirstChild("HumanoidRootPart")
    if hrp and hrp:IsA("BasePart") then return hrp end
    for _, d in ipairs(model:GetDescendants()) do
        if d:IsA("BasePart") then return d end
    end
    return nil
end

local function makeEspGui(model, text, color)
    local part = espPartFor(model)
    if not part then return nil end
    local gui = Instance.new("BillboardGui")
    gui.Name = "BullESP"
    gui.AlwaysOnTop = true
    gui.Size = UDim2.new(0, 220, 0, 56)
    gui.StudsOffset = Vector3.new(0, 5, 0)
    gui.LightInfluence = 0
    local label = Instance.new("TextLabel")
    label.Name = "Label"
    label.BackgroundTransparency = 1
    label.Size = UDim2.new(1, 0, 1, 0)
    label.Font = Enum.Font.GothamBold
    label.TextSize = 16
    label.TextColor3 = color
    label.TextStrokeTransparency = 0.2
    label.TextStrokeColor3 = Color3.new(0, 0, 0)
    label.Text = text
    label.Parent = gui
    gui.Parent = part
    return gui
end

local function refreshEsp()
    if not espOn then return end
    local seen = {}
    for _, d in ipairs(workspace:GetDescendants()) do
        if d:IsA("Model") then
            local id = d:GetAttribute("BullId")
            if type(id) == "string" and not myBulls[id]
                and d:GetAttribute("Rider") == nil then
                local variant = variantOfModel(d)
                local rar = rarityOfModel(d, id)
                local w = weightOfModel(d)
                local ok = (espVariant == "All" or variant == espVariant)
                    and (espRarity == "All" or rar == espRarity)
                    and (espMinKg == nil or (w ~= nil and w >= espMinKg))
                if ok then
                    seen[d] = true
                    local line1 = (variant ~= "Normal"
                        and variant .. " " or "")
                        .. (rar and (rar .. " ") or "")
                        .. (kindOfModel(d, id) or "Bull")
                    local text = line1
                    if w ~= nil then
                        text = text .. "\n" .. formatKg(w) .. " kg"
                    end
                    local color = (rar and RARITY_COLOR[rar])
                        or Color3.fromRGB(255, 255, 255)
                    local gui = espGuis[d]
                    if not gui or gui.Parent == nil then
                        espGuis[d] = makeEspGui(d, text, color)
                    else
                        local label = gui:FindFirstChild("Label")
                        if label then
                            if label.Text ~= text then label.Text = text end
                            if label.TextColor3 ~= color then
                                label.TextColor3 = color
                            end
                        end
                    end
                end
            end
        end
    end
    for model, gui in pairs(espGuis) do
        if not seen[model] then
            if gui then pcall(function() gui:Destroy() end) end
            espGuis[model] = nil
        end
    end
end

task.spawn(function()
    while true do
        if espOn then pcall(refreshEsp) end
        task.wait(0.5)
    end
end)

local function firstOption(options)
    if type(options) == "string" then return options end
    if type(options) == "table" then return options[1] end
    return nil
end

EspTab:CreateToggle({
    Name = "ESP",
    CurrentValue = false,
    Callback = function(value)
        espOn = value
        if not value then
            for _, gui in pairs(espGuis) do
                if gui then pcall(function() gui:Destroy() end) end
            end
            table.clear(espGuis)
        end
    end,
})

EspTab:CreateDropdown({
    Name = "Variant",
    Options = { "All", "Normal", "Gold", "Diamond" },
    CurrentOption = { "All" },
    MultipleOptions = false,
    Callback = function(options)
        espVariant = firstOption(options) or "All"
    end,
})

local espRarityOptions = { "All" }
for _, r in ipairs(RARITY_ORDER) do
    table.insert(espRarityOptions, r)
end

EspTab:CreateDropdown({
    Name = "Rarity",
    Options = espRarityOptions,
    CurrentOption = { "All" },
    MultipleOptions = false,
    Callback = function(options)
        espRarity = firstOption(options) or "All"
    end,
})

EspTab:CreateInput({
    Name = "Min Weight kg (blank = any)",
    PlaceholderText = "e.g. 1500 or 1.5K",
    RemoveTextAfterFocusLost = false,
    Callback = function(text)
        local v = parseKgText(text)
        if v then
            espMinKg = v
        else
            espMinKg = nil
        end
    end,
})

print("[TrainerCatch] v2.20 loaded" .. (RideSim and "" or " (RideSim MISSING)"))
