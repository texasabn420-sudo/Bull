-- Tame a Bull - Trainer + Auto Catch v2.11 (combined, Rayfield Gen 2 GUI)
-- The Auto Catch system below, plus the Bull Trainer at the bottom:
--   AUTO TAP   : center-of-screen taps every 0.10s (VIM mouse events)
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
-- minimum weight in kg from a text box. All optional; a bull must pass
-- every active filter (same rule as the rarity filter).
local nameFilter = nil -- set of lowercased kind names, nil = any name
local mutationFilter = nil -- set of lowercased mutation names, nil = any
local weightMinKg = nil -- number, nil = any weight
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
                    local pass = true
                    if rarityFilter ~= nil
                        and not (rar and rarityFilter[rar]) then
                        if rar then lastSkippedRarity = rar end
                        filterStats.rarity = filterStats.rarity + 1
                        pass = false
                    elseif nameFilter ~= nil
                        and not (kind and nameFilter[string.lower(kind)])
                    then
                        filterStats.name = filterStats.name + 1
                        pass = false
                    elseif mutationFilter ~= nil then
                        local anyMut = false
                        for m in pairs(muts) do
                            if mutationFilter[m] then
                                anyMut = true
                                break
                            end
                        end
                        if not anyMut then
                            filterStats.mutation = filterStats.mutation + 1
                            pass = false
                        end
                    end
                    local weight = nil
                    if pass and weightMinKg ~= nil then
                        weight = weightOfModel(d)
                        if not weight then
                            filterStats.weightUnknown =
                                filterStats.weightUnknown + 1
                            pass = false
                        elseif weight < weightMinKg then
                            filterStats.weight = filterStats.weight + 1
                            pass = false
                        end
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
        if autoCatch and not riding and RideSim then
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

-- AUTO TAP: center-of-screen tap every 0.10s while ON (the Clicker's token
-- bucket accepts 8/s sustained, so 10/s offered keeps it saturated)
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
            task.wait(0.10)
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
                if pressesThisBubble == 0
                    or (pressesThisBubble < 4 and now - lastPressAt >= 0.4) then
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

local Rayfield = loadstring(game:HttpGet("https://sirius.menu/rayfield"))()

local Window = Rayfield:CreateWindow({
    Name = "🐂 Trainer + Catch v2.11",
    LoadingTitle = "Trainer + Catch v2.11",
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
    local char = Player.Character
    local rootPart = char and char:FindFirstChild("HumanoidRootPart")
    if rootPart then
        rootPart.CFrame = CFrame.new(pos + Vector3.new(5, 2, 0))
    end
    setTrainStatus("🏋️ Going to best bull: " .. label)
    task.wait(0.6)
    -- preferred: the game's own Train prompt on/near the bull
    local prompted = false
    if fireproximityprompt then
        local prompt = nil
        for _, d in ipairs(model:GetDescendants()) do
            if d:IsA("ProximityPrompt") then
                prompt = d
                break
            end
        end
        if not prompt then
            local bestD = 12
            for _, d in ipairs(workspace:GetDescendants()) do
                if d:IsA("ProximityPrompt") and d.Parent
                    and d.Parent:IsA("BasePart") then
                    local dist = (d.Parent.Position - pos).Magnitude
                    if dist < bestD then
                        bestD = dist
                        prompt = d
                    end
                end
            end
        end
        if prompt then
            local ok = pcall(function() fireproximityprompt(prompt) end)
            prompted = ok
            print("[TrainerCatch][AutoTrain] Train prompt fired ok="
                .. tostring(ok))
        end
    end
    if not prompted then
        fireTrainStart(guid)
    end
    local live = false
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

TrainerTab:CreateToggle({
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

print("[TrainerCatch] v2.11 loaded" .. (RideSim and "" or " (RideSim MISSING)"))
