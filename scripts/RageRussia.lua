script_version("25.05.2026-1")
script_name("Rage Russia BP")
script_author("mofbe")
script_description("https://www.blast.hk/threads/254680/")

require "lib.moonloader"

local bit                             = require "bit"
local sampev                          = require 'samp.events'
local raknet                          = require 'samp.raknet'
local imgui                           = require 'mimgui'
local encoding                        = require 'encoding'
local vkeys                           = require 'vkeys'
encoding.default                      = 'CP1251'
local u8                              = encoding.UTF8

local AUTH_PASSWORD                   = '123123'

local band, bor, bxor, bnot           = bit.band, bit.bor, bit.bxor, bit.bnot
local rshift, lshift, rol, ror, tobit = bit.rshift, bit.lshift, bit.rol, bit.ror, bit.tobit

local CHECK_SALT_A                    = "Weqtkgdm"
local CHECK_SALT_B                    = "Papeqwkgm"
local ANSWER_SALT_A                   = "Nokmcfqh"
local ANSWER_SALT_B                   = "Jormecva"
local EXPECTED_CHECK                  = "69974ae340db814ab7a2990a742a05dcfbe4cb732d91351ea16cb36ff4bb5279"

local EC610_XOR100                    = 0x8c
local EC674                           = {
    0xff, 0x25, 0x34, 0x39, 0x4d,
    0x00, 0x90, 0x90, 0x90, 0x90,
    0x56, 0x57, 0x50, 0x8b, 0x44,
    0x24, 0x14, 0x8d, 0x0c, 0x80,
}

local K256                            = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
    0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
    0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
    0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
    0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
}

local function treu8(v)
    return v < 0 and v + 256 or v
end

local function cstr(s)
    local pos = s:find("\0", 1, true)
    if pos then
        return s:sub(1, pos - 1)
    end
    return s
end

local function u32be(s, i)
    local a, b, c, d = s:byte(i, i + 3)
    return bor(lshift(a, 24), lshift(b, 16), lshift(c, 8), d)
end

local function len64be(byte_len)
    local bits_hi = math.floor(byte_len / 0x20000000)
    local bits_lo = (byte_len * 8) % 0x100000000
    return string.char(
        band(rshift(bits_hi, 24), 0xff),
        band(rshift(bits_hi, 16), 0xff),
        band(rshift(bits_hi, 8), 0xff),
        band(bits_hi, 0xff),
        band(rshift(bits_lo, 24), 0xff),
        band(rshift(bits_lo, 16), 0xff),
        band(rshift(bits_lo, 8), 0xff),
        band(bits_lo, 0xff)
    )
end

local function hex_lower_byte(x)
    return string.format("%02x", band(x, 0xff))
end

local function hex_upper_byte(x)
    return string.format("%02X", band(x, 0xff))
end

local function sha256_hex(msg)
    local h = {
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
        0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
    }
    local original_len = #msg
    msg = msg .. "\128" .. string.rep("\0", (55 - original_len) % 64) .. len64be(original_len)

    local w = {}
    for chunk = 1, #msg, 64 do
        for i = 0, 15 do
            w[i] = u32be(msg, chunk + i * 4)
        end
        for i = 16, 63 do
            local s0 = bxor(ror(w[i - 15], 7), ror(w[i - 15], 18), rshift(w[i - 15], 3))
            local s1 = bxor(ror(w[i - 2], 17), ror(w[i - 2], 19), rshift(w[i - 2], 10))
            w[i] = tobit(w[i - 16] + s0 + w[i - 7] + s1)
        end

        local a, b, c, d = h[1], h[2], h[3], h[4]
        local e, f, g, hh = h[5], h[6], h[7], h[8]
        for i = 0, 63 do
            local s1 = bxor(ror(e, 6), ror(e, 11), ror(e, 25))
            local ch = bxor(band(e, f), band(bnot(e), g))
            local t1 = tobit(hh + s1 + ch + K256[i + 1] + w[i])
            local s0 = bxor(ror(a, 2), ror(a, 13), ror(a, 22))
            local maj = bxor(band(a, b), band(a, c), band(b, c))
            local t2 = tobit(s0 + maj)
            hh, g, f, e = g, f, e, tobit(d + t1)
            d, c, b, a = c, b, a, tobit(t1 + t2)
        end

        h[1] = tobit(h[1] + a)
        h[2] = tobit(h[2] + b)
        h[3] = tobit(h[3] + c)
        h[4] = tobit(h[4] + d)
        h[5] = tobit(h[5] + e)
        h[6] = tobit(h[6] + f)
        h[7] = tobit(h[7] + g)
        h[8] = tobit(h[8] + hh)
    end

    local out = {}
    for i = 1, 8 do
        local x = h[i]
        out[#out + 1] = hex_lower_byte(rshift(x, 24))
        out[#out + 1] = hex_lower_byte(rshift(x, 16))
        out[#out + 1] = hex_lower_byte(rshift(x, 8))
        out[#out + 1] = hex_lower_byte(x)
    end
    return table.concat(out)
end

local function sha1_words(msg)
    local h0, h1, h2, h3, h4 = 0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0
    local original_len = #msg
    msg = msg .. "\128" .. string.rep("\0", (55 - original_len) % 64) .. len64be(original_len)

    local w = {}
    for chunk = 1, #msg, 64 do
        for i = 0, 15 do
            w[i] = u32be(msg, chunk + i * 4)
        end
        for i = 16, 79 do
            w[i] = rol(bxor(w[i - 3], w[i - 8], w[i - 14], w[i - 16]), 1)
        end

        local a, b, c, d, e = h0, h1, h2, h3, h4
        for i = 0, 79 do
            local f, k
            if i < 20 then
                f = bor(band(b, c), band(bnot(b), d))
                k = 0x5a827999
            elseif i < 40 then
                f = bxor(b, c, d)
                k = 0x6ed9eba1
            elseif i < 60 then
                f = bor(band(b, c), band(b, d), band(c, d))
                k = 0x8f1bbcdc
            else
                f = bxor(b, c, d)
                k = 0xca62c1d6
            end
            local temp = tobit(rol(a, 5) + f + e + k + w[i])
            e, d, c, b, a = d, c, rol(b, 30), a, temp
        end

        h0 = tobit(h0 + a)
        h1 = tobit(h1 + b)
        h2 = tobit(h2 + c)
        h3 = tobit(h3 + d)
        h4 = tobit(h4 + e)
    end

    return h0, h1, h2, h3, h4
end

local function transform_first_key(s)
    local words = { sha1_words(cstr(s)) }
    local out = {}
    for wi = 1, 5 do
        local x = words[wi]
        for shift = 0, 24, 8 do
            local b = bxor(band(rshift(x, shift), 0xff), EC610_XOR100, EC674[#out + 1])
            out[#out + 1] = hex_upper_byte(b)
        end
    end
    return table.concat(out)
end

local function log(text)
    print(text)
    sampAddChatMessage('[{D1D5D8}Rage{FF0000}Russia{FFFFFF}BP]: ' .. tostring(text), -1)
end

function onSendPacket(id, bs)
    if id == 12 then
        return false
    end
end

local RPC_BLOCK = {
    [raknet.RPC.SETOBJECTMATERIAL]       = true,
    [raknet.RPC.ATTACHOBJECTTOPLAYER]    = true,
    [raknet.RPC.SETPLAYERATTACHEDOBJECT] = true,
    [raknet.RPC.SETOBJECTMATERIAL]       = true,
    [raknet.RPC.REMOVEVEHICLECOMPONENT]  = true,
    [raknet.RPC.SCMEVENT]                = true,
    [raknet.RPC.SETVEHICLETIRES]         = true,
}

local function emulateFullSetSpawnInfo(team, skin, x, y, z, rot)
    local out = raknetNewBitStream()
    local SPAWN_UNK = 16

    raknetBitStreamWriteInt8(out, team)
    raknetBitStreamWriteInt32(out, skin)
    raknetBitStreamWriteInt8(out, SPAWN_UNK)

    raknetBitStreamWriteFloat(out, x)
    raknetBitStreamWriteFloat(out, y)
    raknetBitStreamWriteFloat(out, z)
    raknetBitStreamWriteFloat(out, rot)

    -- weapons
    raknetBitStreamWriteInt32(out, 0)
    raknetBitStreamWriteInt32(out, 0)
    raknetBitStreamWriteInt32(out, 0)

    -- ammo
    raknetBitStreamWriteInt32(out, 0)
    raknetBitStreamWriteInt32(out, 0)
    raknetBitStreamWriteInt32(out, 0)

    raknetEmulRpcReceiveBitStream(raknet.RPC.SETSPAWNINFO, out)

    raknetDeleteBitStream(out)
end

local showInteractHint = false

function onReceiveRpc(id, bs)
    if id == raknet.RPC.SETSPAWNINFO then
        if raknetBitStreamGetNumberOfBytesUsed(bs) == 21 then
            local team = treu8(raknetBitStreamReadInt8(bs))
            local skin = raknetBitStreamReadInt32(bs)

            local x = raknetBitStreamReadFloat(bs)
            local y = raknetBitStreamReadFloat(bs)
            local z = raknetBitStreamReadFloat(bs)
            local rot = raknetBitStreamReadFloat(bs)

            emulateFullSetSpawnInfo(team, skin, x, y, z, rot + 0.42)
        end
        return false
    elseif id == raknet.RPC.WORLDVEHICLEADD then
        local data = { modSlots = {} }
        local vehicleId = raknetBitStreamReadInt16(bs)
        data.type = raknetBitStreamReadInt32(bs)
        if data.type < 400 or data.type > 611 then
            data.type = 411
        end
        data.position = {
            x = raknetBitStreamReadFloat(bs),
            y = raknetBitStreamReadFloat(bs),
            z = raknetBitStreamReadFloat(bs)
        }
        data.rotation = raknetBitStreamReadFloat(bs)
        data.interiorColor1 = raknetBitStreamReadInt8(bs)
        data.interiorColor2 = raknetBitStreamReadInt8(bs)
        data.health = raknetBitStreamReadFloat(bs)
        data.interior = 0
        for i = 1, 14 do
            data.modSlots[i] = 0
        end
        data.paintJob = 255
        data.bodyColor1 = data.interiorColor1
        data.bodyColor2 = data.interiorColor2

        local fixed = raknetNewBitStream()
        raknetBitStreamWriteInt16(fixed, vehicleId)
        raknetBitStreamWriteInt32(fixed, data.type)
        raknetBitStreamWriteFloat(fixed, data.position.x)
        raknetBitStreamWriteFloat(fixed, data.position.y)
        raknetBitStreamWriteFloat(fixed, data.position.z)
        raknetBitStreamWriteFloat(fixed, data.rotation)
        raknetBitStreamWriteInt8(fixed, data.interiorColor1)
        raknetBitStreamWriteInt8(fixed, data.interiorColor2)
        raknetBitStreamWriteFloat(fixed, data.health)
        raknetBitStreamWriteInt8(fixed, data.interior)
        raknetBitStreamWriteInt32(fixed, data.doorDamageStatus or 0)
        raknetBitStreamWriteInt32(fixed, data.panelDamageStatus or 0)
        raknetBitStreamWriteInt8(fixed, data.lightDamageStatus or 0)
        raknetBitStreamWriteInt8(fixed, data.tireDamageStatus or 0)
        raknetBitStreamWriteInt8(fixed, data.addSiren or 0)
        for i = 1, 14 do
            raknetBitStreamWriteInt8(fixed, data.modSlots and data.modSlots[i] or 0)
        end
        raknetBitStreamWriteInt8(fixed, data.paintJob or 255)
        raknetBitStreamWriteInt32(fixed, data.bodyColor1 or 0)
        raknetBitStreamWriteInt32(fixed, data.bodyColor2 or 0)

        raknetEmulRpcReceiveBitStream(id, fixed)
        return false
    elseif id == 246 then
        local typeRpc = raknetBitStreamReadInt8(bs)
        if typeRpc == 2 then
            showInteractHint = raknetBitStreamReadInt8(bs) == 1
        end
        return false
    elseif RPC_BLOCK[id] then
        return false
    end
end

local function parseNotifyJson(str)
    local text = str:match('"i"%s*:%s*"(.-)"')
    local ntype = tonumber(str:match('"t"%s*:%s*(-?%d+)')) or 3
    local duration = tonumber(str:match('"d"%s*:%s*(%d+)')) or 3
    local sVal = tonumber(str:match('"s"%s*:%s*(-?%d+)'))
    return text, ntype, duration, sVal
end

local maleSkinIds = { 78, 79, 134, 136, 230, 158, 159, 71, 161 }

local packet238_key = nil

local function xor_with_key(data, key)
    local out = {}

    for i = 1, #data do
        local a = data:byte(i)
        local b = key:byte(((i - 1) % #key) + 1)
        out[i] = string.char(bit.bxor(a, b))
    end

    return table.concat(out)
end

Protection = Protection or {
    verified = false,
    sessionMagic = 0,
    sessionChallenge = 0,
    lastStageTime = 0
}

Protection220 = Protection220 or {}

local function u16(x)
    return bit.band(x, 0xFFFF)
end

local function u31(x)
    return bit.band(x, 0x7FFFFFFF)
end

local function u32(x)
    return bit.band(x, 0xFFFFFFFF)
end

local function mul32(a, b)
    local ah = bit.rshift(a, 16)
    local al = bit.band(a, 0xFFFF)
    local bh = bit.rshift(b, 16)
    local bl = bit.band(b, 0xFFFF)

    local low = al * bl
    local mid = ah * bl + al * bh

    return u32(low + bit.lshift(bit.band(mid, 0xFFFF), 16))
end

function Protection220.calcKey(sessionMagic, sessionChallenge)
    local source = { 0x37, 0x42, 0x51, 0x4C, 0x15, 0x06 }

    local hash = 0x811C9DC5
    local prime = 0x01000193

    for i = 1, #source do
        local b = bit.bxor(source[i], 0x55)

        hash = bit.bxor(hash, b)
        hash = mul32(hash, prime)
        hash = u31(hash)
    end

    local key = bit.bxor(u16(sessionMagic), hash)
    key = bit.bxor(key, sessionChallenge)
    key = u31(key)

    if key == 0 then
        key = 0x5A5A5A5A
    end

    return key
end

function Protection220.crypt(payload, key)
    local out = {}

    for i = 1, #payload do
        local a = bit.bxor(key, bit.band(bit.lshift(key, 13), 0x7FFFE000))
        local b = bit.bxor(a, bit.rshift(a, 17))
        local c = bit.bxor(b, bit.band(bit.lshift(b, 5), 0x7FFFFFE0))

        key = u31(c)

        out[i] = string.char(
            bit.band(bit.bxor(payload:byte(i), bit.band(key, 0xFF)), 0xFF)
        )
    end

    return table.concat(out)
end

function Protection220.calcCrc(payload)
    local crc = 0

    for i = 1, #payload do
        crc = u16(bit.bxor(u16(crc * 2), payload:byte(i)))
    end

    return crc
end

function Protection220.appendCheck(payload)
    local crc = Protection220.calcCrc(payload)
    local check = bit.bxor(u16(Protection.sessionMagic), crc)

    return payload .. string.char(
        bit.band(check, 0xFF),
        bit.band(bit.rshift(check, 8), 0xFF)
    )
end

function Protection220.protectPayloadWithCheck(rawPayload)
    local key = Protection220.calcKey(
        Protection.sessionMagic,
        Protection.sessionChallenge
    )

    local payload = Protection220.appendCheck(rawPayload)
    return Protection220.crypt(payload, key)
end

function Protection220.protectPayloadNoCheck(rawPayload)
    local key = Protection220.calcKey(
        Protection.sessionMagic,
        Protection.sessionChallenge
    )

    return Protection220.crypt(rawPayload, key)
end

function Protection220.sendStage1()
    local s = '016.65.13333'
    local len = #s
    local t = bit.band(os.time(), 0xFFFFFFFF)

    local sum = 0
    for i = 1, len do
        sum = bit.band(sum + s:byte(i), 0xFFFF)
    end

    local hiword = bit.rshift(t, 16)
    local check = bit.band(t + hiword + sum, 0xFFFF)

    local raw = string.char(len) .. s .. string.char(
        bit.band(t, 0xFF),
        bit.band(bit.rshift(t, 8), 0xFF),
        bit.band(bit.rshift(t, 16), 0xFF),
        bit.band(bit.rshift(t, 24), 0xFF),
        bit.band(check, 0xFF),
        bit.band(bit.rshift(check, 8), 0xFF)
    )

    local payload = Protection220.protectPayloadNoCheck(raw)

    local bs = raknetNewBitStream()

    raknetBitStreamWriteInt8(bs, 220)
    raknetBitStreamWriteInt16(bs, Protection.sessionMagic)
    raknetBitStreamWriteInt32(bs, 1)
    raknetBitStreamWriteInt32(bs, #payload)
    raknetBitStreamWriteString(bs, payload)

    raknetSendBitStreamEx(bs, 1, 9, 0)
    raknetDeleteBitStream(bs)

    Protection.lastStageTime = os.time()

    print(string.format('[220] send stage1 len=%d', #payload))
    return true
end

function Protection220.sendStage3(nonce)
    local bs = raknetNewBitStream()

    raknetBitStreamWriteInt8(bs, 220)
    raknetBitStreamWriteInt16(bs, Protection.sessionMagic)
    raknetBitStreamWriteInt32(bs, 3)
    raknetBitStreamWriteInt32(bs, nonce)

    raknetSendBitStreamEx(bs, 1, 9, 0)
    raknetDeleteBitStream(bs)

    Protection.lastStageTime = os.time()

    print(string.format('[220] send stage3 nonce=0x%08X', nonce))
    return true
end

function Protection220.sendCmd(cmd, rawPayload)
    if not Protection.verified then
        print('[220] sendCmd failed: not verified')
        return false
    end

    if Protection.sessionMagic == 0 then
        print('[220] sendCmd failed: sessionMagic is zero')
        return false
    end

    local payload = Protection220.protectPayloadWithCheck(rawPayload or '')

    local bs = raknetNewBitStream()

    raknetBitStreamWriteInt8(bs, 220)
    raknetBitStreamWriteInt16(bs, Protection.sessionMagic)
    raknetBitStreamWriteInt32(bs, 4)
    raknetBitStreamWriteInt8(bs, bit.band(cmd, 0xFF))
    raknetBitStreamWriteInt32(bs, #payload)
    raknetBitStreamWriteString(bs, payload)

    raknetSendBitStreamEx(bs, 1, 9, 0)
    raknetDeleteBitStream(bs)

    return true
end

function Protection220.sendJsonData(xui, jsonStr)
    if #jsonStr > 255 then
        print('[220] json too long: ' .. #jsonStr)
        return false
    end

    local rawPayload = string.char(#jsonStr) .. jsonStr

    return Protection220.sendCmd(bit.band(xui, 0xFF), rawPayload)
end

function onReceivePacket(id, bs)
    if id == 12 then
        raknetBitStreamIgnoreBits(bs, 8)

        local first_key = cstr(raknetBitStreamReadString(bs, treu8(raknetBitStreamReadInt8(bs))))
        local second_key = cstr(raknetBitStreamReadString(bs, treu8(raknetBitStreamReadInt8(bs))))
        local third_key = cstr(raknetBitStreamReadString(bs, treu8(raknetBitStreamReadInt8(bs))))

        packet238_key = cstr(raknetBitStreamReadString(bs, treu8(raknetBitStreamReadInt8(bs))))

        if sha256_hex(CHECK_SALT_A .. cstr(second_key) .. CHECK_SALT_B) ~= EXPECTED_CHECK then
            log("bad second key: " .. second_key)
            return false
        end

        local answer1 = transform_first_key(first_key)
        local answer2 = sha256_hex(ANSWER_SALT_A .. cstr(third_key) .. ANSWER_SALT_B)

        local out = raknetNewBitStream()
        raknetBitStreamWriteInt8(out, id)
        raknetBitStreamWriteInt8(out, #answer1)
        raknetBitStreamWriteString(out, answer1)
        raknetBitStreamWriteInt8(out, #answer2)
        raknetBitStreamWriteString(out, answer2)
        raknetSendBitStreamEx(out, 0, 8, 0)
        raknetDeleteBitStream(out)
        return true
    elseif id == 252 then
        raknetBitStreamIgnoreBits(bs, 8)
        local _type = raknetBitStreamReadInt16(bs)
        local jsonStr = raknetBitStreamReadString(bs, raknetBitStreamReadInt32(bs))
        local json = decodeJson(jsonStr)
        print("[" .. id .. "]: " .. _type .. "~" .. jsonStr)
        if _type == 38 then
            if json.o == 1 then
                if json.r == 0 then
                    lua_thread.create(function()
                        wait(3210)
                        sendJsonData(_type, string.format('{\"t\":1,\"s\":\"\",\"p\":\"%s\"}', AUTH_PASSWORD))
                        wait(200)
                        sendJsonData(_type, "{\"t\":2,\"s\":\"\",\"r\":0}")
                        wait(200)
                        sendJsonData(_type, "{\"t\":4,\"s\":\"\"}")
                        wait(200)
                        sendJsonData(_type, "{\"t\":3,\"r\":0}")
                        wait(200)
                        sendJsonData(_type, string.format('{\"t\":5,\"r\":%i}', maleSkinIds[math.random(#maleSkinIds)]))
                        wait(210)
                        sendJsonData(_type, "{\"c\":1}")
                        log("reg()")
                    end)
                else
                    lua_thread.create(function()
                        wait(3210)
                        sendJsonData(_type, string.format('{\"t\":6,\"s\":\"%s\",\"r\":0}', AUTH_PASSWORD))
                        wait(210)
                        sendJsonData(_type, "{\"c\":1}")
                        log("auth()")
                    end)
                end
            end
        elseif _type == 50 then
            --{"m":[1,2],"o":1}
            if json.o == 1 then
                sendJsonData(_type, "{\"t\":1}")
                log("Send select spawn 1")
            end
        elseif _type == 13 then
            local text, ntype, duration, sVal = parseNotifyJson(jsonStr)

            if text then
                addNotify(text, ntype, duration, sVal)
            end
        elseif _type == 31 then
            local clear = jsonStr:gsub("%s+", "")

            -- {"g":1,"o":1,...}
            if clear:find('"g":1', 1, true) and clear:find('"o":1', 1, true) then
                sendJsonData(_type, '{"t":1}')
            end

            -- {"g":2,"o":1}
            if clear:find('"g":2', 1, true) and clear:find('"o":1', 1, true) then
                sendJsonData(_type, '{"s":1}')
            end
        end
        --return false
    elseif id == 238 then
        raknetBitStreamIgnoreBits(bs, 8)

        local word_1AE27E = raknetBitStreamReadInt16(bs)

        local flag = raknetBitStreamReadInt32(bs)

        if flag == 0 and packet238_key and #packet238_key > 0 then
            local raw_body = string.char(#packet238_key) .. packet238_key
            local encrypted_body = xor_with_key(raw_body, "ragerussia228")

            local out = raknetNewBitStream()

            raknetBitStreamWriteInt8(out, id)

            raknetBitStreamWriteInt16(out, word_1AE27E)

            raknetBitStreamWriteString(out, encrypted_body)

            raknetSendBitStreamEx(out, 1, 9, 0)
            raknetDeleteBitStream(out)

            log("packet 238 answer sent")
        end
    elseif id == 220 then
        raknetBitStreamIgnoreBits(bs, 8)

        local magic = raknetBitStreamReadInt16(bs)
        local stage = raknetBitStreamReadInt32(bs)

        if Protection.sessionMagic ~= 0 and magic ~= Protection.sessionMagic then
            print(string.format(
                '[220] bad magic: got=0x%04X expected=0x%04X',
                magic,
                Protection.sessionMagic
            ))
            return false
        end

        if stage == 0 then
            local challenge = raknetBitStreamReadInt32(bs)

            Protection.sessionMagic = magic
            Protection.sessionChallenge = challenge
            Protection.verified = true

            print(string.format(
                '[220] stage0 magic=0x%04X challenge=0x%08X',
                magic,
                challenge
            ))

            Protection220.sendStage1()
            return false
        end

        if stage == 2 then
            local nonce = raknetBitStreamReadInt32(bs)

            print(string.format(
                '[220] stage2 nonce=0x%08X',
                nonce
            ))

            Protection220.sendStage3(nonce)
            return false
        end

        print(string.format('[220] unknown stage=%d', stage))
        return false
    end
end

function onSendPacket(id, bs)
    if id == 12 then
        return false
    elseif id == 207 then
        raknetBitStreamWriteString(bs, "\xFF\x00") -- ну это шобы наручников не было
        return { id, bs }
    end
end

function sendJsonData(xui, str)
    return Protection220.sendJsonData(xui, str)
end

function sendRpc243(value, state)
    local bs = raknetNewBitStream()

    raknetBitStreamWriteInt32(bs, value)
    raknetBitStreamWriteInt8(bs, state)

    raknetSendRpcEx(243, bs, 1, 8, 0, false)
    raknetDeleteBitStream(bs)
end

function sampev.onSendSpawn()
    sendRpc243(0x11, 1)
    sendRpc243(0x10, 1)
    sendRpc243(0x17, 0)
    sendRpc243(0x1A, 0)
    sendRpc243(0x18, 0)
    sendRpc243(0x1C, 0)
end

function sampev.onSendRequestClass(classId)
    return { 1 }
end

function sampev.onSendClientJoin(version, mod, nickname, challengeResponse, joinAuthKey, clientVer, challengeResponse2)
    return { version, mod, nickname, challengeResponse, "15121F6F18550C00AC4B4F8A167D0379BB0ACA99043", clientVer,
        challengeResponse2 }
end

function sampev.onSendPlayerSync(data)
    data.animationId = 0
    data.animationFlags = 0
    return data
end

local notifications = {}

local function now()
    return os.clock()
end

local function sendNotifyClick(sVal, buttonClick)
    local t = buttonClick and 0 or 1
    sendJsonData(13, string.format('{"c":13,"t":%d,"s":%d,"b":0}', t, sVal))
end

function addNotify(text, ntype, duration, sVal)
    table.insert(notifications, {
        text = text,
        type = ntype or 3,
        start = now(),
        duration = duration or 3,
        s = sVal,
        clickable = sVal ~= nil and sVal >= 0,
        clicked = false
    })

    while #notifications > 4 do
        table.remove(notifications, 1)
    end
end

-- Цвета по типу уведомления
local NOTIFY_COLORS = {
    [0] = { 0.40, 0.78, 0.45 }, -- деньги — зелёный
    [1] = { 0.30, 0.65, 1.00 }, -- инфо — голубой
    [2] = { 1.00, 0.72, 0.20 }, -- предупреждение — жёлтый
    [3] = { 0.65, 0.67, 0.72 }, -- системное/нейтральное — серый
    [4] = { 0.55, 0.45, 1.00 }, -- действие/предложение — фиолетовый
}
local DEFAULT_COLOR = { 0.65, 0.67, 0.72 }

local function getAccent(n)
    local c = NOTIFY_COLORS[n.type] or DEFAULT_COLOR
    return c[1], c[2], c[3]
end

local notifyFrame = imgui.OnFrame(
    function()
        return #notifications > 0
    end,
    function()
        local draw = imgui.GetBackgroundDrawList()
        local screen = imgui.GetIO().DisplaySize
        local time = os.clock()

        local width = math.min(560, screen.x - 40)
        local height = 54
        local x = (screen.x - width) / 2
        local baseY = screen.y - 150

        for i = #notifications, 1, -1 do
            local n = notifications[i]
            local elapsed = time - n.start
            local progress = 1.0 - elapsed / n.duration

            if n.clickable and not n.clicked and wasKeyPressed(vkeys.VK_Y) then
                local inputBlocked = sampIsChatInputActive() or sampIsDialogActive()

                if not inputBlocked then
                    n.clicked = true
                    sendNotifyClick(n.s, true)
                    table.remove(notifications, i)
                end
            elseif progress <= 0 then
                table.remove(notifications, i)
            else
                -- smoothstep fade
                local alpha = 1.0
                if elapsed < 0.22 then
                    local t = elapsed / 0.22
                    alpha = t * t * (3 - 2 * t)
                elseif progress < 0.22 then
                    local t = progress / 0.22
                    alpha = t * t * (3 - 2 * t)
                end

                local slideOffset = (elapsed < 0.22) and ((1 - alpha) * 12) or 0
                local y           = baseY - (#notifications - i) * (height + 10) + slideOffset

                local aR, aG, aB  = getAccent(n)

                local bgCol       = imgui.GetColorU32Vec4(imgui.ImVec4(0.06, 0.07, 0.09, 0.92 * alpha))
                local borderCol   = imgui.GetColorU32Vec4(imgui.ImVec4(1, 1, 1, 0.06 * alpha))
                local textCol     = imgui.GetColorU32Vec4(imgui.ImVec4(0.96, 0.97, 1.0, alpha))
                local accentCol   = imgui.GetColorU32Vec4(imgui.ImVec4(aR, aG, aB, alpha))
                local trackCol    = imgui.GetColorU32Vec4(imgui.ImVec4(1, 1, 1, 0.06 * alpha))

                -- мягкая тень
                for s = 1, 6 do
                    draw:AddRectFilled(
                        imgui.ImVec2(x - s * 0.5, y + s),
                        imgui.ImVec2(x + width + s * 0.5, y + height + s),
                        imgui.GetColorU32Vec4(imgui.ImVec4(0, 0, 0, (0.06 - s * 0.008) * alpha)),
                        10
                    )
                end

                -- фон
                draw:AddRectFilled(
                    imgui.ImVec2(x, y),
                    imgui.ImVec2(x + width, y + height),
                    bgCol, 10
                )

                -- верхний highlight
                draw:AddRectFilled(
                    imgui.ImVec2(x + 1, y + 1),
                    imgui.ImVec2(x + width - 1, y + 2),
                    imgui.GetColorU32Vec4(imgui.ImVec4(1, 1, 1, 0.05 * alpha)),
                    9
                )

                -- рамка
                draw:AddRect(
                    imgui.ImVec2(x, y),
                    imgui.ImVec2(x + width, y + height),
                    borderCol, 10, nil, 1.0
                )

                -- акцентная полоска слева
                draw:AddRectFilled(
                    imgui.ImVec2(x, y + 10),
                    imgui.ImVec2(x + 3, y + height - 10),
                    accentCol, 2
                )

                -- текст по центру вертикали
                local text = u8(n.text)
                local textSize = imgui.CalcTextSize(text)
                local textX = x + 22
                local textY = y + (height - textSize.y) / 2 - 1

                -- если кнопки нет — центрируем по горизонтали
                if not n.clickable and textSize.x < (width - 44) then
                    textX = x + (width - textSize.x) / 2
                end

                draw:AddText(imgui.ImVec2(textX, textY), textCol, text)

                if n.clickable then
                    local keyW, keyH = 36, 24
                    local keyX = x + width - 110
                    local keyY = y + (height - keyH) / 2

                    -- glow
                    draw:AddRectFilled(
                        imgui.ImVec2(keyX - 1, keyY - 1),
                        imgui.ImVec2(keyX + keyW + 1, keyY + keyH + 1),
                        imgui.GetColorU32Vec4(imgui.ImVec4(aR, aG, aB, 0.18 * alpha)),
                        6
                    )
                    -- кнопка
                    draw:AddRectFilled(
                        imgui.ImVec2(keyX, keyY),
                        imgui.ImVec2(keyX + keyW, keyY + keyH),
                        imgui.GetColorU32Vec4(imgui.ImVec4(aR, aG, aB, 0.95 * alpha)),
                        5
                    )
                    -- блик
                    draw:AddRectFilled(
                        imgui.ImVec2(keyX + 1, keyY + 1),
                        imgui.ImVec2(keyX + keyW - 1, keyY + keyH / 2),
                        imgui.GetColorU32Vec4(imgui.ImVec4(1, 1, 1, 0.10 * alpha)),
                        4
                    )

                    local keySize = imgui.CalcTextSize("ALT")
                    draw:AddText(
                        imgui.ImVec2(keyX + (keyW - keySize.x) / 2, keyY + (keyH - keySize.y) / 2),
                        imgui.GetColorU32Vec4(imgui.ImVec4(1, 1, 1, alpha)),
                        "ALT"
                    )

                    local lblSize = imgui.CalcTextSize("Принять")
                    draw:AddText(
                        imgui.ImVec2(keyX + keyW + 10, keyY + (keyH - lblSize.y) / 2),
                        textCol,
                        "Принять"
                    )
                end

                -- тонкий прогресс-бар встроен в низ
                local barX = x + 1
                local barY = y + height - 3
                local barW = width - 2
                local barH = 2

                draw:AddRectFilled(
                    imgui.ImVec2(barX, barY),
                    imgui.ImVec2(barX + barW, barY + barH),
                    trackCol, 1
                )

                local fillW = barW * progress
                draw:AddRectFilled(
                    imgui.ImVec2(barX, barY),
                    imgui.ImVec2(barX + fillW, barY + barH),
                    accentCol, 1
                )

                if fillW > 4 then
                    draw:AddRectFilled(
                        imgui.ImVec2(barX + fillW - 4, barY - 1),
                        imgui.ImVec2(barX + fillW + 1, barY + barH + 1),
                        imgui.GetColorU32Vec4(imgui.ImVec4(aR, aG, aB, 0.5 * alpha)),
                        1
                    )
                end
            end
        end
    end
)

notifyFrame.HideCursor = true

-- состояние для плавности
local altHintAlpha = 0

local altFrame = imgui.OnFrame(
    function()
        return showInteractHint or altHintAlpha > 0.01
    end,
    function()
        local draw = imgui.GetBackgroundDrawList()
        local screen = imgui.GetIO().DisplaySize
        local time = os.clock()

        -- плавный fade in/out
        local target = showInteractHint and 1.0 or 0.0
        altHintAlpha = altHintAlpha + (target - altHintAlpha) * 0.18
        if altHintAlpha < 0.01 and not showInteractHint then
            altHintAlpha = 0
            return
        end

        -- smoothstep для красивой кривой
        local a = altHintAlpha
        a = a * a * (3 - 2 * a)

        local text = "Нажмите"
        local key = "ALT"
        local tail = "для взаимодействия"

        local padX = 16
        local h = 40
        local keyW = 48
        local gap = 10

        local textSize = imgui.CalcTextSize(text)
        local tailSize = imgui.CalcTextSize(tail)

        local totalW = padX * 2 + textSize.x + gap + keyW + gap + tailSize.x
        local x = screen.x - totalW - 30
        local y = screen.y / 2

        -- акцентный красный для активного состояния
        local ACCENT_R, ACCENT_G, ACCENT_B = 1.0, 0.28, 0.32

        local altInteract = isKeyDown(vkeys.VK_MENU)

        -- лёгкая пульсация когда ALT зажат
        local pulse = 1.0
        if altInteract then
            pulse = 0.85 + math.sin(time * 6.0) * 0.15
        end

        local bgCol     = imgui.GetColorU32Vec4(imgui.ImVec4(0.06, 0.07, 0.09, 0.92 * a))
        local borderCol = imgui.GetColorU32Vec4(imgui.ImVec4(1, 1, 1, 0.06 * a))
        local textCol   = imgui.GetColorU32Vec4(imgui.ImVec4(0.96, 0.97, 1.0, a))
        local dimCol    = imgui.GetColorU32Vec4(imgui.ImVec4(0.78, 0.80, 0.84, a))

        -- тень
        for s = 1, 5 do
            draw:AddRectFilled(
                imgui.ImVec2(x - s * 0.5, y + s),
                imgui.ImVec2(x + totalW + s * 0.5, y + h + s),
                imgui.GetColorU32Vec4(imgui.ImVec4(0, 0, 0, (0.06 - s * 0.01) * a)),
                9
            )
        end

        -- фон
        draw:AddRectFilled(
            imgui.ImVec2(x, y),
            imgui.ImVec2(x + totalW, y + h),
            bgCol, 9
        )

        -- верхний highlight
        draw:AddRectFilled(
            imgui.ImVec2(x + 1, y + 1),
            imgui.ImVec2(x + totalW - 1, y + 2),
            imgui.GetColorU32Vec4(imgui.ImVec4(1, 1, 1, 0.05 * a)),
            8
        )

        -- рамка
        draw:AddRect(
            imgui.ImVec2(x, y),
            imgui.ImVec2(x + totalW, y + h),
            borderCol, 9, nil, 1.0
        )

        -- акцентная полоска слева (серая → красная при зажатии)
        local stripR, stripG, stripB
        if altInteract then
            stripR, stripG, stripB = ACCENT_R, ACCENT_G, ACCENT_B
        else
            stripR, stripG, stripB = 0.45, 0.47, 0.52
        end
        draw:AddRectFilled(
            imgui.ImVec2(x, y + 8),
            imgui.ImVec2(x + 3, y + h - 8),
            imgui.GetColorU32Vec4(imgui.ImVec4(stripR, stripG, stripB, a * pulse)),
            2
        )

        local cy = y + (h - textSize.y) / 2
        local cx = x + padX

        -- "Нажмите"
        draw:AddText(imgui.ImVec2(cx, cy), dimCol, text)
        cx = cx + textSize.x + gap

        -- кнопка ALT
        local keyH = 24
        local keyY = y + (h - keyH) / 2

        if altInteract then
            -- активная: красная с glow и бликом
            draw:AddRectFilled(
                imgui.ImVec2(cx - 1, keyY - 1),
                imgui.ImVec2(cx + keyW + 1, keyY + keyH + 1),
                imgui.GetColorU32Vec4(imgui.ImVec4(ACCENT_R, ACCENT_G, ACCENT_B, 0.25 * a * pulse)),
                6
            )
            draw:AddRectFilled(
                imgui.ImVec2(cx, keyY),
                imgui.ImVec2(cx + keyW, keyY + keyH),
                imgui.GetColorU32Vec4(imgui.ImVec4(ACCENT_R, ACCENT_G, ACCENT_B, 0.95 * a)),
                5
            )
            draw:AddRectFilled(
                imgui.ImVec2(cx + 1, keyY + 1),
                imgui.ImVec2(cx + keyW - 1, keyY + keyH / 2),
                imgui.GetColorU32Vec4(imgui.ImVec4(1, 1, 1, 0.12 * a)),
                4
            )
        else
            -- неактивная: тёмная с тонкой рамкой как клавиша
            draw:AddRectFilled(
                imgui.ImVec2(cx, keyY),
                imgui.ImVec2(cx + keyW, keyY + keyH),
                imgui.GetColorU32Vec4(imgui.ImVec4(0.12, 0.13, 0.16, 0.95 * a)),
                5
            )
            draw:AddRect(
                imgui.ImVec2(cx, keyY),
                imgui.ImVec2(cx + keyW, keyY + keyH),
                imgui.GetColorU32Vec4(imgui.ImVec4(1, 1, 1, 0.12 * a)),
                5, nil, 1.0
            )
            -- лёгкий блик сверху
            draw:AddRectFilled(
                imgui.ImVec2(cx + 1, keyY + 1),
                imgui.ImVec2(cx + keyW - 1, keyY + keyH / 2),
                imgui.GetColorU32Vec4(imgui.ImVec4(1, 1, 1, 0.04 * a)),
                4
            )
        end

        local keySize = imgui.CalcTextSize(key)
        local keyTextCol = altInteract
            and imgui.GetColorU32Vec4(imgui.ImVec4(1, 1, 1, a))
            or imgui.GetColorU32Vec4(imgui.ImVec4(0.92, 0.94, 0.98, a))
        draw:AddText(
            imgui.ImVec2(cx + (keyW - keySize.x) / 2, keyY + (keyH - keySize.y) / 2),
            keyTextCol,
            key
        )

        cx = cx + keyW + gap

        draw:AddText(imgui.ImVec2(cx, cy), textCol, tail)
    end
)

altFrame.HideCursor = true

function sampev.onVehicleStreamIn(id, data)
    if data.type < 410 or data.type > 611 then
        data.type = 451
        data.interiorId = 0
        return { id, data }
    end
end

function sendRpc243_12()
    local bs = raknetNewBitStream()

    raknetBitStreamWriteInt32(bs, 0x12)

    raknetSendRpcEx(243, bs, 1, 8, 0, false)
    raknetDeleteBitStream(bs)
end

local AutoUpdater = {}
AutoUpdater.__index = AutoUpdater
local dlstatus = require('moonloader').download_status

function AutoUpdater:new(config)
    local skrrrrrrrr = thisScript()
    local obj = {
        ptrScrrrr = skrrrrrrrr,
        scriptName = config.scriptName or skrrrrrrrr.name,
        scriptVersion = config.scriptVersion or skrrrrrrrr.version,
        manifestUrl = config.manifestUrl,

        silent = false,

        manifestPath = getWorkingDirectory() .. "\\update_manifest.tmp",
        updatePath = skrrrrrrrr.path .. ".update",
        backupPath = skrrrrrrrr.path .. ".backup",

        remoteInfo = nil,
        checking = false,
        downloading = false
    }

    setmetatable(obj, self)
    return obj
end

function AutoUpdater:msg(text)
    log(u8:decode(text))
end

function AutoUpdater:readFile(path)
    local file = io.open(path, "rb")
    if not file then
        return nil
    end

    local data = file:read("*a")
    file:close()

    return data
end

function AutoUpdater:deleteFile(path)
    if path then
        os.remove(path)
    end
end

function AutoUpdater:clearTempFiles()
    self:deleteFile(self.manifestPath)
    self:deleteFile(self.updatePath)
end

function AutoUpdater:isNewVersion(remoteVersion)
    if not remoteVersion or remoteVersion == "" then
        return false
    end

    return tostring(remoteVersion) ~= tostring(self.scriptVersion)
end

function AutoUpdater:getManifestUrl()
    local separator = self.manifestUrl:find("?", 1, true) and "&" or "?"
    return self.manifestUrl .. separator .. "t=" .. os.time()
end

function AutoUpdater:getDownloadUrl()
    if not self.remoteInfo or not self.remoteInfo.url then
        return nil
    end

    local url = self.remoteInfo.url
    local separator = url:find("?", 1, true) and "&" or "?"

    return url .. separator .. "t=" .. os.time()
end

function AutoUpdater:parseManifest(data)
    local ok, decoded = pcall(decodeJson, data)

    if not ok or type(decoded) ~= "table" then
        return nil, "manifest json decode error"
    end

    if type(decoded.scripts) ~= "table" then
        return nil, "manifest does not contain scripts"
    end

    local info = decoded.scripts[self.scriptName]

    if type(info) ~= "table" then
        return nil, "script not found in manifest: " .. tostring(self.scriptName)
    end

    if not info.version or not info.url then
        return nil, "script info does not contain version or url"
    end

    return info, nil
end

function AutoUpdater:validateDownloadedScript(data)
    if not data or #data < 50 then
        return false, "файл пустой или слишком маленький"
    end

    if not data:find("script_name", 1, true) and not data:find("script_version", 1, true) then
        return false, "файл не похож на MoonLoader Lua-скрипт"
    end

    return true, nil
end

function AutoUpdater:replaceScript()
    self:deleteFile(self.backupPath)

    local currentPath = self.skrrrrrrrr.path

    local backupOk = os.rename(currentPath, self.backupPath)

    if not backupOk then
        return false, "не удалось создать backup"
    end

    local replaceOk = os.rename(self.updatePath, currentPath)

    if not replaceOk then
        os.rename(self.backupPath, currentPath)
        return false, "не удалось заменить текущий файл"
    end

    return true, nil
end

function AutoUpdater:download()
    if self.downloading then
        self:msg("Обновление уже скачивается.")
        return
    end

    if not self.remoteInfo then
        self:msg("Сначала проверь обновление командой /bpcheck.")
        return
    end

    if not self:isNewVersion(self.remoteInfo.version) then
        self:msg("У тебя уже актуальная версия.")
        return
    end

    local url = self:getDownloadUrl()

    if not url then
        self:msg("В manifest нет ссылки на обновление.")
        return
    end

    self.downloading = true
    self:deleteFile(self.updatePath)

    self:msg("Скачиваю обновление...")

    downloadUrlToFile(url, self.updatePath, function(id, status)
        if status == dlstatus.STATUS_ENDDOWNLOADDATA then
            self.downloading = false

            local data = self:readFile(self.updatePath)
            local valid, err = self:validateDownloadedScript(data)

            if not valid then
                self:deleteFile(self.updatePath)
                self:msg("Ошибка обновления: " .. tostring(err))
                return
            end

            local ok, replaceErr = self:replaceScript()

            if not ok then
                self:deleteFile(self.updatePath)
                self:msg("Ошибка замены файла: " .. tostring(replaceErr))
                return
            end

            self:msg("Обновление установлено. Перезагружаю скрипт...")

            lua_thread.create(function()
                wait(1000)
                self.skrrrrrrrr:reload()
            end)
        elseif status == dlstatus.STATUS_ERROR then
            self.downloading = false
            self:deleteFile(self.updatePath)
            self:msg("Ошибка загрузки файла обновления.")
        end
    end)
end

function AutoUpdater:checkAndDownload()
    if self.checking or self.downloading then
        self:msg("Проверка или загрузка уже выполняется.")
        return
    end

    self.checking = true
    self.remoteInfo = nil

    self:deleteFile(self.manifestPath)
    self:msg("Проверяю обновление...")

    downloadUrlToFile(self:getManifestUrl(), self.manifestPath, function(id, status)
        if status == dlstatus.STATUS_ENDDOWNLOADDATA then
            self.checking = false

            local data = self:readFile(self.manifestPath)
            self:deleteFile(self.manifestPath)

            if not data or #data == 0 then
                self:msg("Не удалось прочитать manifest.json.")
                return
            end

            local info, err = self:parseManifest(data)

            if not info then
                self:msg("Неверный manifest.json: " .. tostring(err))
                return
            end

            self.remoteInfo = info

            if self:isNewVersion(info.version) then
                self:msg("Найдена новая версия: " .. tostring(info.version))
                self:download()
            else
                self:msg("Обновлений нет. Версия: " .. tostring(self.scriptVersion))
            end
        elseif status == dlstatus.STATUS_ERROR then
            self.checking = false
            self:deleteFile(self.manifestPath)
            self:msg("Ошибка загрузки manifest.json.")
        end
    end)
end

local updater = AutoUpdater:new({
    manifestUrl = "https://raw.githubusercontent.com/MrZalupkin/lua_update/main/manifest.json"
})

function main()
    math.randomseed(os.time())

    repeat wait(100) until isSampAvailable()

    updater:checkAndDownload()

    repeat
        wait(220)
    until not updater.checking and not updater.downloading

    local skrrrrrrrr = thisScript()
    log(u8:decode(string.format("Обход на {ff0000}рэг{ffffff} рашу загружен. Автор: {613dff}%s{ffffff}. %s", skrrrrrrrr.authors[0], skrrrrrrrr.description)))

    while true do
        wait(0)

        local inputBlocked = sampIsChatInputActive() or sampIsDialogActive()

        if not inputBlocked then
            if wasKeyPressed(vkeys.VK_MENU) and showInteractHint then
                sendRpc243_12()
            end
        end
    end
end
