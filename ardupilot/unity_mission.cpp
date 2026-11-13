// Unity translation unit for cpp2lean (README.md "Phase 4: AP_Mission"): ArduPilot's AP_Mission (AP_Mission.cpp,
// included unmodified with the flags of its unit in the reference build, AP_SDCARD_STORAGE_ENABLED 0 on both sides:
// below), with StorageManager (the mission's StorageAccess over the HAL storage), AP_Param's parameter classes
// (AP_ParamT.cpp: MIS_TOTAL, MIS_RESTART, MIS_OPTIONS are state, --param-ext), AP_Common's Location and AP_Math's
// helpers it calls. The objects are the vehicle's: `AP_Mission mission` as ModeAuto holds it (mode.h:619), its three
// callbacks into ModeAuto bound to a stand-in (`MissionVehicle`, not translated: the functor members are left out,
// the execution state machine that calls them is Phase 5). Boundary: `hal.util->get_soft_armed()`,
// `AP_HAL::millis()`, `AP::ahrs().get_home()` (inputs), GCS text (left out), the HAL storage (--hal-storage).
// AP_SDCARD_STORAGE_ENABLED is 1 in the reference build (SITL); its code is `init`'s microSD block (taken only if
// BRD_SD_MISSION > 0, default 0) and StorageAccess's `file != nullptr` branches (taken only after attach_file):
// as for StorageManager (README.md "Phase 2b"), the model is the reference while BRD_SD_MISSION is 0.
//
// MissionTest (below) is the difftest's harness (not ArduPilot code): its member functions take seeds, build
// random commands, MAVLink items and storage contents with a xorshift generator (translated like the rest, so
// both sides make the same values), call the mission and return a 64-bit FNV-1a hash of what they observed:
// results, every field and byte of the commands and items, and, after every call, the whole HAL storage and every
// command read back with read_cmd_from_storage.
#include <AP_Mission/AP_Mission.cpp>
#include <StorageManager/StorageManager.cpp>
#include <AP_Param/AP_ParamT.cpp>
#include <AP_Math/location.cpp>
#include <AP_Common/Location.cpp>
#include <AP_Math/AP_Math.cpp>

class MissionVehicle {
public:
    bool start_command(const AP_Mission::Mission_Command &cmd) { return true; }
    bool verify_command(const AP_Mission::Mission_Command &cmd) { return true; }
    void exit_mission() {}
};

// the command ids the conversions handle in the reference configuration, those compiled out (gripper, payload
// place, scripting's NAV_SCRIPT_TIME, the mount's ROI_WPNEXT_OFFSET), 0 and 1 (reserved), and unknown ones; not the
// fence and rally ids (5000-5004, 5100: stored in a location with a 16-bit id, which read_cmd_from_storage refuses
// with AP_HAL::panic under SITL, AP_Mission.cpp:869-876, the one path the translation leaves out)
static const uint16_t mt_ids[] = {
    0, 1, 16, 17, 18, 19, 20, 21, 22, 30, 31, 36, 82, 83, 84, 85, 92, 93, 94, 112, 114, 115, 177, 178, 179, 181,
    182, 183, 184, 188, 189, 191, 193, 195, 197, 201, 202, 203, 205, 206, 207, 208, 210, 211, 212, 213, 214, 215,
    218, 222, 223, 2000, 2001, 2500, 2501, 531, 532, 534, 600, 601, 1000, 3000, 42600, 42701, 42702, 43003, 43004,
    115, 16, 16, 22, 21, 177, 20, 82, 255, 256, 65535
};

extern AP_Mission mission;

class MissionTest {
public:
    // boot: the whole storage set to a pattern of the seed, the mission's area given the format version or not
    // (mode 0: random bytes, 1: the version, 2: the version and random commands), MIS_TOTAL and MIS_OPTIONS set,
    // then `init()`
    uint64_t t_boot(uint32_t seed, int16_t total, uint8_t mode, uint16_t options) {
        rng = seed | 1;
        uint8_t chunk[64];
        for (uint16_t ofs = 0; ofs < HAL_STORAGE_SIZE; ofs += 64) {
            for (uint8_t i = 0; i < 64; i++) {
                chunk[i] = (uint8_t)next();
            }
            hal.storage->write_block(ofs, chunk, sizeof(chunk));
        }
        StorageAccess area(StorageManager::StorageMission);
        for (uint16_t k = 0; k < 700; k++) {
            valid_bools(k);
        }
        if (mode % 3 != 0) {
            area.write_uint32(0, AP_MISSION_EEPROM_VERSION);
        }
        if (mode % 3 == 2) {
            for (uint16_t k = 0; k < 40; k++) {
                random_command(cmd, next() % 4);
                mission.write_cmd_to_storage(k, cmd);
            }
        }
        mission._cmd_total.set(total);
        mission._options.set(options);
        mission.init();
        return finish(mode);
    }

    // add_cmd of a random command (kind: from a random MAVLink item, from random bytes, a location command)
    uint64_t t_add(uint32_t seed, uint8_t kind) {
        rng = seed | 1;
        random_command(cmd, kind);
        const bool r = mission.add_cmd(cmd);
        return finish(hash_cmd(cmd, r));
    }

    // replace_cmd at an index near the end of the mission (or anywhere)
    uint64_t t_replace(uint32_t seed, uint16_t index, uint8_t kind) {
        rng = seed | 1;
        random_command(cmd, kind);
        if (kind & 4) {
            index = mission.num_commands() == 0 ? 0 : index % (mission.num_commands() + 2);
        }
        const bool r = mission.replace_cmd(index, cmd);
        return finish(hash_cmd(cmd, r));
    }

    // a raw record written at a command slot (to read records the conversions never write: tag bytes 0 and 1, any id)
    uint64_t t_raw(uint32_t seed, uint16_t index, uint8_t tag) {
        rng = seed | 1;
        StorageAccess area(StorageManager::StorageMission);
        uint8_t rawrec[15];
        for (uint8_t i = 0; i < 15; i++) {
            rawrec[i] = (uint8_t)next();
        }
        if (tag % 4 == 0) {
            rawrec[0] = 0;     // a 16-bit id, old format (no location ids: those would panic, AP_Mission.cpp:874)
            uint16_t id = 256 + next() % 4000;
            if (AP_Mission::stored_in_location(id)) {
                id = 42600;
            }
            memcpy(&rawrec[1], &id, 2);
        } else if (tag % 4 == 1) {
            rawrec[0] = 1;     // a 16-bit id, new format
        } else if (tag % 4 == 3 && rawrec[0] == 0) {
            rawrec[0] = 2;     // (not the old format: its id could be a location id)
        } else if (tag % 4 == 2) {
            rawrec[0] = (uint8_t)mt_ids[next() % (sizeof(mt_ids) / 2)];
            if (rawrec[0] < 2) {
                rawrec[0] = 16;
            }
        }
        const uint16_t n = mission.num_commands_max();
        area.write_block(4 + (index % (n + 1)) * 15, rawrec, sizeof(rawrec));
        valid_bools(index % (n + 1));
        return finish(tag);
    }

    uint64_t t_read(uint16_t index) {
        const bool r = mission.read_cmd_from_storage(index, cmd);
        return finish(hash_cmd(cmd, r));
    }

    // a command read back and converted to MISSION_ITEM_INT, as MissionItemProtocol_Waypoints::get_item does; the
    // item's bytes kept (`item`)
    uint64_t t_get(uint16_t index) {
        AP_Mission::Mission_Command c {};
        const bool r = mission.read_cmd_from_storage(index, c);
        mavlink_mission_item_int_t p;
        memset(&p, 0, sizeof(p));
        const bool ok = r && AP_Mission::mission_cmd_to_mavlink_int(c, p);
        memcpy(item, &p, sizeof(item));
        return finish(r + 2 * ok);
    }

    uint64_t t_clear(void) {
        const bool r = mission.clear();
        return finish(r);
    }

    uint64_t t_truncate(uint16_t index) {
        mission.truncate(index);
        return finish(index);
    }

    uint64_t t_home(void) {
        mission.write_home_to_storage();
        return finish(7);
    }

    uint64_t t_next(uint16_t start) {
        const bool r = mission.get_next_nav_cmd(start, cmd);
        return finish(hash_cmd(cmd, r));
    }

    // a random MISSION_ITEM_INT through mavlink_int_to_mission_cmd (result and every byte of the command), the command
    // back through mission_cmd_to_mavlink_int (result and every byte of the item)
    uint64_t t_conv(uint32_t seed, uint8_t kind) {
        rng = seed | 1;
        mavlink_mission_item_int_t item;
        random_item(item, kind);
        h = 1469598103934665603ULL;
        Mission_Command_bytes(cmd);
        const MAV_MISSION_RESULT res = AP_Mission::mavlink_int_to_mission_cmd(item, cmd);
        mix(res);
        hash_cmd(cmd, true);
        mavlink_mission_item_int_t back;
        memset(&back, 0x5a, sizeof(back));
        const bool ok = AP_Mission::mission_cmd_to_mavlink_int(cmd, back);
        mix(ok);
        hash_item_int(back);
        return h;
    }

    // MISSION_ITEM to MISSION_ITEM_INT and back, on random items
    uint64_t t_item(uint32_t seed, uint8_t kind) {
        rng = seed | 1;
        mavlink_mission_item_int_t item;
        random_item(item, kind);
        mavlink_mission_item_t fl;
        memset(&fl, 0, sizeof(fl));
        h = 1469598103934665603ULL;
        const MAV_MISSION_RESULT r1 = AP_Mission::convert_MISSION_ITEM_INT_to_MISSION_ITEM(item, fl);
        mix(r1);
        hash_item(fl);
        if (kind & 8) {
            fl.x = random_float();
            fl.y = random_float();
        }
        mavlink_mission_item_int_t back;
        memset(&back, 0, sizeof(back));
        const MAV_MISSION_RESULT r2 = AP_Mission::convert_MISSION_ITEM_to_MISSION_ITEM_INT(fl, back);
        mix(r2);
        hash_item_int(back);
        return h;
    }

    uint64_t h_storage;     // the hash of the whole HAL storage after the last call
    uint64_t h_cmds;        // the hash of every command read back after the last call
    uint16_t total;         // num_commands() after the last call
    uint8_t item[sizeof(mavlink_mission_item_int_t)];   // the item t_get made

private:
    uint32_t rng;
    uint64_t h;
    AP_Mission::Mission_Command cmd;

    uint32_t next(void) {
        rng ^= rng << 13;
        rng ^= rng >> 17;
        rng ^= rng << 5;
        return rng;
    }

    void mix(uint64_t v) {
        for (uint8_t i = 0; i < 8; i++) {
            h = (h ^ (uint8_t)(v >> (8 * i))) * 1099511628211ULL;
        }
    }

    void mix_bytes(const uint8_t *b, uint16_t n) {
        for (uint16_t i = 0; i < n; i++) {
            h = (h ^ b[i]) * 1099511628211ULL;
        }
    }

    // a float of every kind: random bits (NaNs with payloads, infinities, denormals), small integers, halves, values
    // near the conversions' limits
    float random_float(void) {
        const uint32_t k = next() % 10;
        float f = 0;
        if (k == 0) {
            uint32_t u = next();
            memcpy(&f, &u, 4);
        } else if (k == 1) {
            static const uint32_t special[] = {0x7fc00000U, 0xffc00001U, 0x7f800001U, 0x7f800000U, 0xff800000U, 0x80000000U,
                                               0x00000001U, 0x7f7fffffU, 0xff7fffffU, 0x00800000U, 0x477fff00U, 0x47800000U};
            uint32_t u = special[next() % 12];
            memcpy(&f, &u, 4);
        } else if (k <= 4) {
            f = (float)((int32_t)(next() % 601) - 300);
        } else if (k == 5) {
            f = (float)((int32_t)(next() % 2001) - 1000) * 0.25f;
        } else if (k == 6) {
            f = (float)(next() % 70000);
        } else if (k == 7) {
            f = (float)(next() % 1000) * 0.001f;
        } else if (k == 8) {
            f = (float)((int32_t)(next() % 200001) - 100000) * 0.9f;
        } else {
            f = (float)((int32_t)next()) * 1.0e-3f;
        }
        return f;
    }

    int32_t random_int(void) {
        const uint32_t k = next() % 6;
        if (k == 0) {
            static const int32_t special[] = {0, 1, -1, 900000000, -900000000, 900000001, -900000001, 1800000000,
                                              -1800000000, 1800000001, -1800000001, 2147483647, -2147483647 - 1};
            return special[next() % 13];
        }
        if (k == 1) {
            return (int32_t)next();
        }
        if (k == 2) {
            return (int32_t)(next() % 1800000001U) - 900000000;
        }
        if (k == 3) {
            return (int32_t)(next() % 601) - 300;
        }
        return (int32_t)(next() % 400000000U) - 200000000;
    }

    void random_item(mavlink_mission_item_int_t &item, uint8_t kind) {
        item.param1 = random_float();
        item.param2 = random_float();
        item.param3 = random_float();
        item.param4 = random_float();
        item.x = random_int();
        item.y = random_int();
        item.z = random_float();
        item.seq = (kind & 2) ? (uint16_t)next() : (uint16_t)(next() % 8);
        item.command = (kind & 1) ? (uint16_t)next() : mt_ids[next() % (sizeof(mt_ids) / 2)];
        item.target_system = (uint8_t)next();
        item.target_component = (uint8_t)next();
        item.frame = (kind & 4) ? (uint8_t)next() : (uint8_t)(next() % 12);
        item.current = (uint8_t)next();
        item.autocontinue = (uint8_t)next();
        item.mission_type = (uint8_t)next();
    }

    // a command: (kind 0, 1) converted from a random item when that is accepted, else (kind 2) random bytes for id,
    // p1, the content and the type-specific bits, or (kind 3) a location command with random fields
    void random_command(AP_Mission::Mission_Command &c, uint8_t kind) {
        c = {};
        if (kind % 4 <= 1) {
            mavlink_mission_item_int_t item;
            random_item(item, kind % 2);
            if (AP_Mission::mavlink_int_to_mission_cmd(item, c) == MAV_MISSION_ACCEPTED) {
                return;
            }
        }
        c.index = (uint16_t)next();
        c.id = mt_ids[next() % (sizeof(mt_ids) / 2)];
        if (kind % 4 == 2 && (next() & 1)) {
            c.id = (uint16_t)next();
            if (c.id >= 256 && AP_Mission::stored_in_location(c.id)) {
                c.id = 42600;
            }
        }
        c.p1 = (uint16_t)next();
        uint8_t b[16];
        for (uint8_t i = 0; i < 16; i++) {
            b[i] = (uint8_t)next();
        }
        memcpy((void *)&c.content, b, 16);
        c.type_specific_bits = (uint8_t)next();
        if (kind % 4 == 3) {
            c.content.location = {};
            c.content.location.relative_alt = next() & 1;
            c.content.location.loiter_ccw = next() & 1;
            c.content.location.terrain_alt = next() & 1;
            c.content.location.origin_alt = next() & 1;
            c.content.location.loiter_xtrack = next() & 1;
            c.content.location.alt = random_int();
            c.content.location.lat = random_int();
            c.content.location.lng = random_int();
            c.type_specific_bits = (uint8_t)(next() & 3);
        }
        if (c.id == MAV_CMD_DO_ENGINE_CONTROL) {
            uint8_t v[16];  // (the bool members of Do_Engine_Control: valid_bools)
            memcpy(v, (const void *)&c.content, 16);
            v[0] &= 1;
            v[1] &= 1;
            v[4] &= 1;
            memcpy((void *)&c.content, v, 16);
        }
    }

    // a stored DO_ENGINE_CONTROL record (the only command with `bool` members) gets bytes 0 or 1 for its bools: any
    // other byte is not a value of `bool` (reading it is undefined; clang's code converts the byte itself, 245 to
    // 245.0f, the model's `bool` view of a byte is `!= 0`)
    void valid_bools(uint16_t k) {
        StorageAccess area(StorageManager::StorageMission);
        uint8_t r[15];
        area.read_block(r, 4 + k * 15, sizeof(r));
        uint16_t id = r[0];
        uint8_t c = 3;
        if (r[0] < 2) {
            id = r[1] | (uint16_t)(r[2] << 8);
            c = 5;
        }
        if (id == MAV_CMD_DO_ENGINE_CONTROL) {
            r[c] &= 1;
            r[c + 1] &= 1;
            r[c + 4] &= 1;
            area.write_block(4 + k * 15, r, sizeof(r));
        }
    }

    void Mission_Command_bytes(AP_Mission::Mission_Command &c) {
        c = {};
    }

    uint64_t hash_cmd(const AP_Mission::Mission_Command &c, bool r) {
        mix(r);
        mix(c.index);
        mix(c.id);
        mix(c.p1);
        uint8_t b[16];
        memcpy(b, (const void *)&c.content, 16);
        mix_bytes(b, 16);
        mix(c.type_specific_bits);
        return h;
    }

    void hash_item_int(const mavlink_mission_item_int_t &p) {
        uint8_t b[sizeof(mavlink_mission_item_int_t)];
        memcpy(b, &p, sizeof(b));
        mix_bytes(b, sizeof(b));
    }

    void hash_item(const mavlink_mission_item_t &p) {
        uint8_t b[sizeof(mavlink_mission_item_t)];
        memcpy(b, &p, sizeof(b));
        mix_bytes(b, sizeof(b));
    }

    // after every call: the whole storage, every command read back (and two beyond the end), the count
    uint64_t finish(uint64_t v) {
        h = 1469598103934665603ULL;
        uint8_t chunk[64];
        for (uint16_t ofs = 0; ofs < HAL_STORAGE_SIZE; ofs += 64) {
            hal.storage->read_block(chunk, ofs, sizeof(chunk));
            mix_bytes(chunk, 64);
        }
        h_storage = h;
        h = 1469598103934665603ULL;
        const uint16_t n = mission.num_commands();
        for (uint16_t i = 0; i < n + 2 && i < 400; i++) {
            AP_Mission::Mission_Command c {};
            const bool r = mission.read_cmd_from_storage(i, c);
            hash_cmd(c, r);
            if (r) {
                mavlink_mission_item_int_t p;
                const bool ok = AP_Mission::mission_cmd_to_mavlink_int(c, p);
                mix(ok);
                hash_item_int(p);
            }
        }
        h_cmds = h;
        total = n;
        return v ^ h_storage ^ (h_cmds << 1);
    }
};

MissionVehicle vehicle;
AP_Mission mission{
    FUNCTOR_BIND(&vehicle, &MissionVehicle::start_command, bool, const AP_Mission::Mission_Command &),
    FUNCTOR_BIND(&vehicle, &MissionVehicle::verify_command, bool, const AP_Mission::Mission_Command &),
    FUNCTOR_BIND(&vehicle, &MissionVehicle::exit_mission, void)};
MissionTest tester;
