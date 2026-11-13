// Unity translation unit for cpp2lean: ArduPilot's StorageManager (StorageManager.cpp, included
// unmodified) over the HAL storage (the boundary: `hal.storage`, a byte array of HAL_STORAGE_SIZE,
// --hal-storage), and the functions the difftest drives (README.md, "Phase 2b"). Each test
// function first sets the whole storage to a pattern from a seed (so that every call starts from
// the same bytes on both sides: the C++ storage persists between calls, the Lean one is passed in),
// then calls StorageAccess's members on an object of a storage type, and returns their results and
// a hash of the whole storage. The reads of read_byte/read_uint16/read_uint32/read_float are kept
// inside the area: for a read that does not fit, read_block leaves (part of) their local `v`
// unwritten, and they return an indeterminate value (StorageManager.cpp:249-284); the model's
// locals start at zero. Writes and read_block/write_block are driven anywhere.
#include <StorageManager/StorageManager.cpp>

extern const AP_HAL::HAL& hal;

// the storage set to a pattern of the seed, 256 bytes at a time
static void storage_reset(uint32_t seed)
{
    uint8_t chunk[256];
    for (uint16_t ofs = 0; ofs < HAL_STORAGE_SIZE; ofs += 256) {
        for (uint16_t i = 0; i < 256; i++) {
            chunk[i] = (uint8_t)(((seed ^ ofs) + i) * 2654435761U >> 24);
        }
        hal.storage->write_block(ofs, chunk, sizeof(chunk));
    }
}

// a hash of the whole storage
static uint64_t storage_hash()
{
    uint8_t chunk[256];
    uint64_t h = 1469598103934665603ULL;
    for (uint16_t ofs = 0; ofs < HAL_STORAGE_SIZE; ofs += 256) {
        hal.storage->read_block(chunk, ofs, sizeof(chunk));
        for (uint16_t i = 0; i < 256; i++) {
            h = (h ^ chunk[i]) * 1099511628211ULL;
        }
    }
    return h;
}

uint64_t sm_size(uint8_t type)
{
    StorageAccess a((StorageManager::StorageType)(type % 8));
    return a.size();
}

uint64_t sm_byte(uint32_t seed, uint8_t type, uint16_t loc, uint8_t v, uint16_t at)
{
    storage_reset(seed);
    StorageAccess a((StorageManager::StorageType)(type % 8));
    if (a.size() < 8) {
        return a.size();
    }
    at %= a.size() - 4;
    loc %= a.size() - 4;
    a.write_byte(loc, v);
    a.write_uint8(loc + 3, v ^ 0x5a);
    uint64_t r = a.read_byte(at) + 256 * a.read_uint8(loc);
    return storage_hash() ^ r;
}

uint64_t sm_u16(uint32_t seed, uint8_t type, uint16_t loc, uint16_t v, uint16_t at)
{
    storage_reset(seed);
    StorageAccess a((StorageManager::StorageType)(type % 8));
    if (a.size() < 8) {
        return a.size();
    }
    at %= a.size() - 2;
    loc %= a.size() - 2;
    a.write_uint16(loc, v);
    uint64_t r = a.read_uint16(at) + 65536 * (uint64_t)a.read_uint16(loc);
    return storage_hash() ^ r;
}

uint64_t sm_u32(uint32_t seed, uint8_t type, uint16_t loc, uint32_t v, uint16_t at)
{
    storage_reset(seed);
    StorageAccess a((StorageManager::StorageType)(type % 8));
    if (a.size() < 8) {
        return a.size();
    }
    at %= a.size() - 4;
    loc %= a.size() - 4;
    a.write_uint32(loc, v);
    uint64_t r = a.read_uint32(at) ^ ((uint64_t)a.read_uint32(loc) << 32);
    return storage_hash() ^ r;
}

float sm_float(uint32_t seed, uint8_t type, uint16_t loc, float v, uint16_t at)
{
    storage_reset(seed);
    StorageAccess a((StorageManager::StorageType)(type % 8));
    if (a.size() < 8) {
        return (float)a.size();
    }
    at %= a.size() - 4;
    loc %= a.size() - 4;
    a.write_float(loc, v);
    return a.read_float(at) + a.read_float(loc) * (float)(storage_hash() & 0xff);
}

uint64_t sm_block(uint32_t seed, uint8_t type, uint16_t src, uint16_t dst, uint8_t n)
{
    storage_reset(seed);
    StorageAccess a((StorageManager::StorageType)(type % 8));
    uint8_t buf[64];
    memset(buf, 0xee, sizeof(buf));
    const bool ok1 = a.read_block(buf, src, n % 65);
    const bool ok2 = a.write_block(dst, buf, n % 65);
    uint64_t h = storage_hash();
    for (uint8_t i = 0; i < 64; i++) {
        h = (h ^ buf[i]) * 1099511628211ULL;
    }
    return h ^ (ok1 ? 1 : 0) ^ (ok2 ? 2 : 0);
}

uint64_t sm_copy(uint32_t seed, uint8_t from, uint8_t to)
{
    storage_reset(seed);
    StorageAccess a((StorageManager::StorageType)(from % 8));
    StorageAccess b((StorageManager::StorageType)(to % 8));
    const bool ok = b.copy_area(a);
    return storage_hash() ^ (ok ? 1 : 0);
}
