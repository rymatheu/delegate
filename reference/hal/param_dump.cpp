/*
  copter_ref --param-dump FILE (README.md, "Phase 4: AP_Param"): the vehicle's AP_Param boot sequence up to and
  including AP_Param::load_all() on the storage image (after static construction, before setup()), and the
  parameters as a ground station enumerates them, before and after loading. Only ArduPilot functions are called;
  the format-version check of AP_Vehicle::load_parameters (AP_Vehicle/Parameters.cpp:12-28) is repeated statement by
  statement because that function goes on past load_all (gcs().convert_parameters()). Compiled with
  -fno-access-control (copter.g is private), as est_probe.cpp.

  Output: for each phase a line `# <phase>`, then one line per parameter in AP_Param::first/next_scalar order (the
  order GCS_Param uses):
      <index> <token key>,<token group_element>,<token idx> <name> <type> <value>
  name as copy_name_token(token, buf, AP_MAX_NAME_SIZE, true) writes it (GCS_Param's call), type the ap_var_type,
  value the parameter's bits (integers in decimal, floats as 8 hex digits of their bit pattern); then
  `# count <n>` and `# count_parameters <AP_Param::count_parameters()>`, and the storage's FNV-1a digest.
*/
#include "../../ArduCopter/Copter.h"
#include <stdio.h>
#include <string.h>
#include <time.h>

namespace ParamDump {

static uint64_t now_ns()
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return uint64_t(ts.tv_sec) * 1000000000ULL + uint64_t(ts.tv_nsec);
}

static unsigned enumerate(FILE *f)
{
    AP_Param::ParamToken token {};
    enum ap_var_type type;
    unsigned n = 0;
    for (AP_Param *vp = AP_Param::first(&token, &type); vp != nullptr; vp = AP_Param::next_scalar(&token, &type)) {
        char name[AP_MAX_NAME_SIZE + 1] {};
        vp->copy_name_token(token, name, AP_MAX_NAME_SIZE, true);
        if (f != nullptr) {
            fprintf(f, "%u %u,%u,%u %s %u ", n, unsigned(token.key), unsigned(token.group_element), unsigned(token.idx), name, unsigned(type));
            switch (type) {
            case AP_PARAM_INT8: fprintf(f, "%d\n", int(((AP_Int8 *)vp)->get())); break;
            case AP_PARAM_INT16: fprintf(f, "%d\n", int(((AP_Int16 *)vp)->get())); break;
            case AP_PARAM_INT32: fprintf(f, "%d\n", int(((AP_Int32 *)vp)->get())); break;
            case AP_PARAM_FLOAT: {
                float v = ((AP_Float *)vp)->get();
                uint32_t u;
                memcpy(&u, &v, 4);
                fprintf(f, "%08x\n", unsigned(u));
                break;
            }
            default: fprintf(f, "?\n"); break;
            }
        }
        n++;
    }
    return n;
}

static void phase(FILE *f, const char *tag)
{
    fprintf(f, "# %s\n", tag);
    const unsigned n = enumerate(f);
    fprintf(f, "# count %u\n", n);
    fprintf(f, "# count_parameters %u\n", unsigned(AP_Param::count_parameters()));
    uint8_t buf[HAL_STORAGE_SIZE];
    hal.storage->read_block(buf, 0, sizeof(buf));
    uint64_t h = 1469598103934665603ULL;
    for (uint32_t i = 0; i < sizeof(buf); i++) {
        h = (h ^ buf[i]) * 1099511628211ULL;
    }
    fprintf(f, "# storage %016llx\n", (unsigned long long)h);
}

void run(const char *path)
{
    FILE *f = fopen(path, "w");
    if (f == nullptr) {
        fprintf(stderr, "param_dump: cannot write %s\n", path);
        _exit(2);
    }
    // AP_Vehicle::setup (AP_Vehicle.cpp:315-337): the defaults, then the table check and load_parameters
    AP_Param::setup_sketch_defaults();
    phase(f, "defaults");
    AP_Param::invalidate_count();
    AP_Param::check_var_info();
    // AP_Vehicle::load_parameters(g.format_version, Parameters::k_format_version) as far as load_all
    AP_Int16 &format_version = copter.g.format_version;
    const uint16_t expected_format_version = Parameters::k_format_version;
    if (!format_version.load() ||
        format_version != expected_format_version) {
        StorageManager::erase();
        AP_Param::erase_all();
        format_version.set_and_save(expected_format_version);
    }
    format_version.set_default(expected_format_version);
    const uint64_t t0 = now_ns();
    AP_Param::load_all();
    const uint64_t t1 = now_ns();
    AP_Param::invalidate_count();
    phase(f, "loaded");
    // speed: the enumeration (first/next_scalar and copy_name_token) repeated
    const unsigned reps = 200;
    const uint64_t t2 = now_ns();
    unsigned total = 0;
    for (unsigned r = 0; r < reps; r++) {
        total += enumerate(nullptr);
    }
    const uint64_t t3 = now_ns();
    fprintf(stderr, "param_dump: load_all %.1f us; enumeration %.1f us per pass (%u parameters)\n",
            (t1 - t0) / 1e3, (t3 - t2) / 1e3 / reps, total / reps);
    fclose(f);
}

/*
  --param-test SCRIPT (with --param-dump OUT): the per-function differential test of the translated AP_Param
  (ardupilot/param_difftest.py): after the boot sequence above (without its dumps), one command per line of SCRIPT,
  each printing what it observed (names through copy_name_token, values by type, the storage's digest):
    enum KEY GE IDX        next_scalar from the token {KEY, GE, IDX}
    name NAME              find_by_name, and find (whether it gives the same parameter and type)
    index N                find_by_index
    set NAME TYPE BITS F   find_by_name, set_float(value, TYPE), save_sync(F, false)
    load NAME              find_by_name, load()
    count                  invalidate_count, count_parameters
    dump                   the enumeration
    loadall                load_all again
*/
static void value(FILE *f, AP_Param *vp, enum ap_var_type type)
{
    switch (type) {
    case AP_PARAM_INT8: fprintf(f, "%d", int(((AP_Int8 *)vp)->get())); break;
    case AP_PARAM_INT16: fprintf(f, "%d", int(((AP_Int16 *)vp)->get())); break;
    case AP_PARAM_INT32: fprintf(f, "%d", int(((AP_Int32 *)vp)->get())); break;
    case AP_PARAM_FLOAT: {
        float v = ((AP_Float *)vp)->get();
        uint32_t u;
        memcpy(&u, &v, 4);
        fprintf(f, "%08x", unsigned(u));
        break;
    }
    default: fprintf(f, "?"); break;
    }
}

static void named(FILE *f, AP_Param *vp, const AP_Param::ParamToken &token, enum ap_var_type type)
{
    if (vp == nullptr) {
        fprintf(f, "null");
        return;
    }
    char name[AP_MAX_NAME_SIZE + 1] {};
    vp->copy_name_token(token, name, AP_MAX_NAME_SIZE, true);
    fprintf(f, "%u,%u,%u %s %u ", unsigned(token.key), unsigned(token.group_element), unsigned(token.idx), name, unsigned(type));
    value(f, vp, type);
}

static uint64_t digest()
{
    uint8_t buf[HAL_STORAGE_SIZE];
    hal.storage->read_block(buf, 0, sizeof(buf));
    uint64_t h = 1469598103934665603ULL;
    for (uint32_t i = 0; i < sizeof(buf); i++) {
        h = (h ^ buf[i]) * 1099511628211ULL;
    }
    return h;
}

void test(const char *script, const char *path)
{
    FILE *in = fopen(script, "r");
    FILE *f = fopen(path, "w");
    if (in == nullptr || f == nullptr) {
        fprintf(stderr, "param_test: cannot open %s or %s\n", script, path);
        _exit(2);
    }
    AP_Param::setup_sketch_defaults();
    AP_Param::check_var_info();
    AP_Int16 &format_version = copter.g.format_version;
    const uint16_t expected_format_version = Parameters::k_format_version;
    if (!format_version.load() ||
        format_version != expected_format_version) {
        StorageManager::erase();
        AP_Param::erase_all();
        format_version.set_and_save(expected_format_version);
    }
    format_version.set_default(expected_format_version);
    fprintf(f, "boot %d %016llx\n", int(AP_Param::load_all()), (unsigned long long)digest());
    char line[256];
    while (fgets(line, sizeof(line), in) != nullptr) {
        char cmd[32] {}, a[64] {};
        unsigned k = 0, g = 0, i = 0, ty = 0, bits = 0, force = 0;
        if (sscanf(line, "%31s", cmd) != 1) {
            continue;
        }
        fprintf(f, "%s", line);
        if (strcmp(cmd, "enum") == 0 && sscanf(line, "%*s %u %u %u", &k, &g, &i) == 3) {
            AP_Param::ParamToken token {};
            token.key = k;
            token.group_element = g;
            token.idx = i;
            enum ap_var_type type = AP_PARAM_NONE;
            AP_Param *vp = AP_Param::next_scalar(&token, &type);
            named(f, vp, token, type);
        } else if (strcmp(cmd, "name") == 0 && sscanf(line, "%*s %63s", a) == 1) {
            AP_Param::ParamToken token {};
            enum ap_var_type type = AP_PARAM_NONE, type2 = AP_PARAM_NONE;
            AP_Param *vp = AP_Param::find_by_name(a, &type, &token);
            named(f, vp, token, type);
            AP_Param *vp2 = AP_Param::find(a, &type2);
            fprintf(f, " find %d %u", int(vp2 == vp), unsigned(vp2 != nullptr ? type2 : 0));
        } else if (strcmp(cmd, "index") == 0 && sscanf(line, "%*s %u", &k) == 1) {
            AP_Param::ParamToken token {};
            enum ap_var_type type = AP_PARAM_NONE;
            AP_Param *vp = AP_Param::find_by_index(k, &type, &token);
            named(f, vp, token, type);
        } else if (strcmp(cmd, "set") == 0 && sscanf(line, "%*s %63s %u %x %u", a, &ty, &bits, &force) == 4) {
            AP_Param::ParamToken token {};
            enum ap_var_type type = AP_PARAM_NONE;
            AP_Param *vp = AP_Param::find_by_name(a, &type, &token);
            if (vp != nullptr) {
                float v;
                memcpy(&v, &bits, 4);
                vp->set_float(v, (enum ap_var_type)ty);
                vp->save_sync(force != 0, false);
            }
            named(f, vp, token, type);
            fprintf(f, " %016llx", (unsigned long long)digest());
        } else if (strcmp(cmd, "load") == 0 && sscanf(line, "%*s %63s", a) == 1) {
            AP_Param::ParamToken token {};
            enum ap_var_type type = AP_PARAM_NONE;
            AP_Param *vp = AP_Param::find_by_name(a, &type, &token);
            int r = vp != nullptr ? int(vp->load()) : -1;
            named(f, vp, token, type);
            fprintf(f, " %d", r);
        } else if (strcmp(cmd, "count") == 0) {
            AP_Param::invalidate_count();
            fprintf(f, "%u", unsigned(AP_Param::count_parameters()));
        } else if (strcmp(cmd, "dump") == 0) {
            fprintf(f, "\n");
            enumerate(f);
        } else if (strcmp(cmd, "loadall") == 0) {
            fprintf(f, "%d %016llx", int(AP_Param::load_all()), (unsigned long long)digest());
        }
        fprintf(f, "\n");
    }
    fclose(f);
}

}  // namespace ParamDump
