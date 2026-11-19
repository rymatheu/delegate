// stubs_param.cpp: parameter storage, and what stands in.
//
// AP_Param (libraries/AP_Param) is the parameter storage machinery: tables of names and defaults
// (var_info, in the libraries, compiled here), values loaded from EEPROM at boot, saved on
// change, sent to the ground station. The machinery is outside the module; the stand-in is a
// storage that holds exactly the values the harness gives it (the parameter record and the
// X500's stored GPS1_TYPE) and starts empty in every case.
//
//   symbol                                   why it is outside the module, and what stands in
//   AP_Param::setup_object_defaults,         the code defaults, set by each object's constructor
//   set_value, get_default_value             from its var_info. The same code as AP_Param.cpp
//                                            (lines 1501-1542 and 2685-2696), without the table
//                                            of overrides a defaults file would fill (SITL boots
//                                            without one: storage-x500.txt).
//   harness_param_load (the harness's)       AP_Param::load_all: a value in storage is written
//                                            into the object. Finds the parameter by its full
//                                            name through the vehicle's top-level table
//                                            (ArduCopter/Parameters.cpp: GOBJECT(ins, "INS"),
//                                            GOBJECT(compass, "COMPASS_"), GOBJECT(ahrs, "AHRS_"),
//                                            GOBJECT(barometer, "BARO"), GOBJECT(gps, "GPS"),
//                                            GOBJECTN(ahrs.ekf3.EKF3, "EK3_")), walking the
//                                            groups as AP_Param::find_group does. Marks it stored.
//   AP_Param::configured,                    whether the storage holds a value for this parameter
//   configured_in_storage                    (set_default and set_and_default consult it).
//   AP_Param::load                           a single parameter from storage: true and its value
//                                            if stored, else false (the IMU and compass ids).
//   AP_Param::save, save_sync,               storage writes (calibration results, sensor ids,
//   set_and_save, set_and_save_ifchanged,    the barometer's ground pressure): the value is set in
//   notify                                   the object as the real code does before saving; the
//                                            write itself is dropped.
//   AP_Param::set_default_by_name            the SITL compass driver sets COMPASS_SCALE's default;
//                                            found by name as above, set when not stored.
//   AP_Param::find_top_level_key_by_pointer, the storage's key table, consulted by parameter
//   convert_class, convert_old_parameters,   conversions of old stored values: no table, nothing to
//   _convert_parameter_width                 convert (the storage holds no old values).
//   AP_Param::invalidate_count, add_default  the parameter count and the table of defaults the
//                                            ground station is sent: not kept.
//   (AP_Param/AP_ParamT.cpp, the value setters set_default, set_and_save, set_and_notify, ...,
//   is ArduPilot's own, compiled from sources.txt; it calls configured, save and notify above.)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <AP_Param/AP_Param.h>
#include <AP_AHRS/AP_AHRS.h>
#include <AP_AHRS/AP_AHRS_NavEKF3.h>
#include <AP_Baro/AP_Baro.h>
#include <AP_Compass/AP_Compass.h>
#include <AP_GPS/AP_GPS.h>
#include <AP_InertialSensor/AP_InertialSensor.h>
#include <AP_NavEKF3/AP_NavEKF3.h>

#include "harness_cut.h"

// --- the code defaults (as AP_Param.cpp)
void AP_Param::set_value(enum ap_var_type type, void *ptr, float value)
{
    switch (type) {
    case AP_PARAM_INT8:
        ((AP_Int8 *)ptr)->set(value);
        break;
    case AP_PARAM_INT16:
        ((AP_Int16 *)ptr)->set(value);
        break;
    case AP_PARAM_INT32:
        ((AP_Int32 *)ptr)->set(value);
        break;
    case AP_PARAM_FLOAT:
        ((AP_Float *)ptr)->set(value);
        break;
    default:
        break;
    }
}

float AP_Param::get_default_value(const AP_Param *vp, const struct GroupInfo &info)
{
    if ((info.flags & AP_PARAM_FLAG_DEFAULT_POINTER) != 0) {
        return *((float*)((ptrdiff_t)vp - info.def_value_offset));
    }
    return info.def_value;
}

void AP_Param::setup_object_defaults(const void *object_pointer, const struct GroupInfo *group_info)
{
    ptrdiff_t base = (ptrdiff_t)object_pointer;
    uint8_t type;
    for (uint8_t i=0;
         (type=group_info[i].type) != AP_PARAM_NONE;
         i++) {
        if (type <= AP_PARAM_FLOAT) {
            void *ptr = (void *)(base + group_info[i].offset);
            set_value((enum ap_var_type)type, ptr,
                      get_default_value((const AP_Param *)ptr, group_info[i]));
        } else if (type == AP_PARAM_VECTOR3F) {
            // Single default for all components
            void *ptr = (void *)(base + group_info[i].offset);
            const float default_val = get_default_value((const AP_Param *)ptr, group_info[i]);
            ((AP_Vector3f *)ptr)->set(Vector3f{default_val, default_val, default_val});
        }
    }
}

// --- the storage: which parameters hold a stored value
static const uint16_t MAX_STORED = 128;
static const void *stored[MAX_STORED];
static uint16_t num_stored;

static bool is_stored(const void *p)
{
    for (uint16_t i = 0; i < num_stored; i++) {
        if (stored[i] == p) {
            return true;
        }
    }
    return false;
}

static void mark_stored(const void *p)
{
    if (is_stored(p)) {
        return;
    }
    if (num_stored == MAX_STORED) {
        fprintf(stderr, "estimator: parameter storage full\n");
        abort();
    }
    stored[num_stored++] = p;
}

void harness_reset_params()
{
    num_stored = 0;
}

// --- lookup by name, as AP_Param::find_group walks the tables
struct Found {
    void *ptr;              // the AP_Param object (for a vector, the AP_Vector3f)
    enum ap_var_type type;
    int8_t component;       // for a vector: 0, 1, 2 for _X, _Y, _Z
};

static bool find_in_group(const char *name, const AP_Param::GroupInfo *group_info, ptrdiff_t base,
                          Found &f)
{
    uint8_t type;
    for (uint8_t i = 0; (type = group_info[i].type) != AP_PARAM_NONE; i++) {
        const AP_Param::GroupInfo &g = group_info[i];
        const size_t len = strlen(g.name);
        if (strncmp(name, g.name, len) != 0) {
            continue;
        }
        const char *rest = name + len;
        if (type == AP_PARAM_GROUP) {
            ptrdiff_t new_base = base + g.offset;
            if (g.flags & AP_PARAM_FLAG_POINTER) {
                new_base = *(ptrdiff_t *)new_base;
                if (new_base == 0) {
                    continue;
                }
            }
            const AP_Param::GroupInfo *sub = (g.flags & AP_PARAM_FLAG_INFO_POINTER) ?
                *g.group_info_ptr : g.group_info;
            if (find_in_group(rest, sub, new_base, f)) {
                return true;
            }
        } else if (type == AP_PARAM_VECTOR3F) {
            if (rest[0] == '_' && rest[1] != 0 && rest[2] == 0 && rest[1] >= 'X' && rest[1] <= 'Z') {
                f = {(void *)(base + g.offset), AP_PARAM_VECTOR3F, int8_t(rest[1] - 'X')};
                return true;
            }
        } else if (rest[0] == 0) {
            f = {(void *)(base + g.offset), (enum ap_var_type)type, -1};
            return true;
        }
    }
    return false;
}

static bool lookup(const char *name, Found &f)
{
    struct Top {
        const char *prefix;
        const void *object;
        const AP_Param::GroupInfo *info;
    };
    const Top tops[] = {
        {"INS", &AP::ins(), AP_InertialSensor::var_info},
        {"COMPASS_", &AP::compass(), Compass::var_info},
        {"AHRS_", &AP::ahrs(), AP_AHRS::var_info},
        {"BARO", &AP::baro(), AP_Baro::var_info},
        {"GPS", &AP::gps(), AP_GPS::var_info},
        {"EK3_", harness_ekf3_object(), NavEKF3::var_info},
    };
    for (const Top &t : tops) {
        const size_t len = strlen(t.prefix);
        if (strncmp(name, t.prefix, len) == 0 &&
            find_in_group(name + len, t.info, (ptrdiff_t)t.object, f)) {
            return true;
        }
    }
    return false;
}

static void set_found(const Found &f, float value)
{
    if (f.type == AP_PARAM_VECTOR3F) {
        AP_Vector3f *v = (AP_Vector3f *)f.ptr;
        Vector3f x = v->get();
        x[f.component] = value;
        v->set(x);
    } else {
        AP_Param::set_value(f.type, f.ptr, value);
    }
}

void harness_param_load(const char *name, float value)
{
    Found f;
    if (!lookup(name, f)) {
        fprintf(stderr, "estimator: no parameter %s\n", name);
        abort();
    }
    set_found(f, value);
    mark_stored(f.ptr);
}

// --- the storage API the libraries call
bool AP_Param::configured_in_storage(void) const
{
    return is_stored(this);
}

bool AP_Param::configured(void) const
{
    return is_stored(this);
}

bool AP_Param::load(void)
{
    return is_stored(this);
}

void AP_Param::save(bool force_save)
{
}

void AP_Param::save_sync(bool force_save, bool send_to_gcs)
{
}

void AP_Param::notify() const
{
}

bool AP_Param::set_default_by_name(const char *name, float value)
{
    Found f;
    if (!lookup(name, f)) {
        return false;
    }
    if (!is_stored(f.ptr)) {
        set_found(f, value);
    }
    return true;
}

bool AP_Param::find_top_level_key_by_pointer(const void *ptr, uint16_t &key)
{
    return false;
}

// --- conversions of old stored values (none stored), and the parameter list's bookkeeping
void AP_Param::convert_class(uint16_t param_key, void *object_pointer,
                             const struct AP_Param::GroupInfo *group_info,
                             uint16_t old_index, bool is_top_level, bool recurse_sub_groups)
{
}

void AP_Param::convert_old_parameters(uint16_t old_key, const ConversionInfoNoKey *conversion_table,
                                      uint8_t table_size, uint8_t flags)
{
}

bool AP_Param::_convert_parameter_width(ap_var_type old_ptype, float scale_factor, bool bitmask)
{
    return false;
}

// the count of parameters the ground station is told (AP_Param.cpp); nothing to invalidate here
void AP_Param::invalidate_count(void)
{
}

// the table of defaults reported to the ground station (AP_PARAM_DEFAULTS_ENABLED): not kept
void AP_Param::add_default(AP_Param *ap, float v)
{
}
