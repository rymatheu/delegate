// The C++ environment of the AP_NavEKF_Source World difftest (ardupilot/NavEKF_Source.json; README.md "Phase 3:
// AP_InertialSensor, AP_GPS and AP_NavEKF_Source"): what AP_NavEKF_Source and AP_ParamT.cpp reach outside the
// translation, compiled with the reference build's flags against the real headers.
//   - AP::dal(): the compass's count of enabled compasses (AP_DAL_Compass::get_num_enabled, inline: the member it
//     reads is set from the line's input) on an object that is never constructed (AP_DAL is not linked);
//   - AP_Param's storage: `configured()` is the line's input; saving and notification have no effect.
#include <AP_HAL/AP_HAL.h>
#include <AP_Param/AP_Param.h>
#include <AP_DAL/AP_DAL.h>
#include <string>

#include "cpp2lean_events.h"

std::string cpp2lean_events;

// the line's inputs
uint8_t cpp2lean_num_enabled;
bool cpp2lean_configured;

// AP_DAL: never constructed; only the compass's header record is read (AP_DAL_Compass::get_num_enabled)
alignas(16) static unsigned char dal_storage[sizeof(AP_DAL)];
AP_DAL &AP::dal() { return *reinterpret_cast<AP_DAL *>(dal_storage); }
void cpp2lean_set_num_enabled(uint8_t n) { AP::dal().compass()._RMGH.num_enabled = n; }

// AP_Param: storage is outside the model (saving and notification have no effect; `configured` is an input)
void AP_Param::save(bool force_save) {}
void AP_Param::notify() const {}
bool AP_Param::configured(void) const { return cpp2lean_configured; }
void AP_Param::invalidate_count(void) {}
#if AP_PARAM_DEFAULTS_ENABLED
void AP_Param::add_default(AP_Param *ap, float v) {}
#endif

// AP_Param::setup_object_defaults and the two functions it calls, verbatim from AP_Param.cpp (802db19de1,
// lines 1501-1542 and 2685-2696; AP_Param.cpp itself needs the storage and the GCS): the defaults of the
// var_info table set in the object (no parameter overrides: no defaults file)
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

uint16_t AP_Param::num_param_overrides;
AP_Param::param_override *AP_Param::param_overrides;

float AP_Param::get_default_value(const AP_Param *vp, const struct GroupInfo &info)
{
    for (uint16_t i=0; i<num_param_overrides; i++) {
        if (vp == param_overrides[i].object_ptr) {
            return param_overrides[i].value;
        }
    }
    if ((info.flags & AP_PARAM_FLAG_DEFAULT_POINTER) != 0) {
        return *((float*)((ptrdiff_t)vp - info.def_value_offset));
    }
    return info.def_value;
}
