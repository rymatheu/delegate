// stubs_param.cpp: parameter storage.
//
//   symbol                                   why it is outside the stage, and what stands in
//   AP_Param::setup_object_defaults          loads defaults from var_info tables. No-op: the
//                                            adapter sets every AP_Param member the step reads.
//   AP_Param::save, find_key_by_pointer,     EEPROM and parameter conversion; reached only from
//   convert_old_parameters(_scaled)          convert_parameters (not called) and the PIDs'
//                                            save_gains (not called). Abort.
#include <AP_Param/AP_Param.h>

void AP_Param::setup_object_defaults(const void *object_pointer, const struct GroupInfo *group_info)
{
}

void AP_Param::save(bool force_save)
{
    unreachable("AP_Param::save");
}
