// stubs_param.cpp: parameter storage.
//
//   symbol                                   why it is outside the stage, and what stands in
//   AP_Param::setup_object_defaults          loads defaults from var_info tables (AC_Loiter's
//                                            constructor, AC_Loiter.cpp:107). No-op: the adapter
//                                            sets every AP_Param member the step reads from the
//                                            parameter record afterwards.
#include <AP_Param/AP_Param.h>

void AP_Param::setup_object_defaults(const void *object_pointer, const struct GroupInfo *group_info)
{
}
