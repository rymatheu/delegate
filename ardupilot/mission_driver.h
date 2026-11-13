// What the C++ World driver of the AP_Mission difftest (ardupilot/Mission.json) includes before the World objects of
// ardupilot/unity_mission.cpp (whose definitions difftest.py copies after the unity's last #include): AP_Mission's
// header and what the harness uses. AP_Mission.cpp, StorageManager.cpp, AP_ParamT.cpp, Location.cpp, location.cpp and
// AP_Math.cpp are compiled as they are (Mission.json "cxx_sources"), the environment by ardupilot/mission_env.cpp.
#include <AP_Mission/AP_Mission.h>
#include <StorageManager/StorageManager.h>
extern const AP_HAL::HAL& hal;
