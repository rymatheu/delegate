/* cpp2lean reference vehicle: stand-in for libraries/AP_HAL_SITL/CANSocketIface.h (included by
   AP_CANManager.cpp on the SITL board). SITL declares two CAN interfaces (HAL_NUM_CAN_IFACES 2) that
   AP_CANManager::init allocates only for a bus with a driver configured (CAN_Pn_DRIVER, default 0);
   the lock-step HAL has no CAN bus, so the interface class only has to exist. */
#pragma once
#include <SITL/SITL.h>
#include <AP_HAL/CANIface.h>
#include <AP_HAL_SITL/AP_HAL_SITL_Namespace.h>

class HALSITL::CANIface : public AP_HAL::CANIface {
public:
    explicit CANIface(int index) : num(index) {}
    bool init(const uint32_t bitrate) override { return false; }
    bool is_initialized() const override { return false; }
    int8_t get_iface_num() const override { return num; }
    bool add_to_rx_queue(const CanRxItem &rx_item) override { return false; }
private:
    int num;
};
typedef HALSITL::CANIface HAL_CANIface;
