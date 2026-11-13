/* cpp2lean Phase 3: the GPS's serial port in the estimator's World (README.md "Phase 3: AP_InertialSensor, AP_GPS and
   AP_NavEKF_Source").

   AP_GPS detects its SITL back end only on a port that AP_SerialManager::find_serial found for the GPS protocol
   (AP_GPS.cpp:672: no port, no detection); it then reads the port's baud rate, (re)starts the port at its probe baud
   and sets the flow control. In the reference vehicle the port is the lock-step HAL's SERIAL3, an unconnected port
   of reference/hal/lockstep.cpp's UART class: no bytes in or out, a baud rate that `begin` sets. EstUART is that
   class's logic for an unconnected port, as a class of ArduPilot's AP_HAL::UARTDriver interface, so that the
   translation runs the GPS's port calls as code of the World (as est_scheduler.h does for the scheduler). Both
   sides of a difftest compile this file; it is not part of the reference vehicle (copter_ref keeps lockstep.cpp). */
#pragma once

#include <AP_HAL/AP_HAL.h>

class EstUART : public AP_HAL::UARTDriver {
public:
    bool is_initialized() override { return initialized; }
    bool tx_pending() override { return false; }
    uint32_t txspace() override { return 0; }
    uint32_t bw_in_bytes_per_second() const override { return baud / 10; }
    uint32_t get_baud_rate() const override { return baud; }
    // no byte ever arrives: AP_HAL::UARTDriver::read() through read_locked() and _read() gives -1, as here (the
    // read monitor of UARTDriver.cpp:69 is fed only by successful reads)
    int16_t read(void) override { return -1; }

protected:
    void _begin(uint32_t b, uint16_t rxSpace, uint16_t txSpace) override;
    size_t _write(const uint8_t *buffer, size_t size) override { return 0; }
    ssize_t _read(uint8_t *buffer, uint16_t count) override { return -1; }
    void _end() override {}
    void _flush() override {}
    uint32_t _available() override { return 0; }
    bool _discard_input() override { return true; }

private:
    bool initialized;
    uint32_t baud = 115200;
};

// the object is defined where the World is (ardupilot/unity_sensors.cpp: `EstUART est_uart;`)
extern EstUART est_uart;
