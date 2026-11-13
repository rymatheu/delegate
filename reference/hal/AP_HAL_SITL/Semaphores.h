/* cpp2lean reference vehicle: stand-in for libraries/AP_HAL_SITL/Semaphores.h, which AP_HAL/board/sitl.h
   includes for HAL_Semaphore. The lock-step HAL runs one thread (PORT-PLAN.md 4.11): a semaphore is
   always free, take succeeds, give does nothing. */
#pragma once

#include <AP_HAL/AP_HAL_Boards.h>
#include <AP_HAL/AP_HAL_Macros.h>
#include <AP_HAL/Semaphores.h>
#include <AP_HAL_SITL/AP_HAL_SITL_Namespace.h>

class HALSITL::Semaphore : public AP_HAL::Semaphore {
public:
    Semaphore() {}
    bool give() override { return true; }
    bool take(uint32_t timeout_ms) override { return true; }
    bool take_nonblocking() override { return true; }
    void take_blocking() override {}
    bool check_owner() { return true; }
};

class HALSITL::BinarySemaphore : public AP_HAL::BinarySemaphore {
public:
    BinarySemaphore(bool initial_state=false) : AP_HAL::BinarySemaphore(initial_state), state(initial_state) {}
    bool wait(uint32_t timeout_us) override { bool r = state; state = false; return r; }
    bool wait_blocking() override { state = false; return true; }
    void signal() override { state = true; }
private:
    bool state;
};
