/* cpp2lean Phase 3: the GPS's serial port in the estimator's World (est_uart.h). */
#include "est_uart.h"

// lockstep.cpp's UART::_begin for an unconnected port: a zero call changes nothing; a baud rate is kept
void EstUART::_begin(uint32_t b, uint16_t rxSpace, uint16_t txSpace)
{
    if (b == 0 && rxSpace == 0 && txSpace == 0) {
        return;
    }
    if (b != 0) {
        baud = b;
    }
    initialized = true;
}
