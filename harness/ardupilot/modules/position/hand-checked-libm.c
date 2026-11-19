// The three libm values the hand-checked case needs (macOS libm, as the module links):
// accel_mss_to_angle_rad(a) = atanf(a / GRAVITY_MSS) (AP_Math/control.cpp:838), in binary32.
#include <math.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h>
static unsigned bits(float f) { uint32_t u; memcpy(&u, &f, 4); return u; }
int main(void) {
    const float g = 9.80665f;
    const float a1 = 8.25048828125f, a2 = 0.2509765625f;
    printf("atanf(%.9g/g)=0x%08x atanf(-%.9g/g)=0x%08x\n", a1, bits(atanf(a1 / g)), a1, bits(atanf(-a1 / g)));
    printf("atanf(%.9g/g)=0x%08x atanf(-%.9g/g)=0x%08x\n", a2, bits(atanf(a2 / g)), a2, bits(atanf(-a2 / g)));
    printf("tanf(0.7853982f)=0x%08x\n", bits(tanf(0.7853982f)));
    return 0;
}
