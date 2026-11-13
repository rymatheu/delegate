// cpp2lean reference vehicle: print ArduPilot's earth magnetic field (AP_Declination tables) at a
// location, for the harness's compass model (sim/lockstep_sensors.py). Usage: magfield LAT LON
#include <AP_Declination/AP_Declination.h>
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv)
{
    if (argc != 3) { fprintf(stderr, "usage: magfield LAT LON\n"); return 2; }
    float intensity, declination, inclination;
    if (!AP_Declination::get_mag_field_ef(atof(argv[1]), atof(argv[2]), intensity, declination, inclination)) {
        return 1;
    }
    printf("intensity_gauss %.9g declination_deg %.9g inclination_deg %.9g\n", intensity, declination, inclination);
    return 0;
}
