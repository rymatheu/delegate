"""Geodesy of the gorge: the geographic origin of the world frame and the mapping between local NED offsets and latitude
and longitude.

The origin is held as integers (degrees * 1e7, mm), read from the ORIGIN line of a parameter file (origin.params: the
summit of Pikes Peak, Colorado, 38.8405556 N, 105.0441667 W, 4302 m AMSL); world ENU (0, 0, 0) is that point. One 1e-7
degree of latitude is LATLON_TO_M = 0.011131884502145034 m (ArduPilot's LATLON_TO_M), one of longitude LATLON_TO_M *
cos(origin latitude), the cosine computed once in double precision and rounded to binary32. `latlon_e7` rounds to the
nearest integer (the integers of the mission items); `latlon` and `ne` are the same formulas in double precision without
that rounding.
"""
import math
import struct
from pathlib import Path

import numpy as np

LATLON_TO_M = 0.011131884502145034


def f32(x):
    return struct.unpack("<f", struct.pack("<f", x))[0]


class Origin:
    """The origin: integers (deg * 1e7, mm) and its binary32 cosine of latitude."""

    def __init__(self, lat_e7, lon_e7, alt_mm):
        self.lat_e7, self.lon_e7, self.alt_mm = int(lat_e7), int(lon_e7), int(alt_mm)
        self.cos_lat = f32(math.cos(self.lat_e7 / 1e7 * 3.141592653589793 / 180.0))

    @classmethod
    def parse(cls, lat, lon, alt):
        """From the decimal strings of an ORIGIN line (exact decimal scaling, at most 7 and 3 decimals)."""
        def scaled(s, k):
            neg = s.startswith("-")
            ip, _, fp = s.lstrip("+-").partition(".")
            if len(fp) > k:
                raise ValueError(f"{s}: more than {k} decimals")
            n = int(ip or "0") * 10 ** k + int(fp.ljust(k, "0") or "0")
            return -n if neg else n
        return cls(scaled(lat, 7), scaled(lon, 7), scaled(alt, 3))

    @classmethod
    def from_params(cls, files, override=None):
        """The last ORIGIN line of the parameter files (later files win), or `override` (LAT LON ALT strings)."""
        if override:
            return cls.parse(*override)
        found = None
        for f in files:
            for line in Path(f).read_text().splitlines():
                ws = line.split("#", 1)[0].split()
                if ws[:1] == ["ORIGIN"]:
                    found = ws[1:4]
        if found is None:
            raise ValueError("no ORIGIN line in " + ", ".join(map(str, files)))
        return cls.parse(*found)

    def latlon(self, n, e):
        """Latitude and longitude in degrees (floats) of the NED offset (n, e) m."""
        n, e = np.asarray(n, float), np.asarray(e, float)
        return ((self.lat_e7 + n / LATLON_TO_M) / 1e7, (self.lon_e7 + e / (LATLON_TO_M * self.cos_lat)) / 1e7)

    def latlon_e7(self, n, e):
        """The integers (deg * 1e7) of the NED offset (n, e) m, rounded to nearest."""
        return (self.lat_e7 + int(round(n / LATLON_TO_M)), self.lon_e7 + int(round(e / (LATLON_TO_M * self.cos_lat))))

    def ne(self, lat_deg, lon_deg):
        """NED offset (n, e) m of a latitude and longitude in degrees (without rounding)."""
        lat_deg, lon_deg = np.asarray(lat_deg, float), np.asarray(lon_deg, float)
        return ((lat_deg * 1e7 - self.lat_e7) * LATLON_TO_M, (lon_deg * 1e7 - self.lon_e7) * LATLON_TO_M * self.cos_lat)

    @property
    def alt_m(self):
        return self.alt_mm / 1000.0
