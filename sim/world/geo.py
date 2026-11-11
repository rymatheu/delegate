"""Geodesy of the gorge session: the controller's mapping between local NED offsets and latitude and
longitude, and the Web Mercator tile arithmetic of QGroundControl 5.1.5.

leanfc (Leanfc/Mavlink/Format.lean `toNE`, `toLatLon`; Shell/Link.lean `makeOrigin`): the origin is
held as integers (degrees * 1e7, mm); one 1e-7 degree of latitude is LATLON_TO_M = 0.011131884502145034 m
(ArduPilot's LATLON_TO_M), one of longitude LATLON_TO_M * cos(origin latitude), the cosine computed
once in double precision and rounded to binary32. The controller then works in binary32 and rounds
latitude and longitude to integers; the functions here are the same formulas in double precision
without that rounding (the difference is below 1e-7 degree, about 1 cm).

QGroundControl (src/QtLocationPlugin/Providers/MapProvider.cpp `long2tileX`, `lat2tileY`,
`tileX2long`, `tileY2lat`; QGeoTiledMappingManagerEngineQGC.cpp: 256-pixel tiles, zoom 2 to
QGC_MAX_MAP_ZOOM = 23): spherical Web Mercator. A tile pixel (px, py) of tile (x, y) at zoom z covers
the global pixel square [256 x + px, 256 x + px + 1) x [256 y + py, ...) of a 256 * 2^z map.
"""
import math
import struct
from pathlib import Path

import numpy as np

LATLON_TO_M = 0.011131884502145034
TILE = 256
MAX_ZOOM = 23


def f32(x):
    return struct.unpack("<f", struct.pack("<f", x))[0]


class Origin:
    """The controller's origin: integers (deg * 1e7, mm) and its binary32 cosine of latitude."""

    def __init__(self, lat_e7, lon_e7, alt_mm):
        self.lat_e7, self.lon_e7, self.alt_mm = int(lat_e7), int(lon_e7), int(alt_mm)
        self.cos_lat = f32(math.cos(self.lat_e7 / 1e7 * 3.141592653589793 / 180.0))

    @classmethod
    def parse(cls, lat, lon, alt):
        """From the decimal strings of an ORIGIN line (as Leanfc/ParamFile.lean parseScaled)."""
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
        """The last ORIGIN line of the parameter files (later files win, as the controller merges them),
        or `override` (LAT LON ALT strings, the harness's --origin)."""
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
        """The integers the controller reports for (n, e) (`toLatLon`, rounded to nearest)."""
        return (self.lat_e7 + int(round(n / LATLON_TO_M)), self.lon_e7 + int(round(e / (LATLON_TO_M * self.cos_lat))))

    def ne(self, lat_deg, lon_deg):
        """NED offset (n, e) m of a latitude and longitude in degrees (`toNE` without rounding)."""
        lat_deg, lon_deg = np.asarray(lat_deg, float), np.asarray(lon_deg, float)
        return ((lat_deg * 1e7 - self.lat_e7) * LATLON_TO_M, (lon_deg * 1e7 - self.lon_e7) * LATLON_TO_M * self.cos_lat)

    @property
    def alt_m(self):
        return self.alt_mm / 1000.0


# --- QGroundControl's tile arithmetic (MapProvider.cpp), and its fractional form ------------------

def long2tileX(lon, z):
    return int(math.floor((lon + 180.0) / 360.0 * 2.0 ** z))


def lat2tileY(lat, z):
    return int(math.floor((1.0 - math.log(math.tan(lat * math.pi / 180.0) + 1.0 / math.cos(lat * math.pi / 180.0)) / math.pi) / 2.0 * 2.0 ** z))


def tileX2long(x, z):
    return x / 2.0 ** z * 360.0 - 180.0


def tileY2lat(y, z):
    n = math.pi - 2.0 * math.pi * y / 2.0 ** z
    return math.degrees(math.atan(math.sinh(n)))


def global_pixel(lat, lon, z):
    """Fractional global pixel (X, Y) of a latitude and longitude at zoom z (the same formulas)."""
    lat, lon = np.asarray(lat, float), np.asarray(lon, float)
    X = (lon + 180.0) / 360.0 * 2.0 ** z * TILE
    Y = (1.0 - np.log(np.tan(np.radians(lat)) + 1.0 / np.cos(np.radians(lat))) / np.pi) / 2.0 * 2.0 ** z * TILE
    return X, Y


def pixel_latlon(X, Y, z):
    """Latitude and longitude of fractional global pixel coordinates at zoom z."""
    X, Y = np.asarray(X, float), np.asarray(Y, float)
    lon = X / (TILE * 2.0 ** z) * 360.0 - 180.0
    lat = np.degrees(np.arctan(np.sinh(np.pi - 2.0 * np.pi * Y / (TILE * 2.0 ** z))))
    return lat, lon


def meters_per_pixel(lat, z):
    return 2 * math.pi * 6378137.0 * math.cos(math.radians(lat)) / (TILE * 2.0 ** z)
