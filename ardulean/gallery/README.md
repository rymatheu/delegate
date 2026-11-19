# Gallery

Every flight here was flown by the ArduLean executable in the simulator. Click a picture with a play mark (▶) to open its video.

## Flights

### Two X500s side by side

[![Two X500s abreast in the gorge](images/formation-abreast.png)](videos/formation-abreast.mp4)

▶ [formation-abreast.mp4](videos/formation-abreast.mp4). Two X500s fly the gorge 1.8 m apart. Each one is its own copy of the ArduLean executable. The lower strip shows each vehicle's forward camera and thermal camera.

### Two X500s staggered

[![Two X500s staggered in the gorge](images/formation-staggered.png)](videos/formation-staggered.mp4)

▶ [formation-staggered.mp4](videos/formation-staggered.mp4). The second X500 flies behind and to the right of the first, with its nose pointing backward, so its cameras watch the route behind the pair.

### One X500 at speed

[![One X500 in the gorge](images/gorge-chase.png)](videos/gorge-scurve.mp4)

▶ [gorge-scurve.mp4](videos/gorge-scurve.mp4). One X500 flies the gorge on straight legs with blended corners, reaching 9 m/s.

## The gorge

The route from above, with the flown track in red:

![The gorge from above with one flown track](images/gorge-overview.png)

Both vehicles' tracks on the side-by-side flight:

![The gorge from above with two flown tracks](images/formation-overview.png)

What the vehicle's own cameras see, color and thermal:

| forward camera | thermal camera |
|---|---|
| ![Onboard forward camera](images/gorge-onboard-camera.png) | ![Onboard thermal camera](images/gorge-onboard-thermal.png) |

The pair landing at the far end:

![Two X500s landing](images/formation-landing.png)

## How ArduLean is put together

From the C++ source to a flight:

![From ArduCopter to a flight in the simulator](architecture.png)

How the proofs are layered on the code and on the vehicle's equations of motion:

![How the proofs are layered](proof-structure.png)

The two figures are drawn by `gallery/figures.py`.
