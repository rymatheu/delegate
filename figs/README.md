# Figures and tables

Every figure and table of the paper's staging folder (`/Users/ryan/Research/delegate/staging/figs/*.tex`
and `staging/tabs/*.tex`, archive and previews excluded) as a cropped standalone PDF in `pdf/`, with
the `.tex` sources and the PNGs they include in `src/` (copied from staging on 2026-11-05).
`build_pdfs.sh` regenerates the PDFs from `src/`:

```
figs/build_pdfs.sh              # every figure and table
figs/build_pdfs.sh montecarlo-3d types
```

Figures are typeset in the standalone class over acmart (sigconf) with the union of the preambles
their headers list (TikZ with the `arrows.meta`, `calc`, `positioning`, `fit` and `backgrounds`
libraries; graphicx and amssymb come with acmart; booktabs, array), the PNGs and `\input` files found
in `src/`; the two that size their image to `\linewidth` are set 8.2 cm wide, the width the
figures are made for. Tables are typeset in the same class with the `table` float as a box of the
sigconf line width (241.15 pt), so their caption and rules are as in the paper. Work files go to
`.build/`. Every PDF builds with 0 errors and 0 overfull boxes. Paths below are in cpp2lean unless
named in full; a generator writes every coordinate of its figure (no hand-edited coordinates), a
hand-drawn diagram has none.

| PDF | size | content | data | made by |
|---|---|---|---|---|
| `overview-D.pdf` | 8.20 x 5.03 cm | The contract drawn in the flight's own scene: the stroboscopic flight (33 instants) with the box A, the 2 m ceiling and the 0.25 m corridor projected through the camera, and the code card of `AC_PID::update_i`'s translation. | the re-flight of `sim/out/lean-course-1ms`, `sim/spec/mission-course.json`, `ardupilot/out/AC_PID/AC_PID_lib.lean`; image `src/overview-D-strobe.png` | `sim/figs/render_overview.py` |
| `flight-strobe.pdf` | 8.20 x 5.32 cm | Stroboscopic render of the 1 m/s course (instants every 0.5 s) with labels. | re-flight of the course with `copter_lean`; image `src/flight-strobe.png` | `sim/figs/render_strobe.py` |
| `flight-filmstrip.pdf` | 8.20 x 1.15 cm | Six instants of the course flight as a filmstrip. | the same re-flight; image `src/flight-filmstrip.png` | `sim/figs/render_strobe.py` |
| `flight-path.pdf` | 8.04 x 6.60 cm | Top view and altitude against distance of the course flight, Lean over C++, with the desired position. | `sim/out/lean-course-1ms`, `sim/out/ref-course-1ms` (`flight.csv`, `summary.txt`) | `sim/figs/make_path.py` |
| `flight-timeseries.pdf` | 8.18 x 6.54 cm | Position, attitude, heading and actuators of the course flight against time, with their targets. | `sim/out/lean-course-1ms/flight.csv`, `ref-course-1ms` | `sim/figs/make_timeseries.py` |
| `flight-parity.pdf` | 8.18 x 3.61 cm | Actuator m1 of both vehicles and the count of differing actuators and traced values per tick (0 throughout). | `sim/out/{lean,ref}-course-1ms`, replays with `--exact --trace --bits` | `sim/figs/make_parity.py` |
| `parity-trace.pdf` | 8.07 x 7.21 cm | Parity from the traces: three traced signals of both vehicles, a raster of differing bits for all 22 values per tick (0 of 22 x 7797), and the contrast of a mutated Lean vehicle (single-precision trig in `Quaternion::from_axis_angle`), first differing at tick 541, actuators from tick 1295. | `sim/out/lean-course-1ms/inputs.txt` replayed through `copter_lean`, `copter_ref` and `build/mutated/lean` | `sim/figs/make_parity_trace.py` |
| `montecarlo-paths.pdf` | 8.04 x 6.90 cm | The 200 Monte Carlo flights (starts uniform in A, any heading; Lean and C++ identical) in top view and altitude against distance along the path, over the corridor, the box and the ceiling. | `sim/out/montecarlo/` (`summary.csv`, `runs/`), `sim/spec/mission-course.json` | `sim/figs/make_montecarlo_paths.py` |
| `montecarlo-margins.pdf` | 8.17 x 6.39 cm | The margins of the contract over the 200 runs as dot strips against their bounds: ceiling, corridor, the slack of each leg, the hold. | `sim/out/montecarlo/summary.csv` | `sim/figs/make_montecarlo_margins.py` |
| `montecarlo-3d.pdf` | 8.20 x 4.81 cm | The 200 trajectories in perspective (the overview's camera) and the takeoff region enlarged 5.95 times with the starts, their headings and the climbs into w0. | `sim/out/montecarlo/`, `sim/out/lean-course-1ms` | `sim/figs/make_montecarlo_3d.py` |
| `montecarlo-noise.pdf` | 8.00 x 6.43 cm | The 200 flights under bounded sensing noise L2 (position ±2 cm, velocity ±5 cm/s), the highest level on which all runs pass, in top view, and the spread over 30 s. | `sim/out/montecarlo-noise-L2/`, `sim/out/lean-course-1ms` | `sim/figs/make_montecarlo_noise.py` |
| `oracle-diff.pdf` | 7.57 x 2.77 cm | Actuator difference against the C++ oracle over the flight for the single-precision-trig diagnostic variant and the hand port's replay. | `src/oracle-diff-data.tex`, from the oracle comparison files (`oracle-nosincos`, `oracle-diag-floattrig`, `port-replay`) | data file written separately (see its header); drawing by hand |
| `proofgraph.pdf` | 8.18 x 6.46 cm | Dependency graph of the mission theorem: trusted base and hypotheses, foundations, lemmas, contracts, with the proof status of each node. | the axiom audit of `contracts/` (`AxiomCheck.lean`, `#print axioms`) | `contracts/proofgraph.py` |
| `pipeline.pdf` | 8.20 x 6.10 cm | The whole procedure: translation, the proof lane (M ∩ A ⊆ G checked in Lean) and the execution lane (both binaries on the same samples). | none | hand-drawn TikZ |
| `translator.pdf` | 12.70 x 3.39 cm | The stages of cpp2lean, from the C++ sources to the Lean model. | none | hand-drawn TikZ |
| `harness.pdf` | 8.19 x 6.20 cm | The lock-step flights of the two vehicles and the per-tick comparison. | none (`sim/PROTOCOL.md`) | hand-drawn TikZ |
| `architecture.pdf` | 7.81 x 3.65 cm | The ported control cascade: AC_WPNav, AC_PosControl, AC_AttitudeControl, the rate loop, AP_MotorsMatrix. | none | hand-drawn TikZ |
| `plant.pdf` | 7.96 x 3.68 cm | The plant model and its ports to the controller. | none | hand-drawn TikZ |
| `params.pdf` | 8.55 x 21.32 cm | Table: vehicle, simulation, controller (tuned values with the defaults), mission, build and results of the case study. | `sim/params/*.txt`, `--print-params` of both vehicles, `sim/BENCH.md`, the flights' summaries | `sim/figs/make_params.py` |
| `params-corner.pdf` | 8.55 x 16.76 cm | Table: the same for the earlier corner mission. | the earlier corner mission's parameters and runs (named in its header) | named in its header |
| `types.pdf` | 8.55 x 4.75 cm | Table: the type mapping of cpp2lean, each C++ type to the Lean type of the same representation. | `README.md`, "Mapping, as implemented" | by hand |
