# Archive

Work that is no longer built or extended. Nothing here is imported by `lean/` or `plant/`.

| folder | what it is | toolchain | last state |
|---|---|---|---|
| `contracts/` | The contract package of the earlier work (before the full ArduCopter port): the Crazyflie plant as an ODE, the generic contract library, the hand-written float model (`FloatModel`), a snapshot of the earlier translated controller (`Translated`), and the mission, track and reach proofs. | Lean `v4.36.0-rc2`, Mathlib `v4.36.0-rc2` | tag `float32-proofs-2026-11-11` (commit `c4da4dc`), where it lives at `contracts/` |

Archived on 2026-11-16. The plant was carried over to `plant/` on Lean `v4.35.0`; everything else stays here for reference. Paths inside the archived documents still say `cpp2lean/contracts/`.
