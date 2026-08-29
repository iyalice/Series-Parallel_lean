# External hypotheses

The external trust budget is **2 facts**, below the allowed maximum of 6. Fewer interfaces were
preferred throughout; E-a was not triggered.

## Core interfaces

1. `SeriesParallel.ManualInterfaces.MI01_global_peano_on_compact_interval`
   is a generic Peano existence statement for a continuous scalar field on a compact time
   interval with linear growth. Appendix shooting/profile existence consumes it. The closed
   scalar theorem `resistanceSpeedNearCritical` and its graph-facing counterpart
   `GraphSemantics.graphResistanceSpeedNearCritical` inherit it.

2. `SeriesParallel.MainText.distanceGamma_half_eq_zero : gammaD (1 / 2) = 0`
   is the sole literature input needed by `logarithmicSpeeds` and
   `firstMomentLogarithmicRates`; the corresponding graph-facing wrappers inherit the same
   fingerprint. Parameter monotonicity, a.s./L1 convergence, critical resistance, and all other
   ranges are internal consequences.

## Out-of-scope literature statements

The distance near-critical comparison is not needed for the three requested main theorems. It is
therefore not encoded as a Lean declaration and contributes no project axiom. Its TeX label
remains in `SOURCE_MAP.md` solely as an out-of-scope source citation. The current SPA manuscript
no longer contains the former critical-resistance distributional-limit display.

`ExternalInterfaces.lean` remains an empty historical compatibility boundary. The active core
literature interface is `LiteratureInterfaces.lean`.
