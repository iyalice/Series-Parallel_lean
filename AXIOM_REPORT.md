# Axiom and trust report

Audit date: 2026-08-27. The project has **2 external mathematical facts represented by 2 Lean
`axiom` declarations**. The authorized optional diffusion fallback E-a was not used.

| Class | Declaration | Exact role | Main-theorem reachability |
|---|---|---|---|
| core appendix | `SeriesParallel.ManualInterfaces.MI01_global_peano_on_compact_interval` | generic compact-interval Peano existence under linear growth | third theorem only |
| core literature | `SeriesParallel.MainText.distanceGamma_half_eq_zero` | `gammaD (1 / 2) = 0` | first and second theorem only |

The diffusion identity
`diffusionCoefficient_eq_two_mul_zetaThree` and the resulting
`diffusionMainInput_kappa_eq` are internal theorems, not interfaces.

## Source-facing fingerprints

All three also use the standard kernel principles `propext`, `Classical.choice`, and
`Quot.sound`.

| Theorem | Project axiom fingerprint |
|---|---|
| `logarithmicSpeeds` | `{distanceGamma_half_eq_zero}` |
| `firstMomentLogarithmicRates` | `{distanceGamma_half_eq_zero}` |
| `resistanceSpeedNearCritical` | `{MI01_global_peano_on_compact_interval}` |

The third theorem does not reach the distance input, and the first two do not reach MI01.

The audit manifests are generated only while running the reproducible commands and removed
afterward. The lexical auditor reports `PASS (69 files, 2 axiom declarations)` and no proof
escape; the fingerprint auditor reports `PASS (2 declarations, 3 theorem fingerprints)`.

The remaining distance near-critical literature citation is not needed for these three theorems,
is not encoded as a Lean declaration, and is outside the project trust boundary. The current SPA
manuscript no longer contains the former critical-resistance citation display.
