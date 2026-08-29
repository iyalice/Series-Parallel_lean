# Axiom and trust report

Audit date: 2026-08-29

The repository contains exactly **two project `axiom` declarations**. The traditional graph
definitions, realization, deterministic bridges, and samplewise bridges add no project assumption.

## Project assumptions

| Class | Fully qualified declaration | Exact role | Reachability |
|---|---|---|---|
| literature | `SeriesParallel.MainText.distanceGamma_half_eq_zero` | `gammaD (1 / 2) = 0` | scalar and graph logarithmic-speed and first-moment-rate theorems |
| appendix interface | `SeriesParallel.ManualInterfaces.MI01_global_peano_on_compact_interval` | compact-interval Peano existence under linear growth | scalar and graph near-critical resistance theorem |

`diffusionCoefficient_eq_two_mul_zetaThree` is proved internally and is not an interface.

## Exact fingerprints

The table removes Lean's standard principles `propext`, `Classical.choice`, and `Quot.sound` from
each `#print axioms` result.

| Declaration | Exact project-axiom fingerprint |
|---|---|
| `SeriesParallel.MainText.SPNetwork.traditionalDistance_realize` | empty |
| `SeriesParallel.MainText.SPNetwork.traditionalResistance_realize` | empty |
| `SeriesParallel.MainText.GraphSemantics.graphDistanceValue_eq_distanceValue` | empty |
| `SeriesParallel.MainText.GraphSemantics.graphResistanceValue_eq_resistanceValue` | empty |
| `SeriesParallel.MainText.logarithmicSpeeds` | `{SeriesParallel.MainText.distanceGamma_half_eq_zero}` |
| `SeriesParallel.MainText.GraphSemantics.graphLogarithmicSpeeds` | `{SeriesParallel.MainText.distanceGamma_half_eq_zero}` |
| `SeriesParallel.MainText.firstMomentLogarithmicRates` | `{SeriesParallel.MainText.distanceGamma_half_eq_zero}` |
| `SeriesParallel.MainText.GraphSemantics.graphFirstMomentLogarithmicRates` | `{SeriesParallel.MainText.distanceGamma_half_eq_zero}` |
| `SeriesParallel.MainText.resistanceSpeedNearCritical` | `{SeriesParallel.ManualInterfaces.MI01_global_peano_on_compact_interval}` |
| `SeriesParallel.MainText.GraphSemantics.graphResistanceSpeedNearCritical` | `{SeriesParallel.ManualInterfaces.MI01_global_peano_on_compact_interval}` |

The graph wrapper fingerprints exactly match their scalar counterparts. The deterministic and
samplewise bridges contain no project axiom in their transitive dependency closure.

## Structural trust checks

- `Basic.lean`, `TraditionalDistance.lean`, and `TraditionalResistance.lean` cannot see the
  recursive evaluator modules through their imports.
- `Realization.lean` imports the network syntax, but its realization, endpoint, and embedding
  definition bodies contain neither `.distance` nor `.resistance`.
- No graph-semantics source contains `sorry`, `admit`, `unsafe`, or an `axiom` declaration.
- The project placeholder audit reports `PASS (80 files, 2 axiom declarations)`.
- `SeriesParallel/GraphSemanticsAudit.lean` prints every bridge, wrapper, and scalar fingerprint
  listed above.

The accepted base is Lean 4.32.1, mathlib v4.32.1 at commit
`520045ab14e26149ee970e2e617ca04b09bde5d6`, the Lean kernel, and the two listed interfaces.
