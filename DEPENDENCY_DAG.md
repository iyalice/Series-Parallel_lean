# Canonical dependency DAG

## Traditional graph-semantics branch

```text
Mathlib SimpleGraph metric
└─ GraphSemantics.Basic
   ├─ TraditionalDistance
   ├─ TraditionalResistance
   └─ Realization + SPNetwork syntax
      ├─ DistanceBridge + FinitePaths
      │  ├─ recursive shortest path -> unrestricted graph walk
      │  ├─ vertex-level lower-bound certificate
      │  └─ traditionalDistance_realize
      └─ ResistanceBridge + FiniteFlows
         ├─ recursive flow -> conventional signed current
         ├─ generalized_thomson for every value and current
         ├─ resistance_isLeast_energySet
         └─ traditionalResistance_realize
            DistanceBridge + ResistanceBridge + existing RandomModel
            └─ GraphSemantics.RandomModel
               ├─ two samplewise equalities
               ├─ graph Z/X, moments, normalized sequences
               └─ graph candidate limits
                  └─ GraphSemantics.StatementContract
                     └─ GraphSemantics.MainTheorems
                        └─ GraphSemantics aggregate
                           └─ MainText aggregate
                              └─ MainTextPublicAPI
```

`Basic`, `TraditionalDistance`, and `TraditionalResistance` have no dependency on the recursive
model. `Realization` reads only syntax constructors. The bridge modules are the first point where a
traditional quantity and a recursive evaluator occur together.

## Scalar analytic proof graph

```text
common random model and recursion
├─ finite paths + finite flows
│  └─ first-moment submultiplicativity / Fekete
│     ├─ normalized second moment
│     └─ Jensen gap + center tracking
│        └─ remaining parameter ranges
│           ├─ distanceGamma_half_eq_zero -> logarithmicSpeeds
│           └─ distanceGamma_half_eq_zero -> firstMomentLogarithmicRates
├─ exact density CDF regions
│  └─ generalized-inverse coupling / CDF order
├─ diffusion coefficient closed form
└─ appendix profile facade -> MI01
   ├─ weighted consistency -> upper global barrier -------------------+
   └─ weighted consistency -> hard-edge barrier -> lower iteration ---+
      parameter squeeze + cube/cube-root map + BVP bridge <-----------+
      └─ resistanceSpeedNearCritical
```

Graph-facing contracts are equivalent to scalar contracts and transport this analytic DAG. They
do not copy any probability, CDF, barrier, or near-critical module.

## Axiom leaves

```text
distanceGamma_half_eq_zero
├─ logarithmicSpeeds
├─ firstMomentLogarithmicRates
├─ graphLogarithmicSpeeds
└─ graphFirstMomentLogarithmicRates

MI01_global_peano_on_compact_interval
├─ resistanceSpeedNearCritical
└─ graphResistanceSpeedNearCritical
```

Neither axiom reaches the deterministic bridges or the two samplewise equalities. The resistance
near-critical branch remains separate from the critical-distance interface, as confirmed by kernel
fingerprints.
