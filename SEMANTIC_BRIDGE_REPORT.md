# Traditional graph-semantics bridge report

Status: **COMPLETE**
Audit date: 2026-08-29

## Scope

The formalization supplies an evaluator-independent finite multigraph semantics for every
`SPNetwork`, proves equality with the recursive distance and resistance evaluators, and transports
the resulting samplewise equalities to graph-facing versions of the three principal theorems. The
probabilistic, moment, speed, and near-critical arguments remain in the existing scalar proof
graph.

The two central theorems are:

- `SeriesParallel.MainText.SPNetwork.traditionalDistance_realize`;
- `SeriesParallel.MainText.SPNetwork.traditionalResistance_realize`.

## Acceptance table

| # | Requirement | Status | Lean evidence |
|---:|---|:---:|---|
| 1 | Explicit finite two-terminal multigraph, distinct terminals, and retained edge multiplicity | PASS | `GraphSemantics.TwoTerminalMultigraph`, its four finite/decidable instances, `source_ne_sink`, `edgeCard`, and `SPNetwork.twoParallel_physicalEdges_distinct` |
| 2 | Traditional distance and resistance are dependency-independent of recursive evaluators | PASS | `Basic.lean`, `TraditionalDistance.lean`, and `TraditionalResistance.lean` import only their lower graph layer and Mathlib; their definitions mention no `SPNetwork` symbol |
| 3 | Traditional distance equals `N.distance` for every network | PASS | `SPNetwork.traditionalDistance_realize` |
| 4 | Kirchhoff feasibility is vertex-wise and permits signed currents and circulations | PASS | `TwoTerminalMultigraph.Current`, `divergence`, `throughFlowDemand`, and `IsThroughFlow`; currents have type `Edge -> Real` with no sign restriction |
| 5 | Thomson resistance is independently defined as an energy infimum | PASS | `unitEnergy`, `energySet`, `HasUnitFlow`, `traditionalResistance`, `unitEnergy_nonneg`, and `energySet_bddBelow` |
| 6 | Traditional resistance equals `N.resistance` for every network | PASS | `SPNetwork.generalized_thomson`, `resistance_isLeast_energySet`, and `traditionalResistance_realize` |
| 7 | Both random quantities have samplewise bridge equalities | PASS | `GraphSemantics.graphDistanceValue_eq_distanceValue` and `graphResistanceValue_eq_resistanceValue` |
| 8 | Parallel physical-edge multiplicity, distance, and resistance regressions | PASS | `SPNetwork.realize_twoParallel_edgeCard`, `twoParallel_physicalEdges_distinct`, `traditionalDistance_twoParallel`, and `traditionalResistance_twoParallel` |
| 9 | Graph-semantics files contain no proof escapes; the project has exactly two declared project axioms | PASS | Placeholder audit: `PASS (80 files, 2 axiom declarations)`; no `sorry`, `admit`, `unsafe`, or `axiom` occurs in the graph-semantics files |
| 10 | The three scalar main-theorem fingerprints have the required exact values | PASS | `logarithmicSpeeds` and `firstMomentLogarithmicRates` use only `distanceGamma_half_eq_zero`; `resistanceSpeedNearCritical` uses only `MI01_global_peano_on_compact_interval` |
| 11 | The three graph-facing wrappers have the required exact fingerprints | PASS | `graphLogarithmicSpeeds`, `graphFirstMomentLogarithmicRates`, and `graphResistanceSpeedNearCritical`; see the fingerprint table below |
| 12 | Deterministic and samplewise bridges use no project axiom | PASS | All four `#print axioms` results contain only `propext`, `Classical.choice`, and `Quot.sound` |
| 13 | Required builds and import smoke checks succeed | PASS | Graph-semantics aggregate: 8,726 jobs; `MainTextPublicAPI`: 8,728 jobs; project build succeeds; external smoke import and five `#check` commands succeed |
| 14 | The v5 semantic map is limited to the audited graph-semantic front end | PASS | `V5_SEMANTICS_MAP.md` covers only v5 section 1.1, section 2.1, and Lemma 3.1 |

## Declaration evidence

### Traditional graph layer

`SeriesParallel.MainText.GraphSemantics.TwoTerminalMultigraph` bundles finite vertex and physical
edge types, decidable equality, oriented endpoint maps, and distinct source and sink vertices. The
edge type is retained when the undirected `simpleShadow` is formed, so parallel edges collapse only
for unweighted adjacency and never for current or energy.

`traditionalDistance` is `SimpleGraph.dist` between the two terminals. Reachability is proved for
every realization by `SPNetwork.realize_reachable`, using
`SPNetwork.Path.toRealizeWalk`. The reverse distance inequality is certified for arbitrary walks
by `SPNetwork.vertexLevel` and `SPNetwork.distance_le_realize_walk_length`; it is not restricted to
recursive paths.

`TwoTerminalMultigraph.traditionalResistance` is `sInf energySet`. Feasibility is the full
vertex-wise divergence equation. `SPNetwork.generalized_thomson` quantifies over every real flow
value and every conventional signed current, so its lower bound also covers currents containing
circulation. `SPNetwork.Flow.toCurrent` is a one-way bridge used for attainment; no inverse claim
from conventional currents to recursive flows is made.

### Realization and deterministic bridges

The realization uses tagged recursive types:

- `SPNetwork.PhysicalEdge`: `PUnit` at a leaf and a disjoint sum at both series and parallel gates;
- `SPNetwork.InternalVertex`: a new join tag at each series gate and disjoint child tags;
- `SPNetwork.RealizedVertex`: two boundary tags plus the internal-vertex type;
- `SPNetwork.realize`: the bundled traditional two-terminal multigraph.

The structural invariants are exposed by `realize_noLoops`, `realize_edgeCard`, the endpoint
projection lemmas, and the child-embedding lemmas. A symbol-use audit of the realization
definitions confirms that their bodies contain neither `.distance` nor `.resistance`.

The exact bridge statements are:

```text
SPNetwork.traditionalDistance_realize (network : SPNetwork) :
  traditionalDistance network.realize = network.distance

SPNetwork.traditionalResistance_realize (network : SPNetwork) :
  network.realize.traditionalResistance = network.resistance
```

### Random transport and public theorems

`graphDistanceValue` and `graphResistanceValue` first realize the random network and then apply the
independent traditional quantity. Their samplewise equalities support `graphZ`, `graphX`, graph
moments, normalized graph sequences, and the independent candidates `graphVD`, `graphVR`,
`graphGammaD`, and `graphGammaR`. The three graph statement contracts contain those graph-defined
objects syntactically. Their equivalence theorems transport the already-checked scalar results to:

- `GraphSemantics.graphLogarithmicSpeeds`;
- `GraphSemantics.graphFirstMomentLogarithmicRates`;
- `GraphSemantics.graphResistanceSpeedNearCritical`.

## Regression tests

| Network | Physical edges | Traditional distance | Traditional resistance |
|---|---:|---:|---:|
| one edge | `1` (`realize_one_edgeCard`) | `1` (`traditionalDistance_one`) | `1`, by `traditionalResistance_realize` and reduction of `SPNetwork.resistance` |
| two edges in series | `2` (`realize_twoSeries_edgeCard`) | `2` (`traditionalDistance_twoSeries`) | `2` (`traditionalResistance_twoSeries`) |
| two edges in parallel | `2` (`realize_twoParallel_edgeCard`) | `1` (`traditionalDistance_twoParallel`) | `1 / 2` (`traditionalResistance_twoParallel`) |

The parallel edge values are additionally proved distinct by
`SPNetwork.twoParallel_physicalEdges_distinct`. The edge-count result is established in the
realization layer and does not depend on the resistance bridge.

## Axiom fingerprints

The standard Lean principles shown by `#print axioms` are `propext`, `Classical.choice`, and
`Quot.sound`. Project-axiom fingerprints, after removing those standard principles, are:

| Declaration | Exact project-axiom fingerprint |
|---|---|
| `SPNetwork.traditionalDistance_realize` | empty |
| `SPNetwork.traditionalResistance_realize` | empty |
| `GraphSemantics.graphDistanceValue_eq_distanceValue` | empty |
| `GraphSemantics.graphResistanceValue_eq_resistanceValue` | empty |
| `GraphSemantics.graphLogarithmicSpeeds` | `{SeriesParallel.MainText.distanceGamma_half_eq_zero}` |
| `GraphSemantics.graphFirstMomentLogarithmicRates` | `{SeriesParallel.MainText.distanceGamma_half_eq_zero}` |
| `GraphSemantics.graphResistanceSpeedNearCritical` | `{SeriesParallel.ManualInterfaces.MI01_global_peano_on_compact_interval}` |

The three graph wrapper fingerprints exactly match their scalar counterparts. Neither documentary
assumptions nor any additional mathematical interface is reachable from the bridge.

## Module and import compatibility

The low-level new leaf modules use Lean's module/public system: `module`, `public import`, and
`@[expose] public section`. `RandomModel.lean`, `StatementContract.lean`, and `MainTheorems.lean`
are legacy modules because they must import the existing legacy
`MainTextStatementContract.lean` and `MainTheorems.lean`. This compatibility boundary does not alter
any definition, theorem statement, proof term, or axiom fingerprint.

The import direction is acyclic:

```text
Mathlib
  -> Basic
     -> TraditionalDistance
     -> TraditionalResistance
     -> Realization + Networks
        -> DistanceBridge + FinitePaths
        -> ResistanceBridge + FiniteFlows
           -> graph RandomModel
              -> graph StatementContract
                 -> graph MainTheorems
```

## Verification record

- Lean: 4.32.1.
- Lake: 5.0.0.
- mathlib: v4.32.1 at commit `520045ab14e26149ee970e2e617ca04b09bde5d6`.
- License: Apache-2.0.
- `lake build SeriesParallel.MainText.GraphSemantics`: success, 8,726 jobs.
- `lake env lean SeriesParallel/MainText/GraphSemantics.lean`: success.
- `lake env lean SeriesParallel/GraphSemanticsAudit.lean`: success.
- `lake build SeriesParallel.MainTextPublicAPI`: success, 8,728 jobs.
- `lake env lean SeriesParallel/MainTextPublicAPI.lean`: success.
- Repository-external import smoke test: success for both deterministic bridges and all three
  graph-facing main theorems.
- Placeholder and project-axiom audit: `PASS (80 files, 2 axiom declarations)`.
- Full `lake build`: success, 8,733 jobs.
