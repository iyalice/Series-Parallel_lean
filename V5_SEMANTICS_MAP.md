# V5 traditional graph-semantics map

## Scope

This map covers only the graph-semantic front end of the v5 manuscript: section 1.1, section 2.1,
and Lemma 3.1. It is not a label census and does not claim coverage of every v5 statement. The
manuscript-wide label correspondence is recorded separately in `SOURCE_MAP.md` and
`MANUSCRIPT_LEAN_CORRESPONDENCE.md`.

## Section 1.1: random series--parallel graph and boundary quantities

| Manuscript object | Lean declaration | Correspondence |
|---|---|---|
| A finite graph with two distinct terminals | `GraphSemantics.TwoTerminalMultigraph` | Bundles finite vertex and physical-edge types, endpoint maps, source, sink, and `source_ne_sink` |
| One physical edge | `SPNetwork.edge`; `SPNetwork.PhysicalEdge`; `SPNetwork.realize_one_edgeCard` | The leaf edge type is `PUnit`, and the realization has one edge |
| Series replacement | `SPNetwork.series`; `InternalVertex`; `seriesJoin`; `seriesLeftVertex`; `seriesRightVertex` | The child sink/source are identified at one tagged join vertex; all other internal vertices remain tagged |
| Parallel replacement | `SPNetwork.parallel`; `parallelLeftVertex`; `parallelRightVertex`; `realize_twoParallel_edgeCard` | The two boundary vertices are shared, but the physical edge type is a disjoint sum, preserving multiplicity |
| Depth-`n` random graph | `randomNetwork n environment`; `SPNetwork.realize` | The existing recursive random syntax is realized structurally as an edge-indexed multigraph |
| Graph distance `D_n` | `graphDistanceValue n environment` | Applies `traditionalDistance` to the realized random network |
| Effective resistance `R_n` | `graphResistanceValue n environment` | Applies Kirchhoff--Thomson `traditionalResistance` to the realized random network |
| Samplewise identification of `D_n` | `graphDistanceValue_eq_distanceValue` | Proved from `SPNetwork.traditionalDistance_realize` |
| Samplewise identification of `R_n` | `graphResistanceValue_eq_resistanceValue` | Proved from `SPNetwork.traditionalResistance_realize` |

The realization definitions are structural: they inspect only `edge`, `series`, and `parallel`.
Their definition bodies contain no reference to the recursive distance or resistance evaluator.

## Section 2.1: series/parallel scalar recursions

| Manuscript relation | Lean evidence | Status |
|---|---|:---:|
| Series distance adds | Existing `SPNetwork.distance` recursion, interpreted by `traditionalDistance_realize` | proved as graph semantics |
| Parallel distance takes the minimum | Existing `SPNetwork.distance` recursion, interpreted by `traditionalDistance_realize` | proved as graph semantics |
| Series resistance adds | Existing `SPNetwork.resistance` recursion, interpreted by `traditionalResistance_realize` | proved as Thomson semantics |
| Parallel resistance is `R_1 R_2 / (R_1 + R_2)` | Existing `SPNetwork.resistance` recursion, interpreted by `traditionalResistance_realize` | proved as Thomson semantics |
| Random one-step recursion | Existing `randomNetwork`, `distanceValue`, and `resistanceValue`, together with both samplewise graph equalities | transported without duplicating probability proofs |

The scalar recursions are not definitions of the traditional quantities. They are evaluators whose
agreement with independent general-walk and Kirchhoff-flow semantics is proved by the two bridge
theorems.

## Lemma 3.1: shortest paths and Thomson energy

### Distance side

| Mathematical ingredient | Lean declaration |
|---|---|
| Unrestricted walks in the undirected graph | `TwoTerminalMultigraph.simpleShadow` and `SimpleGraph.Walk` |
| Traditional terminal distance | `GraphSemantics.traditionalDistance` |
| Recursive shortest path realizes as a graph walk | `SPNetwork.Path.toRealizeWalk` and `Path.length_toRealizeWalk` |
| Realized terminals are reachable | `SPNetwork.realize_reachable` |
| Every graph walk has length at least the recursive distance | `SPNetwork.vertexLevel_edge_lipschitz` and `distance_le_realize_walk_length` |
| Equality of the two distances | `SPNetwork.traditionalDistance_realize` |

The lower bound applies to arbitrary graph walks, including walks with backtracking. It does not
claim a bijection between recursive paths and all graph walks.

### Resistance side

| Mathematical ingredient | Lean declaration |
|---|---|
| Signed edge current | `TwoTerminalMultigraph.Current` |
| Vertex divergence and Kirchhoff demand | `divergence`, `throughFlowDemand`, `IsThroughFlow` |
| Unit-edge energy | `unitEnergy` |
| Feasible unit-flow energies and their infimum | `energySet`, `HasUnitFlow`, `traditionalResistance` |
| Attaining conventional current | `SPNetwork.attainingCurrent` and `attainingCurrent_isThroughFlow` |
| Generalized Thomson lower bound | `SPNetwork.generalized_thomson` |
| Least-energy characterization | `SPNetwork.resistance_isLeast_energySet` |
| Equality of traditional and recursive resistance | `SPNetwork.traditionalResistance_realize` |

The Thomson bound quantifies over all conventional signed currents satisfying the vertex-wise
Kirchhoff equations. It therefore permits circulation and does not identify conventional currents
with the specialized recursive flow representation.

## Publication-facing transport

The graph-defined objects `graphZ`, `graphX`, `graphFirstMoment`, `graphMeanLog`, the normalized
graph sequences, and `graphVD`, `graphVR`, `graphGammaD`, `graphGammaR` are equal to their scalar
counterparts. The graph-facing statement contracts contain these objects syntactically, and the
following theorems transport the existing analytic proof graph:

- `GraphSemantics.graphLogarithmicSpeeds`;
- `GraphSemantics.graphFirstMomentLogarithmicRates`;
- `GraphSemantics.graphResistanceSpeedNearCritical`.

No manuscript claim outside the graph interpretation of section 1.1, the scalar recursions of
section 2.1, and the shortest-path/Thomson content used in Lemma 3.1 is certified by this map.
