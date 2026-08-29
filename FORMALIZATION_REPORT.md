# Series--parallel formalization report

Status date: 2026-08-29
Status: **COMPLETE**

## Scope and result

The development proves the three principal manuscript theorems and supplies a faithful traditional
graph interpretation of the distance and resistance random variables. Every `SPNetwork` is
realized as a finite edge-indexed two-terminal multigraph. General-walk distance and
Kirchhoff--Thomson effective resistance of that realization are proved equal to the recursive
evaluators.

```text
SeriesParallel.MainText.SPNetwork.traditionalDistance_realize
SeriesParallel.MainText.SPNetwork.traditionalResistance_realize
SeriesParallel.MainText.GraphSemantics.graphLogarithmicSpeeds
SeriesParallel.MainText.GraphSemantics.graphFirstMomentLogarithmicRates
SeriesParallel.MainText.GraphSemantics.graphResistanceSpeedNearCritical
```

## Toolchain and build surface

- Lean 4.32.1; Lake 5.0.0.
- mathlib v4.32.1 at commit `520045ab14e26149ee970e2e617ca04b09bde5d6`.
- Apache-2.0 license.
- Graph-semantics aggregate: successful, 8,726 jobs.
- Main-text public API: successful, 8,728 jobs.
- Full project build: successful, 8,733 jobs.
- Placeholder audit: `PASS (80 files, 2 axiom declarations)`.

## Traditional graph layer

`GraphSemantics.TwoTerminalMultigraph` bundles finite vertex and physical-edge types, decidable
equality, endpoint maps, and distinct terminals. The electrical layer is edge-indexed, so parallel
edges remain distinct energy terms. The simple undirected shadow is used only for distance.

- `traditionalDistance` is terminal `SimpleGraph.dist`.
- `Current` is `Edge -> Real` with no sign restriction.
- `divergence` and `IsThroughFlow I` impose the full vertex-wise Kirchhoff equations.
- `unitEnergy` is the sum of squared currents over physical edges.
- `traditionalResistance` is the infimum of conventional unit-flow energies.

The raw graph layer does not claim that every graph has a unit flow. `HasUnitFlow` records
nonemptiness; the realization bridge constructs an attaining unit flow before using the infimum.

## Structural realization

`SPNetwork.PhysicalEdge` has one leaf edge and disjoint-sum child edges at both gates.
`SPNetwork.InternalVertex` creates one tagged join at a series gate and disjoint child interiors.
`SPNetwork.RealizedVertex` adds two boundary tags. `SPNetwork.realize` supplies the bundled graph.

Its certificates include `realize_noLoops`, `realize_edgeCard`, endpoint and embedding lemmas, the
three small edge-count regressions, and `twoParallel_physicalEdges_distinct`. Realization
definition bodies inspect the syntax constructors only and contain neither evaluator.

## Distance bridge

The upper bound maps the recursive shortest path to a graph walk through `Path.toRealizeWalk`;
`Path.length_toRealizeWalk` preserves length and `realize_reachable` excludes the disconnected
junk case. The lower bound uses `vertexLevel`, whose source value is zero, sink value is
`N.distance`, and edge increment is at most one. `distance_le_realize_walk_length` applies to
arbitrary walks. These bounds prove `traditionalDistance_realize`.

## Resistance bridge

`Flow.toCurrent` maps a recursive flow witness to a conventional current.
`flow_toCurrent_isThroughFlow` proves full feasibility, and `flow_toCurrent_unitEnergy` computes
the scaled energy. `generalized_thomson` proves for every `I : Real` and every conventional
`I`-through-flow current:

```text
I ^ 2 * network.resistance <= network.realize.unitEnergy current.
```

The parallel case allows arbitrary circulation. The mapped recursive optimum gives attainment;
`resistance_isLeast_energySet` proves least energy, and `traditionalResistance_realize` identifies
that value with the `sInf`. No inverse parametrization of conventional currents is asserted.

## Random transport and theorem status

`graphDistanceValue` and `graphResistanceValue` apply the traditional quantities after realizing
the random network. `graphDistanceValue_eq_distanceValue` and
`graphResistanceValue_eq_resistanceValue` prove exact samplewise equality. Graph versions of
`Z`, `X`, moments, normalized sequences, and the four candidate limits are defined and proved
equal to their scalar counterparts.

| Result | Scalar theorem | Graph-facing theorem | Status |
|---|---|---|:---:|
| Logarithmic speeds | `MainText.logarithmicSpeeds` | `GraphSemantics.graphLogarithmicSpeeds` | proved |
| First-moment logarithmic rates | `MainText.firstMomentLogarithmicRates` | `GraphSemantics.graphFirstMomentLogarithmicRates` | proved |
| Near-critical resistance speed | `MainText.resistanceSpeedNearCritical` | `GraphSemantics.graphResistanceSpeedNearCritical` | proved |

The graph contracts contain graph objects syntactically. Their equivalence with the scalar
contracts transports the analytic proof graph without duplicating it.

## Trust ledger

There are exactly two project axioms:

| Declaration | Reachability |
|---|---|
| `SeriesParallel.MainText.distanceGamma_half_eq_zero` | first and second scalar and graph theorems |
| `SeriesParallel.ManualInterfaces.MI01_global_peano_on_compact_interval` | third scalar and graph theorem |

The deterministic and samplewise graph bridges have empty project-axiom fingerprints. The first
two scalar and graph wrappers have exactly `{distanceGamma_half_eq_zero}`; the third scalar and
graph wrappers have exactly `{MI01_global_peano_on_compact_interval}`. Standard output also lists
`propext`, `Classical.choice`, and `Quot.sound`.

## Module boundary

Low-level graph, realization, and bridge files use the module/public system. Graph
`RandomModel.lean`, `StatementContract.lean`, and `MainTheorems.lean` are legacy modules because
they import existing legacy statement-contract and theorem modules. This compatibility boundary
does not change declaration types, proofs, or fingerprints.

The traditional definition files cannot import the recursive model. `Realization.lean` imports
only the network syntax side. The bridge files are the first modules that see both semantic sides.

## Verification

`SeriesParallel/GraphSemanticsAudit.lean` prints axioms for both deterministic bridges, both
samplewise equalities, the three graph-facing wrappers, and the scalar theorems. The graph
aggregate, graph audit, public API, scalar audit, external smoke file, placeholder scan, symbol-use
scan, fingerprint comparison, and full project build all pass.

See `SEMANTIC_BRIDGE_REPORT.md` for the acceptance table and `V5_SEMANTICS_MAP.md` for the narrow
v5 crosswalk. The manuscript-wide correspondence is in `SOURCE_MAP.md` and
`MANUSCRIPT_LEAN_CORRESPONDENCE.md`.

Remaining formalization blockers: **none**.
