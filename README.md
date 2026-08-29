# Series--parallel Lean formalization

This repository formalizes the three principal results on distance and resistance in random
series--parallel graphs. It includes a traditional finite-graph semantics: every recursive
`SPNetwork` is realized as a finite edge-indexed two-terminal multigraph, its distance is defined
by unrestricted graph walks, and its effective resistance is defined by the Thomson infimum over
all signed Kirchhoff unit flows.

The two semantic bridge theorems are:

```text
SeriesParallel.MainText.SPNetwork.traditionalDistance_realize
SeriesParallel.MainText.SPNetwork.traditionalResistance_realize
```

The graph interpretation is a conservative extension of the existing scalar proof graph. See
[FORMALIZATION_REPORT.md](FORMALIZATION_REPORT.md) for the complete status,
[SEMANTIC_BRIDGE_REPORT.md](SEMANTIC_BRIDGE_REPORT.md) for the 14-item acceptance audit, and
[AXIOM_REPORT.md](AXIOM_REPORT.md) for the trust boundary.

## Requirements

- [elan](https://github.com/leanprover/elan), selecting Lean 4.32.1 from `lean-toolchain`;
- Lake 5.0.0;
- mathlib v4.32.1, pinned by `lake-manifest.json` to commit
  `520045ab14e26149ee970e2e617ca04b09bde5d6`;
- Python 3 for the standard-library-only repository audits.

The repository is licensed under Apache-2.0. From a fresh clone:

```text
lake update
lake cache get
lake build
```

`lake cache get` is optional; `lake build` is the proof gate.

## Public theorems

Import `SeriesParallel.MainTextPublicAPI`. It exports both scalar and traditional-graph forms of
the three principal results.

| Result | Scalar theorem | Graph-facing theorem |
|---|---|---|
| Almost-sure and `L1` logarithmic speeds | `SeriesParallel.MainText.logarithmicSpeeds` | `SeriesParallel.MainText.GraphSemantics.graphLogarithmicSpeeds` |
| First-moment logarithmic rates | `SeriesParallel.MainText.firstMomentLogarithmicRates` | `SeriesParallel.MainText.GraphSemantics.graphFirstMomentLogarithmicRates` |
| Near-critical resistance speed | `SeriesParallel.MainText.resistanceSpeedNearCritical` | `SeriesParallel.MainText.GraphSemantics.graphResistanceSpeedNearCritical` |

The graph-facing contracts contain graph-defined random values, moments, normalized sequences,
and candidate limits syntactically. Their proofs transport the scalar theorems through proved
pointwise equalities, so no probability, CDF, moment, speed, or near-critical argument is
duplicated.

## Traditional graph semantics

### Graph and realization

`GraphSemantics.TwoTerminalMultigraph` bundles finite vertex and physical-edge types, fixed
orientation maps, and distinct source and sink vertices. Physical edges retain identity: two
parallel unit branches are two edge values even though the simple adjacency shadow used for
distance has only one source--sink adjacency.

`SPNetwork.realize` uses tagged recursive vertex and edge types. A series gate creates exactly one
join vertex; a parallel gate shares only the two boundary vertices and retains a disjoint sum of
child edges. The realization is loop-free and has `SPNetwork.edgeCount` physical edges.

### Distance

`GraphSemantics.traditionalDistance` is `SimpleGraph.dist` between the terminals. The recursive
shortest path supplies a realized walk and reachability. A recursive 1-Lipschitz vertex-level
certificate bounds every source--sink graph walk, including backtracking walks. The two bounds
give `SPNetwork.traditionalDistance_realize`.

### Effective resistance

`TwoTerminalMultigraph.Current` is an arbitrary signed edge function. Divergence is computed at
every vertex; `IsThroughFlow I` imposes source demand `I`, sink demand `-I`, and zero internal
divergence. `unitEnergy` sums squared current over physical edges, and `traditionalResistance` is
the `sInf` of conventional unit-flow energies.

`SPNetwork.generalized_thomson` proves the lower bound for every real flow value and every
conventional signed current, including currents containing circulation. A one-way map from the
specialized recursive optimum constructs an attaining current. The least-energy result gives
`SPNetwork.traditionalResistance_realize`.

### Random model

`graphDistanceValue` and `graphResistanceValue` realize `randomNetwork n environment` before
applying the independent traditional quantities. Their samplewise equalities are:

```text
SeriesParallel.MainText.GraphSemantics.graphDistanceValue_eq_distanceValue
SeriesParallel.MainText.GraphSemantics.graphResistanceValue_eq_resistanceValue
```

## Regression values

| Network | Physical edges | Distance | Resistance |
|---|---:|---:|---:|
| one unit edge | 1 | 1 | 1 |
| two unit edges in series | 2 | 2 | 2 |
| two unit edges in parallel | 2 | 1 | `1 / 2` |

The parallel edge count and edge distinctness are proved in the realization layer, independently
of the resistance bridge.

## Trust boundary

The repository contains exactly two project `axiom` declarations:

| External interface | Reachable from |
|---|---|
| `SeriesParallel.MainText.distanceGamma_half_eq_zero` | scalar and graph logarithmic-speed and first-moment theorems |
| `SeriesParallel.ManualInterfaces.MI01_global_peano_on_compact_interval` | scalar and graph near-critical resistance theorems |

The deterministic bridges and the two samplewise random bridges depend on no project axiom. Their
`#print axioms` output contains only `propext`, `Classical.choice`, and `Quot.sound`.

## Repository layout

- `SeriesParallel/MainText/GraphSemantics/`: traditional definitions, realization, bridges,
  random transport, graph contracts, and graph theorem wrappers;
- `SeriesParallel/MainText/GraphSemantics.lean`: graph-semantics aggregate;
- `SeriesParallel/GraphSemanticsAudit.lean`: permanent bridge and theorem fingerprint audit;
- `SeriesParallel/MainTextPublicAPI.lean`: public import surface;
- `scripts/`: placeholder, axiom-fingerprint, and manuscript-label audits;
- `SOURCE_MAP.md` and `MANUSCRIPT_LEAN_CORRESPONDENCE.md`: manuscript/Lean crosswalks;
- `SEMANTIC_BRIDGE_REPORT.md` and `V5_SEMANTICS_MAP.md`: graph-semantics audit and narrow v5 map;
- `FORMALIZATION_REPORT.md`, `AXIOM_REPORT.md`, `DEPENDENCY_DAG.md`, and
  `ENCODING_NOTES.md`: formalization status and design reports.

`MAIN_TEXT_BLOCKERS.md` is a frozen historical input and is not the current status report.

## Reproducible audits

Run from the repository root:

```text
python scripts/audit_lean_placeholders.py --axiom-manifest project-axioms.tsv SeriesParallel SeriesParallel.lean
lake env lean SeriesParallel/MainText/GraphSemantics.lean
lake env lean SeriesParallel/GraphSemanticsAudit.lean
lake env lean SeriesParallel/MainTextPublicAPI.lean
lake env lean SeriesParallel/MainTextAudit.lean > main-text-axioms.out 2>&1
python scripts/audit_project_axioms.py --declarations project-axioms.tsv --fingerprints main-text-axioms.out
python scripts/check_main_text_labels.py
lake build
```

The graph aggregate build succeeds with 8,726 jobs, the public API build succeeds with 8,728 jobs,
the full build succeeds with 8,733 jobs, and the placeholder audit reports
`PASS (80 files, 2 axiom declarations)`. The permanent graph
audit prints the exact fingerprints of both deterministic bridges, both samplewise bridges, all
three graph-facing wrappers, and their scalar counterparts.
