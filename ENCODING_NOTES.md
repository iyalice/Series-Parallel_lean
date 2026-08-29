# Encoding notes

## Traditional graph object

- `TwoTerminalMultigraph` bundles finite vertex and physical-edge types, decidable equality,
  endpoint maps, and distinct terminals.
- Physical edges, not endpoint pairs, are the electrical coordinates. Parallel edges remain
  separate current coordinates and energy terms.
- Tail/head orientation is bookkeeping. Currents are arbitrary real edge functions, so the
  feasible set includes negative currents and circulation.
- The simple undirected shadow forgets multiplicity only for unweighted distance.

## Structural realization

- `PhysicalEdge edge = PUnit`; both gates use a disjoint sum of child edge types.
- `InternalVertex` adds one join tag at a series gate and disjointly tags child interiors.
  `RealizedVertex` adds two boundary tags.
- Series embeddings identify exactly the child sink/source at the join. Parallel embeddings
  identify only the common source and sink.
- `realize` reads syntax constructors only; its body uses neither recursive evaluator.
- `realize_edgeCard` and the small regressions certify physical-edge multiplicity.

## Distance semantics

- `traditionalDistance` is terminal distance in the general-walk `SimpleGraph` shadow.
- The recursive shortest path maps to a realized graph walk of equal length.
- `vertexLevel` is a natural-number 1-Lipschitz certificate: series shifts the right branch and
  parallel clips both branches at the minimum distance.
- The lower-bound theorem covers walks with backtracking and repeated vertices.
- The bridge proves equality of minimum values, not a bijection between path representations.

## Resistance semantics

- Divergence is outgoing minus incoming signed current at every vertex.
- `IsThroughFlow I` prescribes source divergence `I`, sink divergence `-I`, and zero interior
  divergence.
- `unitEnergy` sums squared current over physical edges; `traditionalResistance` is the `sInf` of
  feasible unit-flow energies.
- `HasUnitFlow` records nonemptiness. Disconnected raw graphs are not given a physical
  interpretation merely because `sInf empty` has a default real value.
- `Flow.toCurrent` is one-way and supplies attainment. No false inverse parametrization is made.
- `generalized_thomson` ranges over every conventional signed current and permits circulation.

## Random model and transport

- A common uniform-coordinate Bernoulli environment realizes every parameter and makes parameter
  monotonicity samplewise.
- `graphDistanceValue` and `graphResistanceValue` realize the network before applying the
  independent traditional quantity.
- Samplewise bridge equalities identify the graph variables with the scalar variables.
- Graph versions of `Z`, `X`, moments, normalized sequences, and candidate limits are defined and
  proved equal to their scalar counterparts.
- Graph-facing contracts use graph-defined quantities syntactically. Probability, CDF, moment,
  speed, and near-critical proofs are transported rather than duplicated.

## Analytic representation choices

- `paperLog` maps zero to `EReal.bot` while finite rate candidates remain real-valued.
- Normalized sequences use `n + 1` indexing to avoid division by zero.
- Near-critical powers use `Real.rpow delta ((2 : Real) / 3)` and `Real.cbrt zetaThree`.
- Cubing and cube root are cofinal inverse maps on the right-neighborhood filter, giving a full
  right-limit theorem rather than a subsequence result.
- `SourceWSolution` is the compact-interval boundary-value problem; the appendix facade exposes
  only the profile facts consumed by the main proof graph.

## Module compatibility

The low-level new leaf modules use `module`, `public import`, and `@[expose] public section`.
Graph `RandomModel.lean`, `StatementContract.lean`, and `MainTheorems.lean` are legacy modules
because they import existing legacy statement-contract and theorem modules. This syntax boundary
has no mathematical effect and does not alter declaration types or axiom fingerprints.
