# Series–parallel Lean formalization

This repository formalizes the complete proof graph needed for the three principal results of
[`Series-Parallel_SPA_submission.tex`](Series-Parallel_SPA_submission.tex). The canonical
manuscript has 156 unique active labels (112 in the main text and 44 in the appendices), all
recorded in [SOURCE_MAP.md](SOURCE_MAP.md).

All three public theorems compile. The development is not axiom-free: it uses exactly two
documented external mathematical interfaces, each with a separate theorem dependency path.
See [FORMALIZATION_REPORT.md](FORMALIZATION_REPORT.md) for the full status and
[AXIOM_REPORT.md](AXIOM_REPORT.md) for the exact theorem fingerprints.

## Requirements

- [elan](https://github.com/leanprover/elan), which reads `lean-toolchain` and selects
  Lean 4.32.1;
- Lake 5.0.0, distributed with Lean;
- mathlib 4.32.1, pinned by `lake-manifest.json` to commit
  `520045ab14e26149ee970e2e617ca04b09bde5d6`;
- Python 3 for the repository audits. The scripts use only the Python standard library and have
  no `pip` requirements.

A TeX distribution is needed only to compile the paper. TeX is not part of Lean's trusted
type-checking path; the label audit merely reads the canonical `.tex` source.

From a fresh clone:

```text
lake update
lake cache get
lake build
```

`lake cache get` is an optional speed-up; `lake build` remains the final proof gate.

## What is proved

Import `SeriesParallel.MainTextPublicAPI` to obtain the three public theorems.

### `SeriesParallel.MainText.logarithmicSpeeds`

For every `p ∈ [0,1]`, the normalized logarithms of the distance and resistance converge almost
surely and in `L¹` to deterministic speeds `vD p` and `vR p`. The theorem also proves:

- `vD p = 0` for `0 ≤ p ≤ 1/2`;
- resistance duality `vR (1-p) = -vR p`, hence `vR (1/2) = 0`;
- for `1/2 < p ≤ 1`, both speeds lie in `[log (2p), log 2]`.

### `SeriesParallel.MainText.firstMomentLogarithmicRates`

For every `p ∈ [0,1]`, the first-moment logarithmic rates `gammaD p` and `gammaR p` exist, and

- `gammaD p = vD p`;
- `gammaR p = max (vR p) (log (2p))`, using the paper's convention `log 0 = -∞`;
- `gammaR p = vR p` for `1/2 ≤ p ≤ 1`.

### `SeriesParallel.MainText.resistanceSpeedNearCritical`

The theorem proves that the boundary-value problem

```text
W² W' - λ W + u(1-u) = 0,
W > 0 on (0,1),
W(0) = W(1) = 0
```

has a least admissible positive parameter `lambdaStar`, and proves the paper's three
near-critical asymptotics for `vR` and `gammaR`, with leading constant
`2 * cbrt (ζ(3)) * lambdaStar` and exponent `2/3`.

The formal statement contracts are in
[`MainTextStatementContract.lean`](SeriesParallel/MainText/MainTextStatementContract.lean).
The third theorem is assembled in a separate resistance-only module, so it does not inherit the
critical-distance interface.

## Paper model and Lean model

The mathematical conclusions above are fully represented, but the finite random graph is encoded
by a purpose-built two-terminal series–parallel syntax rather than by Mathlib's general graph and
electrical-network APIs.

| Paper object | Lean object | Correspondence |
|---|---|---|
| Binary-tree Bernoulli variables `ξᵤ` | `Environment` with `environmentMeasure p` | Direct probability encoding: `true` has probability `p` and means series; `false` means parallel. |
| The edge-refinement graph `Gₙ(p)` | `randomNetwork n environment : SPNetwork` | Encoding-equivalent rooted syntax tree. `randomNetwork_refinement` proves compatibility with generation-by-generation leaf replacement. |
| Graph distance `Dₙ(p)` | `distanceValue n environment` | Recursively `edge = 1`, series = addition, parallel = `min`; not definitionally Mathlib graph distance. `distance_eq_minimumPathLength` and `length_shortestPath` prove the shortest-path characterization inside the finite two-terminal model. |
| Effective resistance `Rₙ(p)` | `resistanceValue n environment` | Recursively `edge = 1`, series = addition, parallel = `xy/(x+y)`; not defined through a general graph Laplacian. `optimalFlow_unitEnergy` and `resistance_le_unitEnergy` prove the Thomson minimum-energy characterization for this model. |
| Distributional recursion for `Zₙ` | `Z_succ`, subtree independence, and `X_succ_hasLaw` | Lean first proves a stronger samplewise recursion on one common environment; the independent-subtree law then yields the paper's equality in distribution. |

Thus the distance and resistance recursions are not unsupported replacements for the paper's
notions: their path and flow semantics are proved. What is not claimed is a definitional equality
with an unrelated general-purpose graph library representation.

## Exact translation and equivalent encodings

No principal conclusion is weakened. “Direct” below means that the Lean predicate follows the
paper's mathematical syntax closely; “equivalent” means that Lean uses a different but proved
equivalent representation.

- The third main theorem is a direct semantic translation. `SourceWSolution` represents
  `C([0,1]) ∩ C¹((0,1))`, the ODE, positivity and endpoint conditions; `IsLeast` represents the
  smallest positive parameter; and `IsEquivalent (𝓝[>] 0)` represents `δ ↓ 0` asymptotics.
- The first two main theorems have exactly the paper's mathematical content but use equivalent
  limit packaging. Lean indexes normalized sequences by `n+1` to avoid division by zero and uses
  `chosenSequentialLimit` to give the deterministic constants canonical names. Tail reindexing
  and uniqueness of limits make these forms equivalent to the paper's `n → ∞` and existential
  wording.
- A real parameter with a hypothesis `p ∈ [0,1]` is passed to the probability model as
  `modelParameter p : unitInterval`. The project proves that this projection is exactly `p` under
  the stated interval hypothesis.
- Almost-sure convergence is encoded with `∀ᵐ`, `L¹` convergence by convergence of the integral
  of the absolute error, `δ^(2/3)` by `Real.rpow`, and `ζ(3)^(1/3)` by `Real.cbrt`.
- The convention `log 0 = -∞` is represented by `paperLog : ℝ → EReal`, while the finite rates
  themselves remain real-valued.
- Resistance duality in the near-critical theorem is stated for every `0 < δ ≤ 1/2`, a natural
  full-domain strengthening of the equality appearing beside the local asymptotic. It follows
  from the first theorem's global duality.

The gate formulas themselves are direct translations: `seriesGate`, `parallelGate`,
`logSeriesGate`, `logParallelGate`, and `h` match the manuscript's `Πη`, `g₊`, `g₋` and `h` on
their stated positive domains.

## Trust boundary

The repository contains exactly two project `axiom` declarations:

| External interface | Used by |
|---|---|
| `SeriesParallel.MainText.distanceGamma_half_eq_zero` | `logarithmicSpeeds`, `firstMomentLogarithmicRates` |
| `SeriesParallel.ManualInterfaces.MI01_global_peano_on_compact_interval` | `resistanceSpeedNearCritical` |

The optional diffusion fallback is absent: the identity connecting the diffusion coefficient to
`2 ζ(3)` is proved internally. The audit output may also list Lean's standard logical principles
`propext`, `Classical.choice`, and `Quot.sound`; these are not project-specific assumptions.

## Repository layout

- `SeriesParallel/`: all Lean modules;
- `SeriesParallel.lean`: library root;
- `SeriesParallel/MainTextPublicAPI.lean`: public entry point for the three theorems;
- `scripts/`: placeholder, axiom-fingerprint, and TeX-label audits;
- `Series-Parallel_SPA_submission.tex`: canonical manuscript used by the label audit;
- `SOURCE_MAP.md`: exhaustive 156-label manuscript-to-Lean crosswalk;
- `FORMALIZATION_REPORT.md`, `AXIOM_REPORT.md`, `EXTERNAL_HYPOTHESES.md`,
  `DEPENDENCY_DAG.md`, `STATEMENT_INVENTORY.md`, `ENCODING_NOTES.md`, and `BLOCKERS.md`:
  canonical project reports.

## Reproducible audits

Run these commands from the repository root:

```text
python scripts/audit_lean_placeholders.py --axiom-manifest project-axioms.tsv SeriesParallel SeriesParallel.lean
lake env lean SeriesParallel/MainTextPublicAPI.lean
lake env lean SeriesParallel/MainTextAudit.lean > main-text-axioms.out 2>&1
python scripts/audit_project_axioms.py --declarations project-axioms.tsv --fingerprints main-text-axioms.out
python scripts/check_main_text_labels.py
lake build
```

The first and third commands verify that the only project assumptions and all three theorem
fingerprints match the committed policy. Remove the temporary `project-axioms.tsv` and
`main-text-axioms.out` after the audit; `.gitignore` excludes them.

## Files for GitHub

Track these files:

- `.gitignore`, `LICENSE`, `README.md`;
- `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`;
- `SeriesParallel.lean` and every `.lean` file below `SeriesParallel/`;
- the three Python files in `scripts/`;
- `Series-Parallel_SPA_submission.tex`;
- the eight canonical reports listed under “Repository layout”.

Do not track `.lake/`, Python caches, audit manifests, TeX intermediate files, generated PDFs,
superseded manuscript variants, internal agent-ownership notes, frozen `MAIN_TEXT_*` inputs, or
historical re-audit/revision reports. A submission PDF is better attached to a GitHub Release than
committed to the proof repository.

`MAIN_TEXT_BLOCKERS.md` is a frozen historical input snapshot and is not the current project
status. The current blocker report is `BLOCKERS.md`.
