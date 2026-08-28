# Series–parallel formalization report

Status date: 2026-08-27. **All three source-facing main theorems are declared and compiled.**
There are no remaining blockers for those theorems.

## Input snapshot and toolchain

The mathematical source is `Series-Parallel_SPA_submission.tex`; the current continuation
used `MAIN_TEXT_CLOSURE_MATH_REFERENCE.md` as a formalization aid and
`CODEX_PROMPT_CLOSE_THREE_MAIN_THEOREMS.md` as the execution specification. The frozen
`MAIN_TEXT_BLOCKERS.md` supplied implementation provenance only and was not treated as a
mathematical authority.

- Lean: 4.32.1
- Lake: 5.0.0
- mathlib: 4.32.1
- initial full build: 8706 jobs, successful
- final full build after the two-axiom scope reduction: 8723 jobs, successful

The unique continuation probe directory was `main-text-probe.ef21218e`. Its complete Lean
type-check passed, and that exact directory and its `MainTextInputProbe.lean` were then removed.
The verified input surface was:

| Fully qualified declaration | Verified type/role |
|---|---|
| `SeriesParallel.MainText.X_succ_hasLaw` | exact one-generation law recursion for `X` |
| `SeriesParallel.MainText.logarithmic_drift` | exact expected logarithmic drift identity |
| `SeriesParallel.MainText.firstMoment_succ_lower_bound` | one-step first-moment lower bound |
| `SeriesParallel.MainText.firstMoment_geometric_bounds` | finite geometric first-moment bounds |
| `SeriesParallel.MainText.jensenGap_nonneg` | nonnegativity of the Jensen gap |
| `SeriesParallel.MainText.conditional_refinement_core` | refinement identity, descendant product law, iid family, and sigma-algebra independence |
| `SeriesParallel.MainText.SPNetwork.distance_substituteConst` | distance evaluator homogeneity under constant leaf substitution |
| `SeriesParallel.MainText.SPNetwork.resistance_substituteConst` | resistance evaluator homogeneity under constant leaf substitution |
| `SeriesParallel.MainText.cdfOperator` / `Iminus` / `Iplus` | measure-backed CDF operator and the two crossing integrals |
| `SeriesParallel.MainText.cdfOperator_translate` | translation covariance |
| `SeriesParallel.MainText.diffusionCoefficient` | integral-defined diffusion coefficient |
| `diffusionIntegrand_hasFiniteIntegral` / `diffusionCoefficient_pos` | finiteness and positivity |
| `summable_zetaThree` / `zetaThree_pos` | convergence and positivity of the project zeta-three series |
| `SeriesParallel.Appendix.waveProfile_exactSource` / `waveRelativeDerivatives` | full-line profile façade inputs |
| `SeriesParallel.Appendix.subcriticalProfile_exactSource` / `subcriticalProfile` | hard-edge profile façade inputs |
| `SeriesParallel.AppendixPublicAPI.wave_density_probability` | full-line profile probability law |
| `SeriesParallel.AppendixPublicAPI.hardEdge_density_probability` | hard-edge profile probability law |
| `SeriesParallel.MainInput` / `.a` / `.a_pos` | appendix input structure and its two source fields |

No input signature or proof required a source-correctness repair.

## Main theorem status

Import `SeriesParallel.MainTextPublicAPI` for the three complete source-facing contracts:

| TeX result | Lean theorem | Status |
|---|---|---|
| `thm:logarithmic-speeds` | `SeriesParallel.MainText.logarithmicSpeeds` | proved |
| `thm:first-moment-logarithmic-rates` | `SeriesParallel.MainText.firstMomentLogarithmicRates` | proved |
| `thm:near-critical-speed` | `SeriesParallel.MainText.resistanceSpeedNearCritical` | proved |

`MainTextStatementContract.lean` fixes all quantifiers and endpoints, almost-sure plus `L¹`
convergence, `paperLog 0 = -∞`, duality, the literal source BVP and its least positive parameter,
and the three full right-filter equivalences. The first two contracts use equivalent `n + 1`
tail indexing and canonical chosen limits; the third is a direct semantic translation.
`ResistanceNearCritical.lean` assembles it in a resistance-only dependency closure.

## Census and source coverage

The committed parser recomputes **156 active unique TeX labels**:

| Owner | Metadata | Statement environments | Formula labels | Total |
|---|---:|---:|---:|---:|
| main | 14 | 20 | 78 | 112 |
| appendix | 2 | 9 | 33 | 44 |
| total | 16 | 29 | 111 | 156 |

The 11 profile labels moved into the current main text are counted once with
`TeX owner = main` and `implementation owner = appendix/façade`. `SOURCE_MAP.md` is the sole
per-label authority. A small number of rows marked `partial (theorem-path bound proved)` record
standalone display-wrapper granularity only; they do not weaken a main theorem.

The cited distance near-critical comparison is not needed for the three requested theorems. It is
retained in the 156-label census as an out-of-scope literature-citation display, but has no Lean
declaration, module, or project axiom. The former critical-resistance citation display is absent
from the current SPA manuscript.

## Appendix–main façade boundary

The appendix depends only on `SeriesParallel.MainInput`, whose source fields are `a` and `a_pos`.
The main text constructs `diffusionMainInput` from the internally proved diffusion coefficient
and consumes the narrow appendix/profile APIs through `ProfileFacade.lean`. There is no reverse
import from the appendix into the main proof graph. Hard-edge uniqueness remains `EqOn` on
`Set.Ici 0`; the full-line BVP uses the canonical unit-clamp extension.

## Trust ledger

| Trust class | Content | Count |
|---|---|---:|
| internal | model, path/flow semantics, moments, CDF/order, diffusion calculation, barriers, assembly | project proofs |
| mathlib | measure theory, asymptotics, integration, probability, real analysis | library theorems |
| core literature | `distanceGamma_half_eq_zero` | 1 |
| core appendix | generic Peano interface `MI01_global_peano_on_compact_interval` | 1 |

Thus the project contains **2 external mathematical facts represented by 2 Lean `axiom`
declarations**, below the allowed maximum of 6. The optional diffusion fallback E-a was not used:
`diffusionCoefficient_eq_two_mul_zetaThree` is an internal theorem.

## Transitive theorem fingerprints

Besides the standard kernel principles `propext`, `Classical.choice`, and `Quot.sound`:

| Theorem | Project axiom fingerprint |
|---|---|
| `logarithmicSpeeds` | `{distanceGamma_half_eq_zero}` |
| `firstMomentLogarithmicRates` | `{distanceGamma_half_eq_zero}` |
| `resistanceSpeedNearCritical` | `{MI01_global_peano_on_compact_interval}` |

In particular, the first two do not inherit MI01 and the third does not inherit the distance
input. No stronger literature citation is encoded in the project.

## Dependency and encoding summary

The merged proof graph is recorded in `DEPENDENCY_DAG.md`. Its two main branches are finite
path/flow semantics through Fekete and Jensen/center tracking, and exact CDF/order plus the
internally evaluated diffusion coefficient through the upper and hard-edge lower barriers. They
meet only at the final parameter squeeze and theorem assembly.

Key representation choices are recorded in `ENCODING_NOTES.md`: a common uniform-coordinate
environment for parameter coupling, recursive path and through-current witnesses, a
measure-backed CDF operator, `EReal` for the paper logarithm at zero, and cofinal cube/cube-root
maps for a full `𝓝[>] 0` result rather than a subsequence.

## Reproducible final audit

Run from the project root:

```text
python scripts/audit_lean_placeholders.py --axiom-manifest project-axioms.tsv SeriesParallel SeriesParallel.lean
lake env lean SeriesParallel/MainTextPublicAPI.lean
lake env lean SeriesParallel/MainTextAudit.lean > main-text-axioms.out 2>&1
python scripts/audit_project_axioms.py --declarations project-axioms.tsv --fingerprints main-text-axioms.out
python scripts/check_main_text_labels.py
lake build
```

The lexical audit checks nested comments and strings, runs its fixtures, rejects proof escapes,
and reports `PASS (69 files, 2 axiom declarations)`. The fingerprint audit reports
`PASS (2 declarations, 3 theorem fingerprints)` and matches all three
theorem dependency sets exactly. The label parser reports `156 = 112 + 44` with no missing,
extra, or duplicate label. The public API and theorem audit pass; the final project gate reports
`Build completed successfully (8723 jobs)`. The generated
`project-axioms.tsv` and `main-text-axioms.out` are deliberately removed after auditing, as are
all probe and scratch files.

## Report provenance and blockers

Canonical reports are `SOURCE_MAP.md`, `STATEMENT_INVENTORY.md`, `DEPENDENCY_DAG.md`,
`ENCODING_NOTES.md`, `EXTERNAL_HYPOTHESES.md`, `AXIOM_REPORT.md`, and `BLOCKERS.md`.
The legacy files `MAIN_TEXT_SOURCE_MAP.md`, `MAIN_TEXT_STATEMENT_INVENTORY.md`,
`MAIN_TEXT_DEPENDENCY_DAG.md`, `MAIN_TEXT_ENCODING_NOTES.md`,
`MAIN_TEXT_EXTERNAL_HYPOTHESES.md`, and `MAIN_TEXT_AXIOM_REPORT.md` are non-canonical indices to
those merged reports. `Series_Parallelv2_reaudit_zh.md` and
`Series_Parallelv2_revision_log_zh.md` are historical summary/index documents.
`MAIN_TEXT_BLOCKERS.md` remains byte-for-byte frozen input evidence and is not current status.

Remaining blockers: **none**.
