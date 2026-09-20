# Formalization report

Status: **main theorems complete relative to the stated inputs; auxiliary qualifications below**
Manuscript: `SeriesParallel.tex`

## Main result

The Lean development covers the three main results and their supporting proof dependencies,
relative to the two external inputs below. Theorem 1.3 has joint coverage by the
near-critical theorem and a separate admissible-halfline theorem.

| PDF result | Mathematical content | Lean declaration | External input |
|---|---|---|---|
| Theorem 1.1 | Almost-sure and $L^1$ logarithmic speeds for $D_n(p)$ and $R_n(p)$, with the stated identities and bounds on the full parameter range | `SeriesParallel.MainText.logarithmicSpeeds` | $\gamma_D(1/2)=0$ |
| Theorem 1.2 | Existence and identification of both first-moment logarithmic rates | `SeriesParallel.MainText.firstMomentLogarithmicRates` | $\gamma_D(1/2)=0$ |
| Theorem 1.3 | Existence and characterization of $\lambda_*$ and the sharp near-critical resistance asymptotics; joint coverage | `SeriesParallel.MainText.resistanceSpeedNearCritical`; `SeriesParallel.MainText.mainAdmissible_eq_Ici_lambdaStar` | compact-interval Peano existence |

For Theorem 1.3, `IsLeast` in the public wrapper supplies the least admissible parameter;
the separate identity `mainAdmissible = Set.Ici lambdaStar` supplies the full
if-and-only-if characterization. The traditional-graph wrapper has the same joint coverage.
The first two theorems do not use the Peano
interface, and the third theorem does not use the critical-distance interface.

## Supporting results

The 29 numbered theorem, proposition, and lemma environments are listed by their printed PDF
numbers in [MANUSCRIPT_LEAN_CORRESPONDENCE.md](MANUSCRIPT_LEAN_CORRESPONDENCE.md). The complete
label-level audit contains 137 active labels: 102 in the main text and 35 in the appendices.

Lemma 4.8 is a qualified auxiliary entry: Lean exports the error estimate used in the proof
of Theorem 1.3, but does not package every clause of the displayed standalone lemma as one theorem.
The displayed density bound `eq:q-uniform-bound` is also qualified: Lean exports
`q^2 <= exp(M) * q`, which is sufficient for the proof, rather than the manuscript's
sharper `q <= exp(M)/2`. These qualifications concern auxiliary packaging and constants,
not a missing premise in the main-theorem proof paths.

## Trust boundary

There are exactly two project axioms:

1. $\gamma_D(1/2)=0$;
2. global existence for a scalar ODE on a compact interval under continuity and a linear-growth
   bound.

Their exact mathematical statements and theorem dependencies are given in
[EXTERNAL_HYPOTHESES.md](EXTERNAL_HYPOTHESES.md) and [AXIOM_REPORT.md](AXIOM_REPORT.md).
No `sorry` or `admit` occurs in the Lean sources.

## Verification

This unreleased manuscript and report revision follows the author's final journal
source, through the synchronized arXiv companion. The sole repository reference is
`SeriesParallel.tex`. Its source map records all 137 active labels (102 main, 35
appendix), their current source lines, and the LF-normalized SHA-256.
All 140 raw label occurrences, including comments, have matching line numbers in
the journal, arXiv, and repository sources. The reference differs from arXiv only
by comment-padded removal of code availability; AI and Lean declarations remain.

The 29 numbered theorem/proposition/lemma statements are unchanged from the
previous reference. No Lean source, theorem signature, dependency version, or
external input was changed from commit `5afa967ce186ddba102d6801152330541e2b0d34`.
The existing joint-coverage audit checks the two near-critical wrappers and the
admissible-halfline identity. Current build, audit, LaTeX, and correspondence
results are recorded in [verification/2026-09-21](verification/2026-09-21/README.md).
The earlier dated evidence directory is retained as a historical record.

The lexical audit covers 80 Lean files and the two documented project axioms.
The scalar, graph, and halfline fingerprints are recorded in
[AXIOM_REPORT.md](AXIOM_REPORT.md). Joint coverage is stated in the reports;
the manuscript wording is preserved rather than augmented by audit terminology.

For Lemma A.2, Lean proves the stated continuity with Lipschitz constant
`3 * (3/4)^(1/3)`. The manuscript proof gives the sharper constant `3 * 2^(-1/3)`.
This unlabelled auxiliary improvement is not claimed as a verbatim Lean export.
The manuscript's comparison with EGS's bounds and endpoint asymptotics is a
literature comparison, not an additional formalization of EGS's paper.

No release, tag, or package-version change accompanies this revision.
