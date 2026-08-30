# Formalization report

Status: **complete**
Manuscript: `Distance_and_resistance_arxiv_amsart.tex`

## Main result

The Lean development proves every clause of the three main results in the manuscript.

| PDF result | Mathematical content | Lean declaration | External input |
|---|---|---|---|
| Theorem 1.1 | Almost-sure and $L^1$ logarithmic speeds for $D_n(p)$ and $R_n(p)$, with the stated identities and bounds on the full parameter range | `SeriesParallel.MainText.logarithmicSpeeds` | $\gamma_D(1/2)=0$ |
| Theorem 1.2 | Existence and identification of both first-moment logarithmic rates | `SeriesParallel.MainText.firstMomentLogarithmicRates` | $\gamma_D(1/2)=0$ |
| Theorem 1.3 | Existence and characterization of $\lambda_*$ and the sharp near-critical resistance asymptotics | `SeriesParallel.MainText.resistanceSpeedNearCritical` | compact-interval Peano existence |

Thus Theorems 1.1, 1.2, and 1.3 are fully formalized. The first two theorems do not use the Peano
interface, and the third theorem does not use the critical-distance interface.

## Supporting results

The 29 numbered theorem, proposition, and lemma environments are listed by their printed PDF
numbers in [MANUSCRIPT_LEAN_CORRESPONDENCE.md](MANUSCRIPT_LEAN_CORRESPONDENCE.md). The complete
label-level audit contains 136 active labels: 98 in the main text and 38 in the appendices.

The only qualified auxiliary entry is Lemma 4.5: Lean exports the error estimate used in the proof
of Theorem 1.3, but does not package every clause of the displayed standalone lemma as one theorem.
This does not weaken any main-theorem statement or leave any gap in their proof paths.

## Trust boundary

There are exactly two project axioms:

1. $\gamma_D(1/2)=0$;
2. global existence for a scalar ODE on a compact interval under continuity and a linear-growth
   bound.

Their exact mathematical statements and theorem dependencies are given in
[EXTERNAL_HYPOTHESES.md](EXTERNAL_HYPOTHESES.md) and [AXIOM_REPORT.md](AXIOM_REPORT.md).
No `sorry` or `admit` occurs in the Lean sources.

## Verification

- The attached final TeX has 136 distinct active labels in the source map, in the correct order
  and at the recorded lines.
- The lexical proof audit finds exactly the two declared project axioms above.
- Release 1.0.2 pins Lean 4.32.1 and mathlib v4.32.1; the complete retained source tree
  succeeds with `lake build`.

There are no remaining blockers for the three main theorems.
