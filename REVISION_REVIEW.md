# Response to the strict review — 2026-09-20

The authoritative repository manuscript is `Series_Parallel.tex`, derived from
the revised arXiv submission, which in turn follows the author's current journal
submission. The original review concerned an earlier 35-page PDF and archived
release v1.0.2. Its recommendations were checked against the current source rather
than assumed to describe the current manuscript unchanged.

## Review findings and disposition

| Review issue | Current disposition |
|---|---|
| Lemma A.2's mismatched initial/terminal-value citation | The supplied current journal source already contains a self-contained proof. Its existence, comparison/uniqueness, positivity, strict parameter order, and uniform continuity argument were checked. Real cube roots are now specified before the comparison lemma, and hard-coded appendix cross-references are replaced by labels. No direct application of the mismatched EGS clauses remains. |
| Overbroad formalization claim | The abstract and methodology cover the three main theorems and their proof dependencies relative to two documented inputs. Auxiliary packaging and constant differences are explicitly qualified. |
| Theorem 1.3 halfline clause | All corresponding report tables list joint coverage by the near-critical theorem and `mainAdmissible_eq_Ici_lambdaStar`. The traditional-graph wrapper has the same qualification. A new audit module records the three relevant axiom fingerprints. |
| Remark 4.11's unjustified CDF iteration heuristic | Replaced by the scale balance giving the exponent 2/3. It does not infer iterated CDF comparability from signed increments. |
| Remark 1.5 profile assumptions and constant | Specifies the full-line profile with parameter above the threshold and points to the diffusion-coefficient calculation. |
| Endpoint strict inequality in Proposition A.6 | The residual is nonnegative on the closed interval and positive away from zero. |
| Code visibility/version correspondence | Companion submissions describe the public repository and distinguish the current unreleased revision from archived v1.0.2. The repository reference omits the code-availability section as requested. No release or tag is created. |
| Old source map and numbering | Regenerated against the sole current reference: 137 active labels, 102 main and 35 appendix; all 29 theorem/proposition/lemma numbers checked from a fresh compilation. |
| Independent build and axiom outputs | Full project build passed (8733 jobs); all four audit modules and lexical/fingerprint checks passed. Actual outputs and source fingerprints are archived under `verification/2026-09-20`. |
| Language and layout | Corrected the normalized-moment limit order, explained minimum-flow attainment, fixed the initial-CDF math delimiter, replaced broad novelty comparisons by precise claims, corrected variable names, and wrapped long formulas/identifiers. |

The review found no issue requiring a change to the three main theorem statements
or their existing Lean proofs. The supporting estimates were checked with their
stated parameter ranges and order of limits, including density-weighted Taylor
remainders, the cutoff atom, the negative boundary layer, and the eight-term
auxiliary expansion used for differentiable endpoint remainders. This is a
mathematical/editorial review, distinct from the archived Lean compilation evidence.

## Qualified auxiliary coverage

- Lemma 4.8: the estimate needed by the main proof is exported; the entire displayed
  standalone lemma is not packaged as one Lean declaration.
- The displayed full-line density bound uses `q <= exp(M)/2`; the exported proof
  bound is `q^2 <= exp(M) * q`.
- The unlabelled estimate in the proof of Lemma A.2 uses `3 * 2^(-1/3)`; the Lean
  parameter Lipschitz theorem uses `3 * (3/4)^(1/3)`. Both imply the labelled
  continuity statement.

These differences are recorded rather than erased by a blanket statement that
all mathematical text is formalized verbatim. No extra mathematical axiom was added.

## Citation checks and limits

All 18 citation keys resolve to unique bibliography entries. Content-specific
checks used primary sources, including [Hambly–Jordan's author manuscript](https://people.maths.ox.ac.uk/hambly/PDF/Papers/spap.pdf),
[Chen–Derrida–Duquesne–Shi's publication](https://doi.org/10.1017/apr.2025.10023),
[Chen–Duquesne–Shi v2](https://arxiv.org/abs/2511.16880v2),
[Morfe v3](https://arxiv.org/html/2511.11036v3), and
[Audrito–Vázquez](https://arxiv.org/pdf/1601.05718). Version-specific arXiv links
are now fixed to the cited revisions. The distinction between a varying-parameter
critical window and fixed-parameter logarithmic speed is retained.

The [EGS publication metadata](https://www.aimsciences.org/article/doi/10.3934/dcds.2013.33.173)
was checked. Its complete publication text could not be retrieved in this run, and
publication theorem numbers were not independently verified. Unverified pinpoint
numbers were therefore removed; EGS remains a background/classification citation
with the explicit normalization `p=3`, `c=2 lambda`, `f(u)=2u(1-u)`. The proof of
Lemma A.2 and the bounds needed for the main theorem are self-contained. The
review's normalization check supports the additional cited upper-bound comparison;
this run does not claim to have re-proved the EGS paper. The disputed 1986/1987
Shneiberg bibliographic year was not mechanically changed.

AI and Lean declarations are retained in the reference manuscript. The reports
and reference are an unreleased revision, with the trust boundary and version
scope documented in [FORMALIZATION_REPORT.md](FORMALIZATION_REPORT.md) and
[AXIOM_REPORT.md](AXIOM_REPORT.md).
