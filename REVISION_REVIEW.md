# Response to the strict review — 2026-09-21

The sole repository reference is `SeriesParallel.tex`, derived from the arXiv
companion of the author's final journal source. The author's final wording is
authoritative. This synchronization does not reapply earlier editorial proposals.
The original strict review concerned an earlier 35-page PDF and release v1.0.2;
its recommendations are distinguished below from the author's accepted text.

## Review findings and disposition

| Review issue | Current disposition |
|---|---|
| Lemma A.2 initial/terminal-value citation | The final manuscript contains its self-contained existence, comparison, uniqueness, positivity, parameter order, and continuity proof. The real-cube-root convention appears before the comparison lemma. No mismatched EGS initial-value clause is used as its proof. |
| Formalization scope | The abstract and methodology refer to the three main theorems and their proof dependencies relative to two documented inputs. The final author's wording is retained; the reports state the trust boundary explicitly. |
| Theorem 1.3 halfline clause | The corresponding tables retain joint coverage by the near-critical theorem and `mainAdmissible_eq_Ici_lambdaStar`, including the traditional graph wrapper. The existing audit checks each declaration. No extra coverage paragraph is inserted in the manuscript. |
| Remark 4.11 | The final text retains scale balance and omits the unsupported inference from signed increments to iterated CDF comparability. It uses “one-step expansion” in this explanation. |
| Remark 1.5 | The author's generic slowly varying CDF discussion is retained, together with the diffusion-coefficient lemma reference. The earlier proposed explicit profile specialization was withdrawn; the report does not claim it remains in this remark. The rigorous comparison results carry their own profile assumptions. |
| Flow minimizer and limits | The final text uses a bounded-energy minimizing sequence and a convergent subsequence to explain attainment, and states the order of the normalized-moment limits. |
| Endpoint inequality | The final formula in Proposition A.6 ends in a non-strict inequality, including the zero endpoint. The previously proposed extra explanatory sentence was withdrawn. |
| EGS comparison | Published Proposition 2, Lemma 3.1(a), and Theorem 3.3 support the specific comparisons described below. The author's shortened wording is preserved. |
| Source map and filename | Regenerated against `SeriesParallel.tex`: 137 active labels, 102 main and 35 appendix. All 140 raw label lines agree across journal, arXiv, and reference sources. All 29 numbered result statements are unchanged from the previous reference. |
| Code availability | The repository reference omits this block with comment padding. The journal and arXiv companions retain identical author-approved code-availability text, including its link to the preceding revision; this update does not silently replace that link. The current reference and evidence are identified by their stored hashes. |
| Build and trust boundary | No Lean sources or external hypotheses changed. Current verification results and fingerprints are recorded under `verification/2026-09-21`; the previous dated evidence is preserved. |

## Qualified auxiliary coverage

- Lemma 4.8: Lean exports the estimate used by the main proof; the complete
  displayed standalone lemma is not packaged as one declaration.
- The full-line density bound in the manuscript is `q <= exp(M)/2`; the exported
  proof bound is `q^2 <= exp(M) * q`.
- The unlabelled estimate in Lemma A.2's proof uses `3 * 2^(-1/3)`; the Lean
  parameter Lipschitz estimate uses `3 * (3/4)^(1/3)`. Both imply the labelled
  continuity statement.

These qualifications and Theorem 1.3's joint coverage remain explicit in the
correspondence and source-map tables. No additional mathematical axiom was added.

## Published EGS comparison and scope

The author's supplied publication is Enguiça, Gavioli, and Sanchez,
*Discrete and Continuous Dynamical Systems* 33 (2013), 173–191,
[doi:10.3934/dcds.2013.33.173](https://doi.org/10.3934/dcds.2013.33.173).
The supplied PDF has SHA-256
`54dc70830da33f313873853be1e28c34291cbac524b454a88cc1d9109c83919c`.
The preceding publication-text review superseded the earlier report's
metadata-only limitation. Its relevant published locators are:

- Proposition 2, p.176: existence/uniqueness classification and the upper bound.
  With `p=3`, `q=3/2`, `c=2 lambda`, and `f(u)=2u(1-u)`, the parameter
  `mu = 4/(3 sqrt(3))` gives `lambdaStar <= 2^(-1/3)`.
- Lemma 3.1(a), p.177: its quantitative lower bound is zero for this nonlinearity.
  This does not deny EGS's qualitative positivity of the critical parameter.
  The manuscript's explicit positive lower bound is obtained by its own integral estimate.
- Theorem 3.3, p.181: part (b) agrees with the critical asymptotic; part (a)
  gives `W_lambda(u) = o(sqrt(u))` in the supercritical case. The manuscript
  proves the more precise asymptotic `W_lambda(u) ~ u/lambda` and differentiable
  remainder estimates.

The publication locators are not the differently numbered accepted-manuscript
locators discussed in the original strict review. The final manuscript's
self-contained proof of Lemma A.2 remains its proof dependency.

This update synchronizes the author's accepted text and rechecks its references
and compiled numbering mechanically. It does not claim a new comprehensive
literature search or a Lean formalization of the cited papers. The previous
checks of other cited works are not represented as newly repeated checks here.
AI and Lean declarations remain, and no release or tag is created.
