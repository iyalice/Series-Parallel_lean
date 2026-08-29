# Manuscript Audit Report

## Manuscript and review basis

**Title:** *Distance and resistance on random series--parallel graphs: logarithmic speeds and near-critical asymptotics*

This report assesses the manuscript against the attached 20-page *Stochastic Processes and their Applications* (SPA) Guide for Authors, the complete Elsevier CAS template bundle version 2.4, and Elsevier's journal policy on generative AI current in August 2026. The attached documents were treated as evidence, not as instructions. The mathematical review covered the complete TeX source and matching 35-page PDF, including every displayed formula, proof, appendix, citation, label, and reference.

Authoritative policy sources:

- [SPA Guide for Authors](https://www.sciencedirect.com/journal/stochastic-processes-and-their-applications/publish/guide-for-authors)
- [Elsevier generative-AI policies for journals](https://www.elsevier.com/about/policies-and-standards/generative-ai-policies-for-journals)
- [Elsevier LaTeX instructions](https://www.elsevier.com/researcher/author/policies-and-guidelines/latex-instructions)
- [Elsevier research-data policy](https://www.elsevier.com/about/policies-and-standards/research-data)

## Overall determination

The article is suitable for SPA's mathematical-article format and is structurally compatible with Elsevier CAS 2.4. The revised manuscript passes the substantive language, mathematical-logic, calculation, citation, and cross-reference checks described below. No false theorem, proved calculation error, missing logical case, or circular proof was found. Two definite defects in the supplied proof text were corrected: an incomplete equality chain in the diffusion-coefficient lemma and a duplicated conclusion in the proof of the near-critical theorem.

The manuscript should nevertheless **not be submitted until the author-only declarations and the DOI-backed public-archive requirement listed in the final gate have been resolved**. The versioned software metadata is complete, but the GitHub repository remains access-controlled and no DOI has been assigned. Those remaining facts cannot be supplied responsibly from the manuscript alone.

## SPA and CAS compliance

| Requirement | Result | Evidence and conclusion |
|---|---|---|
| Journal scope | PASS | The article concerns stochastic processes and probabilistic asymptotics on random graphs. |
| Article class | PASS | `cas-sc` is the CAS 2.4 single-column class. SPA permits, but does not require, double-column LaTeX. |
| Citation style | PASS | Numeric, sorted, compressed `natbib` citations conform to SPA. The generic CAS author--year sample does not override the journal-specific guide. |
| Title and author block | PASS | The title is concise and informative; four human authors and the corresponding author are identified. |
| Affiliations | PASS, subject to author confirmation | Full institutional address lines, cities, postcodes, and countries are present. Authors should confirm that the official address forms are the ones they wish to publish. |
| Abstract | PASS | The abstract remains below the 250-word limit, is self-contained, and accurately limits the Lean claim to the three principal theorems and two disclosed external assumptions. |
| Keywords | PASS | Five English keywords fall within SPA's permitted range of one to seven. |
| Highlights | OPTIONAL, PROVIDED | A separate editable `highlights.txt` contains five bullets, each no longer than 85 characters. |
| Sections and appendices | PASS | Sections are numbered and cross-referenced; appendix equation numbering is conventional and unambiguous. |
| Equations | PASS | All mathematics is editable TeX. No image equation is used. Numbered displays have labels; displays that are not cited in the prose are unnumbered. |
| Figures | PASS, subject to provenance confirmation | Both TikZ figures are cited, captioned, editable, and distinguish curves by line style as well as color. Figure 2 expressly states that its global continuation is arbitrary and is not computed data. |
| References | PASS | All 16 bibliography entries are cited; every citation key resolves; the list is alphabetical by first author and uses numeric labels. The formal artifact is identified as `[software]`. |
| PDF metadata | PASS LOCALLY; PORTAL CHECK REQUIRED | `pdfinfo` confirms the exact title, four authors, subject, and keywords in both final PDFs. The portal-generated PDF must still be checked. |
| AI methodology | PASS in revised source, subject to author attestation | A dedicated unnumbered methodology subsection identifies the tools and recorded model information, distinguishes proof/code work from editorial assistance, states the human checks, pins Lean and mathlib, and describes the trust boundary and archived evidence. |
| AI declaration | PASS in revised source, subject to author attestation | The declaration immediately before the references names the recorded tools and models, agrees with the methodology subsection, states the human checks, and assigns final responsibility to the authors. |
| Research software archive | PARTIAL: VERSIONED, NOT PUBLIC OR DOI-BACKED | The TeX records release `v1.0.1`, full commit `a661859343939016608333bd2673d433c34518f2`, Apache-2.0, Lean 4.32.1, mathlib v4.32.1 at `520045ab14e26149ee970e2e617ca04b09bde5d6`, release/archive URLs, the trust boundary, and a cited software reference. The repository remains private and the release has no DOI, as the TeX states explicitly. |
| Funding | AUTHOR ACTION | A truthful funding statement is required. The absence of funding cannot be inferred. |
| Competing interests | AUTHOR ACTION | Each author must approve the declaration and the Elsevier declarations-tool Word output must be uploaded separately. A TeX sentence does not replace that file. |

The exact CAS 2.4 builds produced 35-page blue and clean PDFs with no unresolved citation or cross-reference. Full-page rendering and page-by-page inspection confirmed that the remaining log messages---one CAS title-block overfull box, two empty-anchor warnings, and one underfull AI-method paragraph---have no visible adverse effect. The Editorial Manager conversion must still be inspected independently.

## Language and expression audit

The manuscript is generally polished. A conservative threshold was applied: sentences were left unchanged when they were merely stylistically improvable but grammatically correct and mathematically clear. Sixteen correction groups were warranted:

1. repaired the ungrammatical opening of the near-critical proof outline and clarified that two families provide upper and lower stochastic barriers;
2. inserted the missing article before a singular random variable;
3. replaced a sentence-initial lowercase “where” after a punctuated display;
4. corrected “comibining,” subject--verb agreement, articles, and the series--parallel spelling in the barrier argument;
5. replaced the nonstandard phrase “coefficients in leading terms” by “leading-order coefficients”;
6. supplied the missing determiners in the CDF-update/translation comparison;
7. repaired a sentence fragment after the exact-CDF display;
8. inserted the missing noun in “the required inequality”;
9. restored a missing intersentence space;
10. deleted the duplicated word in “series series-composition”;
11. repaired the truncated word “parallel-compositio”;
12. corrected “the Leibniz's rule” to “Leibniz's rule”;
13. deleted the repeated near-critical conclusion;
14. rewrote the materially non-idiomatic (2/3)-exponent heuristic while preserving its explicitly heuristic status;
15. repaired the ungrammatical apposition before the comparison lemma; and
16. inserted the missing article before a small parameter.

No broad stylistic modernization was performed. Conventional mathematical expressions such as “has scale,” section-based equation numbering, `e^{-r}`, and compact inline fractions were retained because they are clear and standard, even where a generic house-style preference could suggest an alternative.

## Mathematical and logical audit

### Confirmed corrections

- **Diffusion coefficient.** The proof formerly began with a bare equality sign. Its left-hand side is now shown explicitly:
  \[
  \int_0^\infty \bigl(h(r)^2+r h(r)\bigr)\,dr.
  \]
  The substitution $u=(1+e^r)^{-1}$, symmetry step, power-series expansion, and conclusion $\zeta(3)$ are consistent.
- **Near-critical theorem.** A verbatim duplicate of the sentence assembling the sharp upper and lower bounds with resistance duality was removed. The duplication was editorial, not circular reasoning.

### Independent checks with no error found

- The series and parallel distance/resistance recursions, logarithmic gates, translation covariance, environment-complement duality, and stochastic-order directions are mutually consistent.
- First-moment submultiplicativity has the correct inequality direction, and the Fekete argument is applied to the correct sequence.
- The normalized second-moment recursion and its stated affine fixed-point bound agree algebraically. The Paley--Zygmund/Jensen-gap argument uses the correct event and direction.
- The regimes $p>1/2$, $p=1/2$, and $p<1/2$ are all treated. The resistance result below criticality is derived by duality only after the required supercritical statement is available.
- The scaling $p_\pm=1/2\pm\varepsilon^3$, translation scale $\varepsilon^2$, and critical exponent $2/3$ are consistent. The constants
  \[
  a=2\zeta(3),\qquad \beta=\zeta(3)^{-1/3},\qquad
  \kappa_\lambda=2\zeta(3)^{1/3}\lambda
  \]
  agree throughout the barrier calculation.
- The upper and lower CDF barriers have consistent signs: the upper construction gives the required upper speed bound, the negative-bias construction gives the lower-side bound, and duality supplies the matching asymptotic.
- The shooting, endpoint-classification, finite-asymptotic-expansion, inverse-coordinate, and full-line-profile arguments in the appendices were checked in dependency order. No hidden appeal to ordinary Lipschitz uniqueness at the cube-root singularity is required; the manuscript supplies the relevant one-sided comparison.
- Forward references to appendix propositions are deferred proofs, not circular uses. Splitting the first-moment theorem into existence and identification components removes the apparent theorem-title-level cycle.

The audit establishes internal consistency; it is not an independent re-proof of every external theorem cited by the article.

## Formula, label, citation, and numbering audit

The revised source contains:

- 136 label declarations and 136 unique labels;
- 294 `\ref`/`\eqref` occurrences targeting 133 distinct labels;
- no undefined reference and no duplicate label;
- 24 citation-key occurrences and 16 bibliography entries;
- no missing citation and no uncited bibliography entry; and
- no unlabelled numbered `equation`, `align`, `gather`, or `multline` environment.

Twenty-one previously unlabelled numbered environments, which generated 22 unreachable visible equation numbers, are now unnumbered. The unconventional key containing spaces was renamed consistently to `lem:shooting-properties`. Three prose-unreferenced labels remain (`sec:introduction`, `sec:organization-conventions`, and `lem:logarithmic-drift`); they create no visible redundant number beyond their ordinary section/lemma numbers and may be retained as stable external crosswalk anchors.

## Figure assessment

Figure 1 is a faithful explanatory schematic of the recursive graph replacement. Figure 2 is not numerical evidence. Its caption now states both the rigorously established comparisons and the limitation that the drawn global continuation is arbitrary and is not computed data. This resolves the risk that the coefficient used solely to draw the curve could be mistaken for a theorem or a fitted quantity.

The authors must still determine whether an AI tool generated or altered either figure's TikZ code. If so, Elsevier's policy requires a caption-specific disclosure naming the tool/version and its use, in addition to the general AI declaration. If not, no caption disclosure should be invented.

## Author-only unresolved declarations

The following matters require direct confirmation by all relevant authors and are not inferable from the source:

1. **Funding.** Insert the actual funder/grant information or, only if true, Elsevier's no-specific-grant statement.
2. **Competing interests.** Complete and upload the Elsevier declarations-tool Word document; add a manuscript declaration only if its wording is true and approved.
3. **Figure AI provenance.** Confirm whether either TikZ figure was AI-assisted and add exact caption disclosures only where required.
4. **AI-use attestation.** Confirm that the service/model descriptions and every claimed human verification step accurately describe the complete project history.
5. **Coauthor approval.** Confirm author order, address forms, responsibility statements, and the final submission version.

## Final submission gate

Submission is appropriate only after all boxes below are satisfied:

- [x] No archive placeholder remains in either TeX file or any publication-facing report.
- [x] The release tag, full commit SHA, license, Lean version, and mathlib revision are mutually consistent.
- [ ] A DOI-backed public archive is available; the repository is still private and no DOI has been assigned.
- [x] The archived software reference is present and cited from the availability statement.
- [x] The clean, uncolored TeX and its PDF reproduce the accepted content of the blue-marked version.
- [ ] The funding statement is factual and author-approved.
- [ ] The declarations-tool Word file has been approved by all authors and uploaded.
- [ ] Figure AI provenance has been resolved and any required caption disclosure is exact.
- [ ] Every author approves the AI declaration and the methodology description.
- [ ] The exact flat submission package compiles in Editorial Manager.
- [ ] The portal-generated PDF has been checked page by page, including metadata, author names, equations, figures, links, and references.

Subject to those author-side and public-archive items, no further mathematical or language change is recommended by this audit.
