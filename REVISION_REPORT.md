# Revision Report

## Scope

This report records the differences incorporated into the blue-marked manuscript
`Distance_and_resistance_SPA_revised_blue.tex` relative to the supplied source
`Distance and resistance on random series-parallel graphs.tex`. Blue text denotes
accepted additions or replacements; blue unnumbered displays denote displays whose
content or numbering status changed. The editing policy was conservative: correct,
ordinary mathematical English was left unchanged.

Supplied-source fingerprints:

- TeX SHA-256: `19430D35C597E4CC1CDD7764A7629FF5B16A9BF2ACADE72671501D399964C878`
- PDF SHA-256: `E73B5F31FA805CC05E681467775015A474D8C75B3EEA98C0EC337C704C904E73`

Final-artifact fingerprints:

- Revised blue TeX SHA-256: `030ED26637D5702F1C13E678074FEAB1E4C7ABCD06089EB0595AAC47D8C4C940`
- Revised blue PDF SHA-256: `1D162A3C85CDF0B1547FDD6A787A301106DF39256ADD474260EC012457CB050A`
- Clean submission TeX SHA-256: `D73BEEE87E90C52075C7AFC328231C9C6EFB2D82E2049823BA10768B12CF4695`
- Clean submission PDF SHA-256: `1AA12AAB03452D6AD98092225407C557CE5FD9CAEAE8DC0427AE847E74AA3CD1`

## Front matter and SPA compliance changes

| Area | Change |
|---|---|
| Affiliations | Added the official street/road and district lines for AMSS, UCAS, and SUFE while retaining the existing cities, postcodes, and country. These affiliation additions are the sole source-level differences not printed blue: CAS 2.4's affiliation parser recursed to TeX capacity when color wrappers were placed in `addressline`. The substantive values remain visible and compile correctly. |
| Abstract | Replaced the overbroad statement that “all mathematical results” were formalized with the precise statement that the companion Lean development formalizes the three principal theorems and their proof graph subject to two documented external mathematical assumptions. |
| PDF metadata | Added explicit title, four-author, subject, and keyword metadata after `\maketitle` to override defective CAS defaults. |
| Figure 2 | Added the sentence “The plotted global continuation is arbitrary and is not computed data.” No plotted value is presented as evidence. |
| AI methodology | Added an unnumbered `AI-assisted formalization methodology` subsection identifying the recorded services/model information, purposes, human review, Lean/mathlib versions, reproducibility checks, and the two-interface trust boundary. |
| Availability and software citation | Added a no-empirical-data statement and a code statement identifying release `v1.0.1`, full commit `a661859343939016608333bd2673d433c34518f2`, release and source-archive URLs, Apache-2.0, Lean 4.32.1, mathlib v4.32.1 at `520045ab14e26149ee970e2e617ca04b09bde5d6`, the trust boundary, and a cited `[software]` bibliography entry. The text accurately states that the repository is access-controlled and no DOI has been assigned. |
| End AI declaration | Replaced the overbroad preliminary disclosure with wording aligned to the methodology subsection and project record: ChatGPT with the recorded GPT-5.6 model and Codex with a GPT-5-family model assisted with specified proof, Lean, checking, crosswalk, and language tasks; the authors performed the stated checks and retain responsibility. Author attestation remains required. |

## Language and expression changes

Sixteen evidence-based correction groups were applied:

1. Recast the opening near-critical proof-outline sentence so that the two barrier families and their upper/lower roles are explicit.
2. Added the missing article in “a random variable” and removed the unnecessary comma before the restrictive clause.
3. Changed sentence-initial “where” to “Here” after a punctuated display.
4. Corrected “comibining,” repaired agreement and participial syntax, supplied articles, and standardized “series--parallel graphs.”
5. Changed “coefficients in leading terms” to “leading-order coefficients.”
6. Supplied determiners in the comparison between the CDF update and the translation.
7. Changed the post-display fragment “which proves” to the complete sentence “This proves.”
8. Inserted the missing noun in “the required inequality.”
9. Inserted the missing space between adjacent sentences in the remainder estimate.
10. Removed the duplicated word from “series series-composition.”
11. Restored the final letter in “parallel-composition.”
12. Changed “the Leibniz's rule” to “Leibniz's rule.”
13. Removed the verbatim duplicate conclusion in the near-critical theorem proof.
14. Recast the $2/3$-exponent heuristic to repair non-idiomatic phrasing, agreement, spelling, and ambiguous reference while preserving its heuristic status.
15. Replaced the faulty apposition “by the comparison principle Lemma” with a direct lemma attribution.
16. Added the missing article in “a small $\eta$.”

No global whitespace, notation, or stylistic rewrite was performed. In particular, ordinary mathematical uses of exponential notation, compact fractions, and section-based numbering were retained.

## Mathematical and logical changes

### Diffusion-coefficient calculation

The equality chain in the proof of `lem:diffusion-coefficient` formerly began with a bare `&=`. The left-hand side

\[
\int_0^\infty\bigl(h(r)^2+r h(r)\bigr)\,dr
\]

was restored. The subsequent substitution and series calculation were unchanged except for layout. The value $\zeta(3)$ was independently consistent with numerical quadrature and the zeta series.

### Near-critical assembly

One of two identical sentences combining the sharp upper bound, sharp lower bound, and resistance duality was deleted. No premise or inference changed.

### Schematic-status clarification

The Figure 2 caption now distinguishes the proved local/order statements from the arbitrary drawn continuation. The underlying curve remains a schematic aid, not computed data.

No other mathematical correction was indicated. The gate identities, first-moment bounds, Jensen-gap argument, parameter-range decomposition, near-critical constants, barrier directions, ODE analysis, and theorem dependency graph passed the audit. No circular proof was found.

## Formula numbering, labels, and citations

- Twenty-one numbered but unlabelled display environments, producing 22 visible numbers that could not be cited, were converted to unnumbered blue display environments.
- The diffusion-coefficient statement was likewise made unnumbered because the lemma, rather than the displayed identity, is the cited unit.
- The label key `lem:property of y` was renamed consistently to `lem:shooting-properties`.
- All manuscript references continue to resolve.
- The revised source has 136 unique labels, 294 `\ref`/`\eqref` occurrences, and 133 distinct referenced targets.
- There is no undefined reference, duplicate label, missing citation, or uncited bibliography item.
- Three labels remain intentionally available as external anchors although they are not cited in the prose: `sec:introduction`, `sec:organization-conventions`, and `lem:logarithmic-drift`.

## Verification record

| Check | Result |
|---|---|
| CAS 2.4 compilation | PASS; 35 pages in both blue and clean outputs |
| Undefined/multiply defined references | PASS; none |
| Missing/uncited bibliography entries | PASS; none |
| Unlabelled numbered equation-like environments | PASS; none |
| Visible formula overlap or clipping | PASS; all 35 pages of both PDFs were rendered and inspected |
| Mathematical calculation and dependency review | PASS with the two local corrections recorded above |
| Conservative English-language review | PASS after 16 correction groups |
| Final clean source/PDF | PASS; clean TeX and PDF compile independently, and extracted PDF text is identical to the blue PDF |
| Source-map and manuscript--Lean crosswalk | PASS; 136 unique labels, 98 main and 38 appendix, with all physical line anchors verified; all 29 labelled theorem-like statements appear exactly once in the correspondence report |
| Frozen Lean build and axiom fingerprints | PASS; full build succeeded with 8,733 jobs, the placeholder audit found 80 Lean files and exactly two project axioms, and deterministic/samplewise bridge fingerprints contain no project axiom |
| Public release/DOI link verification | PARTIAL; the versioned release is `v1.0.1` at the recorded full SHA, but the GitHub repository is private, anonymous access is unavailable, and no DOI has been assigned |

The final blue and clean logs contain only one CAS title-block overfull box, two empty-anchor warnings at the title block, and one underfull paragraph in the AI-method subsection. Fresh compilation and rendered-page inspection after metadata integration confirmed that these messages have no visible adverse effect.

## Author confirmation required

The following facts were deliberately not invented or inferred:

1. funding and sponsor-role status;
2. each author's competing interests and the declarations-tool Word output;
3. whether either TikZ figure was generated or altered with AI;
4. final approval of tool/model descriptions and claimed human verification steps;
5. final author approval of postal address forms, author order, responsibility statements, and submission files.

If either figure was AI-assisted, its caption requires a factual tool/version/use disclosure. If no figure was AI-assisted, no disclosure should be added. If no specific grant supported the work, the journal's recommended no-specific-grant sentence may be used only after author confirmation.

## Archive status

The TeX contains no literal archive placeholder. Repository and release URLs, release tag, full
commit SHA, license, Lean version, mathlib revision, data/code statements, software citation, and
AI disclosures are internally consistent. The clean and blue sources differ substantively only in
the revision-color switch, and the hashes above were computed after final metadata integration.
The remaining archive limitation is external: the repository is private and the release has no
DOI, so it is not anonymously verifiable or DOI-backed.
