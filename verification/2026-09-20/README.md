# Verification record — 2026-09-20

This record accompanies an unreleased manuscript/report revision. The proof source
baseline is commit `3c9592d72c8c5a77f8c47ecbbfc1c13b69264416`; every existing Lean
source is unchanged. The only added Lean module is `SeriesParallel/JointCoverageAudit.lean`.
The repository's package version remains 1.0.2; this record does not create a release.

## Environment and results

The run used Windows, Lean 4.32.1, Lake 5.0.0, and mathlib v4.32.1, commit
`520045ab14e26149ee970e2e617ca04b09bde5d6`. The nine dependency checkouts were
checked against `lake-manifest.json`. Existing dependency artifacts were reused;
this was a fresh project build, not a claim to have rebuilt all of mathlib from source.

| Check | Actual result | Evidence |
|---|---|---|
| Full project build | PASS, 8733 jobs | [lake-build.log](lake-build.log) |
| Scalar public theorem audit | PASS, exit 0 | [main-text-axioms.log](main-text-axioms.log) |
| Traditional graph and bridge audit | PASS, exit 0 | [graph-semantics-axioms.log](graph-semantics-axioms.log) |
| Appendix public theorem audit | PASS, exit 0 | [appendix-axioms.log](appendix-axioms.log) |
| Joint-coverage audit | PASS, exit 0 | [joint-coverage-axioms.log](joint-coverage-axioms.log) |
| Lexical audit | PASS, 80 Lean files, two project axioms | [lexical-audit.log](lexical-audit.log), [manifest](project-axioms.tsv) |
| Scalar fingerprints | PASS, three public theorems | [project-axiom-check.log](project-axiom-check.log) |
| Joint and graph fingerprints | PASS, three joint declarations and ten graph/bridge fingerprints | [joint-coverage-check.log](joint-coverage-check.log) |
| Manuscript correspondence | PASS, 137 active labels, 29 numbered results, 18 citations | [manuscript-check.log](manuscript-check.log) |

`source-sha256.tsv` fingerprints the 80 Lean sources, pinned configuration,
audit scripts, and reference manuscript with LF-normalized UTF-8 text. The
reference manuscript SHA-256 is
`2906514bd64faa6f59fe7d9c12ad06ddc0200e8f6c8116aadb9e3e0af8660ba2`.
`evidence-sha256.tsv` fingerprints the archived verification outputs as stored.
Log line endings are normalized to LF and trailing whitespace is removed;
no diagnostic lines are omitted.

The main build emitted linter/style suggestions but no errors. The freshly compiled
reference manuscript has 41 pages and no undefined references/citations or overfull
boxes. The only reference-TeX warning is microtype's unavailable footnote patch.
All pages were rendered for visual review, with first/end pages and long formulas
inspected more closely. The companion journal source has a class-generated
frontmatter box warning and empty-anchor warnings; visual inspection found no
clipping. Its body has no overfull boxes.

## Reproduction

From the repository root, with the pinned Lean toolchain and dependencies available:

```sh
lake build
lake env lean SeriesParallel/MainTextAudit.lean > main-text-axioms.out
lake env lean SeriesParallel/GraphSemanticsAudit.lean > graph-semantics-axioms.out
lake env lean SeriesParallel/Audit.lean > appendix-axioms.out
lake env lean SeriesParallel/JointCoverageAudit.lean > joint-coverage-axioms.out
python scripts/audit_lean_placeholders.py --axiom-manifest project-axioms.tsv SeriesParallel.lean SeriesParallel
python scripts/audit_project_axioms.py --declarations project-axioms.tsv --fingerprints main-text-axioms.out
python scripts/check_joint_coverage.py --joint joint-coverage-axioms.out --graph graph-semantics-axioms.out
latexmk -pdf -interaction=nonstopmode -halt-on-error Series_Parallel.tex
python scripts/check_manuscript.py --aux Series_Parallel.aux
```

Use a shell that writes redirected Lean output as UTF-8. The optional
`--spa PATH --arxiv PATH` arguments to `check_manuscript.py` additionally verify
companion-body/abstract identity and all 140 raw label occurrences (including
commented labels). The reference differs from the arXiv companion only by the
comment-padded removal of the marked code-availability block.

These checks establish compilation and the reported correspondence and trust
boundary. They are not a claim that the two declared external mathematical inputs
were proved inside Lean, or that every auxiliary manuscript constant is exported
verbatim. See the correspondence report for those qualifications.
