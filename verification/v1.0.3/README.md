# Release verification — v1.0.3

Release date: 2026-09-21. The release includes the author's subsequent AI
contribution statement and README edits from `cb8eee0df95548a228d6d8d2d7707a20b247997a`.
The reference remains `SeriesParallel.tex`, with AI and Lean declarations and no
code-availability section. The package version, software citation, and release
metadata are updated to 1.0.3.

## Checks performed for this release

| Check | Result | Evidence |
|---|---|---|
| Build with release package metadata | PASS, 8733 jobs | [lake-build.log](lake-build.log) |
| Current reference compilation | PASS, 41 pages; no undefined references/citations or overfull boxes | [reference-latex.log](reference-latex.log) |
| Source-map and compiled numbering | PASS, 137 active labels and 29 numbered results | [manuscript-check.log](manuscript-check.log) |
| Lexical placeholder/escape audit | PASS, 80 Lean files, two declared project axioms | [lexical-audit.log](lexical-audit.log), [manifest](project-axioms.tsv) |
| Scalar project-axiom check | PASS, three fingerprints | [project-axiom-check.log](project-axiom-check.log) |
| Joint-coverage and graph check | PASS, three joint declarations, ten graph/bridge fingerprints | [joint-coverage-check.log](joint-coverage-check.log) |
| Pinned environment | All nine dependency revisions match the manifest | [environment.log](environment.log) |
| Reference versus author's final arXiv source | Same active text apart from code availability and the synchronized software citation; all 137 active label lines agree | [source manifest](source-sha256.tsv) |

All 80 project Lean files are hash-identical to those in the
[2026-09-21 verification](../2026-09-21/README.md). The release's scalar and
joint/graph fingerprint checks consume that record's actual Lean axiom outputs;
the four audit modules were not rerun for this metadata-only release. Their
evidence remains applicable to the unchanged Lean files and pinned toolchain.
The full Lake build, lexical audit, reference compilation, and manuscript check
were run again for the release. Existing dependency artifacts were reused.

The reference SHA-256 (UTF-8, LF-normalized) is
`a5034c47dea2bbe6d47af58dea3154ea9a74db5d165bbd695d6f6fcd5955b677`.
The final arXiv source removes historical comments, so raw commented-label counts
need not agree. Active labels and source positions agree. Only whitespace differs
in the author's AI contribution statement. The software citation is updated to
v1.0.3 in both manuscripts; the arXiv code-availability block receives the release
URL, source archive URL, and fixed commit after publication.

The reference's first page and software bibliography entry were rendered and
visually inspected. The only LaTeX warning is microtype's unavailable footnote
patch. Complete final-pass TeX and Lake logs are included; trailing whitespace
and line endings are normalized, without omitting diagnostic lines.

Theorem 1.3 remains covered jointly by the public near-critical result and
`mainAdmissible_eq_Ici_lambdaStar`, including the traditional graph version.
The two external inputs and qualified auxiliary coverage are unchanged. No new
mathematical axiom, theorem statement, or proof implementation was introduced.

## Reproduction

```sh
lake build
latexmk -pdf -interaction=nonstopmode -halt-on-error SeriesParallel.tex
python scripts/check_manuscript.py --aux SeriesParallel.aux
python scripts/audit_lean_placeholders.py --axiom-manifest project-axioms.tsv SeriesParallel.lean SeriesParallel
python scripts/audit_project_axioms.py --declarations project-axioms.tsv --fingerprints verification/2026-09-21/main-text-axioms.log
python scripts/check_joint_coverage.py --joint verification/2026-09-21/joint-coverage-axioms.log --graph verification/2026-09-21/graph-semantics-axioms.log
```

The preceding record documents commands for rerunning all four Lean axiom audits.
`source-sha256.tsv` fingerprints the current Lean sources, pinned configuration,
scripts, reference, and reports. `evidence-sha256.tsv` fingerprints the stored
release evidence as file bytes. Historical verification records are unchanged.
