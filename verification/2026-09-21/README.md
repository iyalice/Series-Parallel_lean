# Verification record — 2026-09-21

This record accompanies the author's final manuscript synchronization and an
unreleased report revision. All 80 Lean sources and all pinned dependency
configuration are unchanged from commit `5afa967ce186ddba102d6801152330541e2b0d34`.
No release, tag, or version bump was made; the package version remains 1.0.2.
The preceding dated verification record remains historical and is not overwritten.

## Environment and actual results

Windows, Lean 4.32.1, Lake 5.0.0, and mathlib v4.32.1 at commit
`520045ab14e26149ee970e2e617ca04b09bde5d6` were used. All nine dependency
checkouts were checked against the pinned manifest. Existing compiled artifacts
were reused; this is not a claim to rebuild mathlib from scratch.

| Check | Actual result | Evidence |
|---|---|---|
| Full project build | PASS, 8733 jobs | [lake-build.log](lake-build.log) |
| Scalar public theorem audit | PASS, exit 0 | [main-text-axioms.log](main-text-axioms.log) |
| Traditional graph and bridge audit | PASS, exit 0 | [graph-semantics-axioms.log](graph-semantics-axioms.log) |
| Appendix audit | PASS, exit 0 | [appendix-axioms.log](appendix-axioms.log) |
| Joint-coverage audit | PASS, exit 0 | [joint-coverage-axioms.log](joint-coverage-axioms.log) |
| Lexical audit | PASS, 80 Lean files, two project axioms | [lexical-audit.log](lexical-audit.log), [declarations](project-axioms.tsv) |
| Scalar fingerprints | PASS, three public declarations | [project-axiom-check.log](project-axiom-check.log) |
| Joint/graph fingerprints | PASS, three joint declarations and ten graph/bridge fingerprints | [joint-coverage-check.log](joint-coverage-check.log) |
| Reference correspondence | PASS, 137 active labels, 29 numbered results; 17 cited keys resolve among 18 bibliography entries | [manuscript-check.log](manuscript-check.log) |
| Three-way synchronization | PASS, 140 raw label lines and all compiled label numbers agree | [manuscript-sync.json](manuscript-sync.json) |
| Journal compilation | PASS, 35 pages | [spa-latex.log](spa-latex.log) |
| arXiv compilation | PASS, 41 pages | [arxiv-latex.log](arxiv-latex.log) |
| Reference compilation | PASS, 41 pages | [reference-latex.log](reference-latex.log) |

The authoritative journal source is `Series-Parallel_SPA_submission_final.tex`;
it was not edited. Its SHA-256 is
`5e6a5a46bfc469d43e12414ef002d00a1d75f19fd3fad14ba842d0a2cdf594e3`.
The arXiv companion is `Series-Parallel_arxiv_submission.tex`, SHA-256
`4974aa7d0b44de3cee8a528fdedc96c72d379130dd8e1b4f18a265cfe4023418`.
The sole repository reference is `SeriesParallel.tex`, SHA-256
`3ae0cbb7743bd3fe4241b71cf3bc56dd67a99f9483cc6b1e00b965bdd1bc363a`.
Hashes refer to UTF-8, LF-normalized source. The synchronization JSON also records
the file-byte hashes of the local companion sources.

The arXiv abstract and the complete source from Introduction through the end of
the document equal the author's final journal source exactly. Its class remains
`amsart`; author, affiliation, title, and keyword content are carried in that
class's format. Header comments align the introduction without editing the journal
source. The reference equals arXiv with only the marked code-availability block
replaced by the same number of comment lines. AI and Lean declarations remain.
Removing that block removes the only citation of the archived software entry from
the reference, while preserving the author's complete 18-entry bibliography.

All 29 numbered theorem/proposition/lemma statements are unchanged from the previous
reference. All 137 active labels (102 main, 35 appendix) have current source-map
positions; the 140 raw occurrences also include three commented labels.
Theorem 1.3 retains joint coverage in the reports. The audit no longer requires
injecting the internal halfline theorem's identifier into the author's manuscript.

## Layout inspection

Both arXiv-format PDFs were rendered in full and checked in contact sheets.
Their first 38 rendered pages are byte-identical; the final pages differ because
of the requested removal of code availability. First pages, the EGS comparison,
endpoint discussion, code availability, and declarations were inspected separately.
No clipping, overlapping text, or overfull boxes was found in either arXiv-format
build. Their only LaTeX warning is microtype's unavailable footnote patch.
The unchanged journal template retains its existing frontmatter box and
empty-anchor warnings. There are no undefined references/citations in any build.
The archived LaTeX logs are the complete final-pass engine logs; the Lean build
retains its actual linter/style diagnostics. Stored log line endings are normalized
to LF and trailing whitespace is removed; no diagnostic lines are omitted.

## Reproduction

From the repository root with the pinned environment:

```sh
lake build
lake env lean SeriesParallel/MainTextAudit.lean > main-text-axioms.out
lake env lean SeriesParallel/GraphSemanticsAudit.lean > graph-semantics-axioms.out
lake env lean SeriesParallel/Audit.lean > appendix-axioms.out
lake env lean SeriesParallel/JointCoverageAudit.lean > joint-coverage-axioms.out
python scripts/audit_lean_placeholders.py --axiom-manifest project-axioms.tsv SeriesParallel.lean SeriesParallel
python scripts/audit_project_axioms.py --declarations project-axioms.tsv --fingerprints main-text-axioms.out
python scripts/check_joint_coverage.py --joint joint-coverage-axioms.out --graph graph-semantics-axioms.out
latexmk -pdf -interaction=nonstopmode -halt-on-error SeriesParallel.tex
python scripts/check_manuscript.py --aux SeriesParallel.aux
```

Use UTF-8 for redirected output. The optional `--spa PATH --arxiv PATH` pair
additionally checks companion equality and all raw label lines.

`source-sha256.tsv` fingerprints the Lean sources, pinned configuration, audit
scripts, reference, and current reports using LF-normalized UTF-8. The environment
and source baseline are recorded in `environment.log`. `evidence-sha256.tsv`
fingerprints this record, the stored outputs, and the source manifest as file bytes.

These checks establish the stated compilation, correspondence, and trust boundary.
They do not prove the two external mathematical inputs inside Lean or turn every
auxiliary manuscript constant or literature comparison into a formalized theorem.
