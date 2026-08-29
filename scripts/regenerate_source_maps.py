#!/usr/bin/env python3
"""Regenerate the manuscript-to-Lean source maps from the active SPA TeX source.

The parser removes TeX comments and literal ``\\iffalse`` branches while preserving physical
line numbers.  Existing per-label Lean metadata is retained only for labels that remain active;
new or renamed labels require an explicit entry in ``METADATA_OVERRIDES`` below.

The generated files are:

* ``SOURCE_MAP.md`` -- every active label, in TeX order;
* ``MAIN_TEXT_SOURCE_MAP.md`` -- the main-text subset before ``\\appendix``;
* ``MANUSCRIPT_LEAN_CORRESPONDENCE.md`` -- every labelled theorem-like environment.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
import re
import sys


LABEL_RE = re.compile(r"\\label\{([^{}]+)\}")
REFERENCE_RE = re.compile(r"\\(?:eqref|ref|autoref|cref|Cref)\{([^{}]+)\}")
CONDITIONAL_RE = re.compile(r"\\(iffalse|if[a-zA-Z@]+|else|fi)\b")
BEGIN_END_RE = re.compile(r"\\(begin|end)\{([^{}]+)\}")
APPENDIX_RE = re.compile(r"\\appendix\b")
DECLARATION_RE = re.compile(
    r"^\s*(?:(?:public|private|protected|noncomputable|unsafe)\s+)*"
    r"(?:theorem|lemma|def|abbrev|axiom|structure|class|inductive)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)\b"
)
STRUCTURE_FIELD_RE = re.compile(r"^\s{2}([A-Za-z_][A-Za-z0-9_']*)\s*:")

THEOREM_KINDS = {"theorem", "proposition", "lemma", "corollary"}
EQUATION_ENVS = {"equation", "equation*", "align", "align*", "gather", "gather*",
                 "multline", "multline*", "revequation", "revalign"}


@dataclass(frozen=True)
class Metadata:
    kind: str
    implementation_owner: str
    declarations: str
    module: str
    status: str
    trust: str


@dataclass(frozen=True)
class LabelRow:
    label: str
    line: int
    owner: str
    environment: str | None


METADATA_OVERRIDES: dict[str, Metadata] = {
    "fig:series-parallel-replacement": Metadata(
        "figure", "manuscript", "—", "—", "doc-only", "doc-only"
    ),
    "low_barrier_init": Metadata(
        "equation",
        "main",
        "hardEdgeScaledLaw_initial_CDFOrdered",
        "MainText.HardEdgeConsistency",
        "proved",
        "internal/mathlib; MI01-transitive after profile instantiation",
    ),
    "low_one_step": Metadata(
        "equation",
        "main",
        "hard_edge_global_lower_barrier",
        "MainText.HardEdgeConsistency",
        "proved",
        "internal/mathlib; MI01-transitive after profile instantiation",
    ),
    "lem:shooting-properties": Metadata(
        "lemma",
        "appendix",
        "shootingProperties",
        "Appendix.Shooting",
        "proved",
        "internal/mathlib; MI01-transitive after profile instantiation",
    ),
    "thm:logarithmic-speeds": Metadata(
        "theorem",
        "main",
        "GraphSemantics.graphLogarithmicSpeeds; logarithmicSpeeds",
        "MainText.GraphSemantics.MainTheorems; MainText.MainTheorems",
        "proved",
        "internal/mathlib + distanceGamma_half_eq_zero",
    ),
    "thm:first-moment-logarithmic-rates": Metadata(
        "theorem",
        "main",
        "GraphSemantics.graphFirstMomentLogarithmicRates; firstMomentLogarithmicRates",
        "MainText.GraphSemantics.MainTheorems; MainText.MainTheorems",
        "proved",
        "internal/mathlib + distanceGamma_half_eq_zero",
    ),
    "thm:near-critical-speed": Metadata(
        "theorem",
        "main",
        "GraphSemantics.graphResistanceSpeedNearCritical; resistanceSpeedNearCritical",
        "MainText.GraphSemantics.MainTheorems; MainText.ResistanceNearCritical",
        "proved",
        "internal/mathlib + MI01_global_peano_on_compact_interval",
    ),
    "prop:full-line-distribution": Metadata(
        "proposition",
        "appendix/façade",
        "full_line_distribution; full_line_density_probability",
        "MainText.ProfileFacade; Appendix.ProfileMeasures",
        "proved (façade)",
        "internal/mathlib; MI01-transitive after profile instantiation",
    ),
    "prop:hard-edge-distribution": Metadata(
        "proposition",
        "appendix/façade",
        "hard_edge_distribution; hard_edge_density_probability",
        "MainText.ProfileFacade",
        "proved (façade)",
        "internal/mathlib; MI01-transitive after profile instantiation",
    ),
    "lem:logarithmic-drift": Metadata(
        "lemma",
        "main",
        "X_succ_hasLaw; logarithmic_drift",
        "MainText.LogarithmicDrift",
        "proved",
        "internal/mathlib",
    ),
    "lem:exact-cdf": Metadata(
        "lemma",
        "main",
        "exact_cdf_operator_density; cdfOperator_mono_of_CDFOrdered; cdfOperator_translate",
        "MainText.DensityGateRegions; MainText.GeneralizedInverseCoupling; MainText.CDFOperator",
        "proved",
        "internal/mathlib",
    ),
    "lem:first-moment-submultiplicativity": Metadata(
        "lemma",
        "main",
        "firstMoment_submultiplicative; normalizedLogFirstMoment_tendsto_feketeLimit",
        "MainText.FirstMomentSubmultiplicative",
        "proved",
        "internal/mathlib",
    ),
    "prop:bounded-Jensen-gap": Metadata(
        "proposition",
        "main",
        "jensenGap_le_uniform_bound; normalizedMeanLog_tendsto_firstMomentLimit",
        "MainText.JensenAndCenter",
        "proved",
        "internal/mathlib",
    ),
    "lem:center-tracking": Metadata(
        "lemma",
        "main",
        "centered_X_uniform_bound; centered_X_ae_tendsto_zero_signed; centered_X_div_L1_tendsto_zero",
        "MainText.JensenAndCenter",
        "proved",
        "internal/mathlib",
    ),
    "prop:Cstar-halfline": Metadata(
        "proposition",
        "appendix",
        "cstarHalfline; existsUnique_boundarySolution_iff_lambdaStar_le; lambdaLower_eq_rpow",
        "Appendix.AdmissibleHalfline; Appendix.AdmissibleParameters",
        "proved",
        "internal/mathlib + MI01_global_peano_on_compact_interval",
    ),
    "lem:u0-dichotomy": Metadata(
        "lemma",
        "appendix",
        "leftEndpointDichotomy_source",
        "Appendix.LeftEndpointDichotomy",
        "proved",
        "internal/mathlib; MI01-transitive after profile instantiation",
    ),
}

# Direct `#print axioms` fingerprints for all theorem-like rows. `standard` abbreviates
# `propext`, `Classical.choice`, and `Quot.sound`.
THEOREM_TRUST: dict[str, str] = {
    "thm:logarithmic-speeds": "standard + distanceGamma_half_eq_zero",
    "thm:first-moment-logarithmic-rates": "standard + distanceGamma_half_eq_zero",
    "thm:near-critical-speed": "standard + MI01_global_peano_on_compact_interval",
    "lem:logarithmic-drift": "standard",
    "prop:conditional-refinement": "standard",
    "lem:deterministic-bound": "standard",
    "lem:first-moment-bounds": "standard",
    "lem:resistance-duality": "standard",
    "lem:exact-cdf": "standard",
    "lem:first-moment-submultiplicativity": "standard",
    "prop:bounded-Jensen-gap": "standard",
    "lem:center-tracking": "standard",
    "lem:normalized-L2": "standard",
    "lem:diffusion-coefficient": "standard",
    "prop:full-line-distribution": "standard + MI01_global_peano_on_compact_interval",
    "prop:hard-edge-distribution": "standard + MI01_global_peano_on_compact_interval",
    "lem:weighted-consistency": "standard",
    "lem:upper-cutoff-error": "standard",
    "lem:hard-edge-consistency": "standard",
    "prop:hard-edge-barrier": "standard",
    "lem:cuberoot-comparison": "standard",
    "lem:shooting-properties": "standard + MI01_global_peano_on_compact_interval",
    "prop:Cstar-halfline": "standard + MI01_global_peano_on_compact_interval",
    "prop:subcritical-W": "standard + MI01_global_peano_on_compact_interval",
    "lem:linear-u1": "standard + MI01_global_peano_on_compact_interval",
    "lem:u0-dichotomy": "standard + MI01_global_peano_on_compact_interval",
    "prop:critical-branches": "standard + MI01_global_peano_on_compact_interval",
    "lem:finite-asymptotic-ode": "standard",
    "lem:linear-branch-regularity": "standard",
}

ROW_TRUST_OVERRIDES: dict[str, str] = {
    "eq:full-range-L1": "standard + distanceGamma_half_eq_zero",
    "eq:supercritical-speed-bounds": "standard",
    "eq:resistance-first-moment-dichotomy": "standard",
    "eq:supercritical-resistance-identification": "standard",
    "eq:main-W-bvp": "standard + MI01_global_peano_on_compact_interval",
    "eq:main-near-critical-limit": "standard + MI01_global_peano_on_compact_interval",
    "eq:resistance-first-moment-near-critical":
        "standard + MI01_global_peano_on_compact_interval",
    "eq:distance-nonpositive-annealed-speed": "standard",
}

REQUIRED_CORRESPONDENCE_DECLARATIONS = {
    "graphLogarithmicSpeeds",
    "graphFirstMomentLogarithmicRates",
    "graphResistanceSpeedNearCritical",
    "graphLogarithmicSpeedsStatement_iff",
    "graphFirstMomentLogarithmicRatesStatement_iff",
    "graphResistanceSpeedNearCriticalStatement_iff",
    "traditionalDistance_realize",
    "traditionalResistance_realize",
    "graphDistanceValue_eq_distanceValue",
    "graphResistanceValue_eq_resistanceValue",
    "graphZ_eq_Z",
    "graphX_eq_X",
}


def strip_tex_comments(text: str) -> str:
    """Remove comments while retaining every newline and therefore every physical line."""
    output: list[str] = []
    for line in text.splitlines(keepends=True):
        cut = len(line)
        for index, char in enumerate(line):
            if char != "%":
                continue
            backslashes = 0
            cursor = index - 1
            while cursor >= 0 and line[cursor] == "\\":
                backslashes += 1
                cursor -= 1
            if backslashes % 2 == 0:
                cut = index
                break
        kept = line[:cut]
        if line.endswith("\n") and not kept.endswith("\n"):
            kept += "\n"
        output.append(kept)
    return "".join(output)


def strip_inactive_iffalse(text: str) -> str:
    """Blank literal false branches without changing offsets or line numbers."""
    output = list(text)
    cursor = 0
    while True:
        opener = re.search(r"\\iffalse\b", text[cursor:])
        if opener is None:
            break
        start = cursor + opener.start()
        match = CONDITIONAL_RE.match(text, start)
        assert match is not None
        depth = 1
        active = False
        scan = match.end()
        for index in range(start, scan):
            if output[index] != "\n":
                output[index] = " "
        while depth and scan < len(text):
            token = CONDITIONAL_RE.search(text, scan)
            end = token.start() if token is not None else len(text)
            if not active:
                for index in range(scan, end):
                    if output[index] != "\n":
                        output[index] = " "
            if token is None:
                raise ValueError("unterminated \\iffalse branch")
            command = token.group(1)
            token_end = token.end()
            if command.startswith("if"):
                depth += 1
            elif command == "fi":
                depth -= 1
            elif command == "else" and depth == 1:
                active = not active
            for index in range(token.start(), token_end):
                if output[index] != "\n":
                    output[index] = " "
            scan = token_end
        cursor = scan
    return "".join(output)


def active_tex(text: str) -> str:
    return strip_inactive_iffalse(strip_tex_comments(text))


def line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def environment_at_labels(text: str) -> dict[int, str | None]:
    """Return the innermost open environment at each label offset."""
    tokens: list[tuple[int, str, str]] = []
    tokens.extend((match.start(), match.group(1), match.group(2)) for match in BEGIN_END_RE.finditer(text))
    tokens.extend((match.start(), "label", match.group(1)) for match in LABEL_RE.finditer(text))
    tokens.sort(key=lambda token: token[0])
    stack: list[str] = []
    result: dict[int, str | None] = {}
    for offset, command, value in tokens:
        if command == "begin":
            stack.append(value)
        elif command == "end":
            if not stack or stack[-1] != value:
                raise ValueError(f"environment stack mismatch near line {line_number(text, offset)}: {value}")
            stack.pop()
        else:
            result[offset] = stack[-1] if stack else None
    return result


def parse_labels(text: str) -> tuple[list[LabelRow], int]:
    appendix_match = APPENDIX_RE.search(text)
    if appendix_match is None:
        raise ValueError("missing \\appendix boundary")
    appendix_line = line_number(text, appendix_match.start())
    environments = environment_at_labels(text)
    rows: list[LabelRow] = []
    for match in LABEL_RE.finditer(text):
        line = line_number(text, match.start())
        rows.append(LabelRow(
            match.group(1), line, "main" if line < appendix_line else "appendix",
            environments[match.start()],
        ))
    return rows, appendix_line


def classify(row: LabelRow) -> str:
    label = row.label
    if label.startswith(("sec:", "app:")):
        return "section"
    if label.startswith("fig:"):
        return "figure"
    if label.startswith("thm:"):
        return "theorem"
    if label.startswith("lem:"):
        return "lemma"
    if label.startswith("prop:"):
        return "proposition"
    if label.startswith("cor:"):
        return "corollary"
    if label.startswith("rem:"):
        return "remark"
    if row.environment in THEOREM_KINDS | {"remark", "figure", "figure*"}:
        return row.environment.removesuffix("*")
    return "equation"


def validate_environments(rows: list[LabelRow]) -> list[str]:
    errors: list[str] = []
    for row in rows:
        kind = classify(row)
        if kind in THEOREM_KINDS and row.environment != kind:
            errors.append(
                f"{row.label} at line {row.line}: kind={kind}, open environment={row.environment}"
            )
        if kind == "figure" and row.environment not in {"figure", "figure*"}:
            errors.append(
                f"{row.label} at line {row.line}: figure label outside figure environment"
            )
        if kind == "equation" and row.environment not in EQUATION_ENVS:
            errors.append(
                f"{row.label} at line {row.line}: equation label in {row.environment!r}"
            )
    return errors


def parse_existing_metadata(path: Path) -> dict[str, Metadata]:
    result: dict[str, Metadata] = {}
    if not path.exists():
        return result
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.startswith("| `"):
            continue
        cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
        if len(cells) != 8 or not cells[0].startswith("`"):
            continue
        label = cells[0].strip("`")
        result[label] = Metadata(
            kind=cells[2],
            implementation_owner=cells[3],
            declarations=cells[4].strip("`"),
            module=cells[5].strip("`"),
            status=cells[6],
            trust=cells[7],
        )
    return result


def metadata_for(rows: list[LabelRow], previous: dict[str, Metadata]) -> dict[str, Metadata]:
    metadata: dict[str, Metadata] = {}
    unknown: list[str] = []
    for row in rows:
        if row.label in METADATA_OVERRIDES:
            entry = METADATA_OVERRIDES[row.label]
        elif row.label in previous:
            entry = previous[row.label]
        else:
            unknown.append(row.label)
            continue
        actual_kind = classify(row)
        if entry.kind != actual_kind:
            entry = Metadata(
                actual_kind,
                entry.implementation_owner,
                entry.declarations,
                entry.module,
                entry.status,
                entry.trust,
            )
        metadata[row.label] = entry
    if unknown:
        raise ValueError(
            "active labels lack reviewed Lean metadata: " + ", ".join(sorted(unknown))
        )
    return metadata


def markdown_code(value: str) -> str:
    return "—" if value == "—" else f"`{value}`"


def canonical_header(tex_name: str, rows: list[LabelRow], appendix_line: int) -> str:
    main_count = sum(row.owner == "main" for row in rows)
    appendix_count = len(rows) - main_count
    return f"""# Canonical manuscript–Lean source map

Authoritative manuscript: `{tex_name}`. The table is generated from active TeX after comments
and literal `\\iffalse` branches are removed. Physical label lines are preserved exactly. The
`\\appendix` boundary is line {appendix_line}. The census is **{len(rows)} unique labels =
{main_count} main + {appendix_count} appendix**.

`proved` means that the named Lean declaration is present in the checked project. A trust entry
names any project axiom inherited by the relevant path; `internal/mathlib` means that no project
axiom is asserted for that row. `partial (theorem-path bound proved)` is used only where the Lean
development proves the bound consumed by the main theorem but does not export the complete
standalone display as one declaration. Documentation-only rows make no formalization claim.
For theorem-like rows, the trust entry is the exact direct `#print axioms` fingerprint, with
`standard` abbreviating `propext`, `Classical.choice`, and `Quot.sound`.

| TeX label | Label line / TeX owner | Kind | Implementation owner | Lean declaration | Module | Status | Trust boundary |
|---|---:|---|---|---|---|---|---|
"""


def map_table(rows: list[LabelRow], metadata: dict[str, Metadata]) -> str:
    output: list[str] = []
    for row in rows:
        entry = metadata[row.label]
        output.append(
            f"| `{row.label}` | {row.line} / {row.owner} | {entry.kind} | "
            f"{entry.implementation_owner} | {markdown_code(entry.declarations)} | "
            f"{markdown_code(entry.module)} | {entry.status} | {entry.trust} |"
        )
    return "\n".join(output) + "\n"


def main_map_text(tex_name: str, rows: list[LabelRow], metadata: dict[str, Metadata]) -> str:
    main_rows = [row for row in rows if row.owner == "main"]
    return f"""# Main-text manuscript–Lean source map

Authoritative manuscript: `{tex_name}`. This is the exact main-text subset of
[`SOURCE_MAP.md`](SOURCE_MAP.md), ending before `\\appendix`. It contains **{len(main_rows)}**
active labels in physical TeX order.

| TeX label | Label line / TeX owner | Kind | Implementation owner | Lean declaration | Module | Status | Trust boundary |
|---|---:|---|---|---|---|---|---|
""" + map_table(main_rows, metadata)


def correspondence_text(tex_name: str, rows: list[LabelRow], metadata: dict[str, Metadata]) -> str:
    theorem_rows = [row for row in rows if classify(row) in THEOREM_KINDS]
    main_rows = [row for row in theorem_rows if row.owner == "main"]
    appendix_rows = [row for row in theorem_rows if row.owner == "appendix"]

    def theorem_table(selected: list[LabelRow]) -> str:
        lines = [
            "| Manuscript statement | Label line | Kind | Lean declaration(s) | Defining module(s) | Coverage | Direct axiom fingerprint |",
            "|---|---:|---|---|---|---|---|",
        ]
        for row in selected:
            entry = metadata[row.label]
            lines.append(
                f"| `{row.label}` | {row.line} | {entry.kind} | "
                f"{markdown_code(entry.declarations)} | {markdown_code(entry.module)} | "
                f"{entry.status} | {entry.trust} |"
            )
        return "\n".join(lines)

    partial = [row.label for row in theorem_rows if metadata[row.label].status.startswith("partial")]
    partial_text = ", ".join(f"`{label}`" for label in partial) if partial else "none"
    return f"""# Manuscript–Lean proposition correspondence

Authoritative manuscript: `{tex_name}`. This report covers every active labelled theorem,
proposition, lemma, and corollary exactly once. The census is **{len(theorem_rows)} statements =
{len(main_rows)} main + {len(appendix_rows)} appendix**. Equation-, figure-, remark-, and
section-level correspondence is recorded separately in [`SOURCE_MAP.md`](SOURCE_MAP.md).

## Principal graph-facing statements

The three principal results are exported in both traditional-graph and scalar forms. Their
equivalence is proved pointwise through the structural realization bridge; the graph-facing
statements therefore do not duplicate the probabilistic or asymptotic arguments.

| Manuscript label | Traditional-graph theorem | Scalar theorem | Contract equivalence |
|---|---|---|---|
| `thm:logarithmic-speeds` | `GraphSemantics.graphLogarithmicSpeeds` | `logarithmicSpeeds` | `GraphSemantics.graphLogarithmicSpeedsStatement_iff` |
| `thm:first-moment-logarithmic-rates` | `GraphSemantics.graphFirstMomentLogarithmicRates` | `firstMomentLogarithmicRates` | `GraphSemantics.graphFirstMomentLogarithmicRatesStatement_iff` |
| `thm:near-critical-speed` | `GraphSemantics.graphResistanceSpeedNearCritical` | `resistanceSpeedNearCritical` | `GraphSemantics.graphResistanceSpeedNearCriticalStatement_iff` |

The deterministic semantic bridge is `SPNetwork.traditionalDistance_realize` for walk distance
and `SPNetwork.traditionalResistance_realize` for Thomson resistance. The graph random variables
are identified with their recursive counterparts by `graphDistanceValue_eq_distanceValue`,
`graphResistanceValue_eq_resistanceValue`, `graphZ_eq_Z`, and `graphX_eq_X`.

## Main-text statements

{theorem_table(main_rows)}

## Appendix statements

{theorem_table(appendix_rows)}

## Coverage boundary

The only theorem-like row marked partial is {partial_text}. For that row, the Lean project proves
the estimate used along the closed main-theorem path, but does not expose the complete displayed
manuscript lemma as a single standalone declaration. In the fingerprint column, `standard` means
exactly `propext`, `Classical.choice`, and `Quot.sound`. The two project axioms that occur are
`distanceGamma_half_eq_zero` (the cited critical distance input) and
`MI01_global_peano_on_compact_interval` (the external compact-interval ODE existence input).
Several analytic declarations take a profile as a theorem parameter and therefore have a
standard direct fingerprint even though a closed profile construction used downstream may invoke
`MI01_global_peano_on_compact_interval`. No row should be read as formalization of surrounding
explanatory prose beyond the labelled mathematical statement.
"""


def lean_declaration_locations(root: Path) -> dict[str, set[Path]]:
    index: dict[str, set[Path]] = {}
    for path in root.rglob("*.lean"):
        for line in path.read_text(encoding="utf-8").splitlines():
            match = DECLARATION_RE.match(line)
            field_match = STRUCTURE_FIELD_RE.match(line)
            if match is None and field_match is None:
                continue
            name = (match or field_match).group(1)
            index.setdefault(name, set()).add(path)
            index.setdefault(name.rsplit(".", 1)[-1], set()).add(path)
    return index


def module_name(lean_root: Path, path: Path) -> str:
    relative = path.relative_to(lean_root)
    parts = list(relative.with_suffix("").parts)
    return ".".join(parts)


def normalize_metadata(
    rows: list[LabelRow], metadata: dict[str, Metadata], lean_root: Path
) -> dict[str, Metadata]:
    """Use defining-file discovery for module columns and normalize trust vocabulary."""
    index = lean_declaration_locations(lean_root)
    normalized: dict[str, Metadata] = {}
    for row in rows:
        entry = metadata[row.label]
        if entry.status == "doc-only":
            normalized[row.label] = Metadata(
                entry.kind, "manuscript", "—", "—", entry.status, "doc-only"
            )
            continue
        modules: list[str] = []
        for declaration in (item.strip() for item in entry.declarations.split(";")):
            leaf = declaration.rsplit(".", 1)[-1]
            locations = index.get(declaration, set()) or index.get(leaf, set())
            for path in sorted(locations):
                module = module_name(lean_root, path)
                if module not in modules:
                    modules.append(module)
        trust = entry.trust.replace(
            "internal / MI01-transitive where profiles are instantiated",
            "internal/mathlib; MI01-transitive after profile instantiation",
        )
        if row.label in ROW_TRUST_OVERRIDES:
            trust = ROW_TRUST_OVERRIDES[row.label]
        if row.label in THEOREM_TRUST:
            trust = THEOREM_TRUST[row.label]
        normalized[row.label] = Metadata(
            entry.kind,
            entry.implementation_owner,
            entry.declarations,
            "; ".join(modules) if modules else entry.module,
            entry.status,
            trust,
        )
    return normalized


def validate_mapped_declarations(
    rows: list[LabelRow], metadata: dict[str, Metadata], lean_root: Path
) -> list[str]:
    index = lean_declaration_locations(lean_root)
    errors: list[str] = []
    for row in rows:
        entry = metadata[row.label]
        if entry.declarations == "—" or entry.status == "doc-only":
            continue
        for declaration in (item.strip() for item in entry.declarations.split(";")):
            leaf = declaration.rsplit(".", 1)[-1]
            if declaration not in index and leaf not in index:
                errors.append(f"{row.label}: Lean declaration not found: {declaration}")
    return errors


def validate_correspondence_declarations(lean_root: Path) -> list[str]:
    index = lean_declaration_locations(lean_root)
    return [
        f"correspondence declaration not found: {declaration}"
        for declaration in sorted(REQUIRED_CORRESPONDENCE_DECLARATIONS)
        if declaration not in index
    ]


def validate_references(text: str, rows: list[LabelRow]) -> list[str]:
    labels = {row.label for row in rows}
    missing: set[str] = set()
    for match in REFERENCE_RE.finditer(text):
        for label in match.group(1).split(","):
            label = label.strip()
            if label and label not in labels:
                missing.add(label)
    return [f"reference target has no active label: {label}" for label in sorted(missing)]


def self_test() -> None:
    sample = r"""\section{A}\label{sec:a}
\begin{lemma}\label{lem:a}True.\end{lemma}
escaped \% not-a-comment \label{eq:a}
% \label{commented}
\iffalse
\label{false-outer}
\iftrue \label{false-inner}\fi
\else
\begin{equation}\label{eq:b}0=0\end{equation}
\fi
\appendix
\section{B}\label{app:b}
"""
    active = active_tex(sample)
    rows, boundary = parse_labels(active)
    assert [(row.label, row.line, row.owner) for row in rows] == [
        ("sec:a", 1, "main"),
        ("lem:a", 2, "main"),
        ("eq:a", 3, "main"),
        ("eq:b", 9, "main"),
        ("app:b", 12, "appendix"),
    ]
    assert boundary == 11


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--tex", type=Path, default=Path("Distance_and_resistance_SPA_revised_blue.tex")
    )
    parser.add_argument("--source-map", type=Path, default=Path("SOURCE_MAP.md"))
    parser.add_argument("--main-source-map", type=Path, default=Path("MAIN_TEXT_SOURCE_MAP.md"))
    parser.add_argument(
        "--correspondence", type=Path, default=Path("MANUSCRIPT_LEAN_CORRESPONDENCE.md")
    )
    parser.add_argument("--lean-root", type=Path, default=Path("SeriesParallel"))
    parser.add_argument("--check", action="store_true", help="verify generated files, do not write")
    args = parser.parse_args()

    try:
        self_test()
        text = active_tex(args.tex.read_text(encoding="utf-8"))
        rows, appendix_line = parse_labels(text)
        previous = parse_existing_metadata(args.source_map)
        metadata = metadata_for(rows, previous)
        metadata = normalize_metadata(rows, metadata, args.lean_root)
    except (AssertionError, OSError, ValueError) as error:
        print(f"ERROR: {error}")
        return 2

    counts = Counter(row.label for row in rows)
    errors = [f"duplicate active label: {label}" for label, count in counts.items() if count != 1]
    errors.extend(validate_environments(rows))
    errors.extend(validate_references(text, rows))
    errors.extend(validate_mapped_declarations(rows, metadata, args.lean_root))
    theorem_labels = {row.label for row in rows if classify(row) in THEOREM_KINDS}
    errors.extend(
        f"theorem-like label lacks an audited axiom fingerprint: {label}"
        for label in sorted(theorem_labels - THEOREM_TRUST.keys())
    )
    errors.extend(validate_correspondence_declarations(args.lean_root))
    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        return 1

    source_text = canonical_header(args.tex.name, rows, appendix_line) + map_table(rows, metadata)
    main_text = main_map_text(args.tex.name, rows, metadata)
    correspondence = correspondence_text(args.tex.name, rows, metadata)
    outputs = {
        args.source_map: source_text,
        args.main_source_map: main_text,
        args.correspondence: correspondence,
    }

    if args.check:
        mismatches = [
            str(path) for path, expected in outputs.items()
            if not path.exists() or path.read_text(encoding="utf-8") != expected
        ]
        if mismatches:
            print("ERROR: generated files are stale: " + ", ".join(mismatches))
            return 1
    else:
        for path, output in outputs.items():
            path.write_text(output, encoding="utf-8", newline="\n")

    main_count = sum(row.owner == "main" for row in rows)
    theorem_count = sum(classify(row) in THEOREM_KINDS for row in rows)
    mode = "verified" if args.check else "generated"
    print(
        f"{mode}: labels={len(rows)} (main={main_count}, appendix={len(rows) - main_count}), "
        f"theorem-like={theorem_count}, appendix-line={appendix_line}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
