#!/usr/bin/env python3
"""Audit active TeX labels, source lines, and Markdown source-map ownership.

An unescaped percent sign starts a TeX comment.  A percent sign is escaped exactly when the
immediately preceding run of backslashes has odd length.  Literal ``\\iffalse`` branches are
removed (with nested conditionals and an optional active ``\\else`` branch) while preserving
line numbers.
"""

from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path
import re
import sys


EXPECTED_TOTAL = 156
EXPECTED_MAIN = 112
EXPECTED_APPENDIX = 44
APPENDIX_BOUNDARY = "app:ode"
MOVED_LABELS = {
    "prop:full-line-distribution",
    "eq:Phi-phase-definition",
    "eq:upper-profile-equation",
    "eq:full-line-relative-bounds",
    "eq:full-line-tail-ratios",
    "prop:hard-edge-distribution",
    "eq:Psi-subcritical-definition",
    "eq:lower-profile-equation",
    "eq:subcritical-relative-bounds",
    "eq:q-extension-bounds",
    "eq:subcritical-right-tail",
}
LABEL_RE = re.compile(r"\\label\{([^{}]+)\}")
TABLE_ROW_RE = re.compile(
    r"^\|\s*`([^`]+)`\s*\|\s*(\d+)\s*/\s*([^|]+?)\s*\|", re.MULTILINE
)
CONDITIONAL_RE = re.compile(r"\\(iffalse|if[a-zA-Z@]+|else|fi)\b")


def strip_tex_comments(text: str) -> str:
    """Remove TeX comments while retaining line boundaries."""
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
                scan = len(text)
                break
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


def table_rows(path: Path) -> list[tuple[str, int, str]]:
    return [
        (label, int(line), owner.strip())
        for label, line, owner in TABLE_ROW_RE.findall(path.read_text(encoding="utf-8"))
    ]


def label_rows(text: str) -> list[tuple[str, int]]:
    return [
        (match.group(1), text.count("\n", 0, match.start()) + 1)
        for match in LABEL_RE.finditer(text)
    ]


def self_test() -> None:
    sample = r"""\label{visible-a}
escaped \% not-a-comment \label{visible-b}
% \label{commented}
\iffalse
\label{false-outer}
\iftrue \label{false-inner}\fi
\else
\label{visible-c}
\fi
"""
    rows = label_rows(active_tex(sample))
    assert rows == [("visible-a", 1), ("visible-b", 2), ("visible-c", 8)]


def describe_difference(expected: set[str], actual: set[str]) -> tuple[list[str], list[str]]:
    return sorted(expected - actual), sorted(actual - expected)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tex", type=Path, default=Path("Series-Parallel_SPA_submission.tex"))
    parser.add_argument("--source-map", type=Path, default=Path("SOURCE_MAP.md"))
    parser.add_argument("--main-source-map", type=Path)
    args = parser.parse_args()

    try:
        self_test()
    except AssertionError:
        print("ERROR: internal TeX lexical fixtures failed")
        return 2

    active_text = active_tex(args.tex.read_text(encoding="utf-8"))
    rows = label_rows(active_text)
    labels = [label for label, _line in rows]
    line_of = dict(rows)
    counts = Counter(labels)
    duplicates = sorted(label for label, count in counts.items() if count != 1)
    try:
        boundary_index = labels.index(APPENDIX_BOUNDARY)
    except ValueError:
        print(f"ERROR: missing appendix boundary {APPENDIX_BOUNDARY}")
        return 1

    main_labels = labels[:boundary_index]
    appendix_labels = labels[boundary_index:]
    main_set = set(main_labels)
    appendix_set = set(appendix_labels)
    active_set = set(labels)

    errors: list[str] = []
    if len(labels) != EXPECTED_TOTAL or len(active_set) != EXPECTED_TOTAL:
        errors.append(f"total={len(labels)}, unique={len(active_set)}, expected={EXPECTED_TOTAL}")
    if len(main_labels) != EXPECTED_MAIN:
        errors.append(f"main={len(main_labels)}, expected={EXPECTED_MAIN}")
    if len(appendix_labels) != EXPECTED_APPENDIX:
        errors.append(f"appendix={len(appendix_labels)}, expected={EXPECTED_APPENDIX}")
    if duplicates:
        errors.append(f"duplicate={duplicates}")
    wrong_moved = sorted(MOVED_LABELS - main_set)
    moved_in_appendix = sorted(MOVED_LABELS & appendix_set)
    if wrong_moved or moved_in_appendix:
        errors.append(
            f"moved ownership: missing-from-main={wrong_moved}, present-in-appendix={moved_in_appendix}"
        )

    map_specs = [(args.source_map, active_set)]
    if args.main_source_map is not None:
        map_specs.append((args.main_source_map, main_set))
    for map_path, expected in map_specs:
        if not map_path.exists():
            errors.append(f"missing source map: {map_path}")
            continue
        mapped_rows = table_rows(map_path)
        mapped = [label for label, _line, _owner in mapped_rows]
        mapped_counts = Counter(mapped)
        mapped_duplicates = sorted(label for label, count in mapped_counts.items() if count != 1)
        missing, extra = describe_difference(expected, set(mapped))
        wrong_lines = sorted(
            (label, mapped_line, line_of.get(label))
            for label, mapped_line, _owner in mapped_rows
            if line_of.get(label) != mapped_line
        )
        expected_order = [label for label in labels if label in expected]
        order_matches = mapped == expected_order
        if missing or extra or mapped_duplicates or wrong_lines or not order_matches:
            errors.append(
                f"{map_path}: rows={len(mapped)}, missing={missing}, extra={extra}, "
                f"duplicate={mapped_duplicates}, wrong-lines={wrong_lines}, "
                f"source-order={order_matches}"
            )

    if args.source_map.exists():
        canonical_rows = table_rows(args.source_map)
        wrong_owners = sorted(
            (label, owner, "main" if label in main_set else "appendix")
            for label, _line, owner in canonical_rows
            if (label in main_set and owner != "main")
            or (label in appendix_set and not owner.startswith("appendix"))
        )
        if wrong_owners:
            errors.append(f"{args.source_map}: wrong TeX owners={wrong_owners}")

    print(
        f"active labels: total={len(labels)}, unique={len(active_set)}, "
        f"main={len(main_labels)}, appendix={len(appendix_labels)}, "
        f"source-lines={rows[0][1]}..{rows[-1][1]}"
    )
    print(f"moved labels owned by main: {len(MOVED_LABELS & main_set)} / {len(MOVED_LABELS)}")
    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        return 1
    print("label/source-map audit: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
