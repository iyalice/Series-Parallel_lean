#!/usr/bin/env python3
"""Audit project axiom declarations and the three main-theorem fingerprints."""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys


MI01 = "SeriesParallel.ManualInterfaces.MI01_global_peano_on_compact_interval"
DISTANCE_INPUT = "SeriesParallel.MainText.distanceGamma_half_eq_zero"
FORBIDDEN_DOCUMENTARY_INPUTS = frozenset(
    {
        "SeriesParallel.MainText.criticalResistanceKnownLimit",
        "SeriesParallel.MainText.distanceGamma_nearCritical",
    }
)
OPTIONAL_DIFFUSION_INPUT = (
    "SeriesParallel.MainText.diffusionCoefficient_eq_two_mul_zetaThree_external"
)

THEOREMS = {
    "SeriesParallel.MainText.logarithmicSpeeds": frozenset({DISTANCE_INPUT}),
    "SeriesParallel.MainText.firstMomentLogarithmicRates": frozenset({DISTANCE_INPUT}),
    "SeriesParallel.MainText.resistanceSpeedNearCritical": frozenset({MI01}),
}

STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
AXIOM_BLOCK_RE = re.compile(
    r"'([^']+)'\s+depends on axioms:\s*\[(.*?)\]", re.DOTALL
)
NO_AXIOM_RE = re.compile(r"'([^']+)'\s+does not depend on any axioms")


def read_declarations(path: Path) -> dict[str, tuple[str, int]]:
    declarations: dict[str, tuple[str, int]] = {}
    for number, raw_line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        fields = raw_line.split("\t")
        if len(fields) != 3:
            raise ValueError(f"{path}:{number}: expected three tab-separated fields")
        name, source, source_line_text = fields
        try:
            source_line = int(source_line_text)
        except ValueError as error:
            raise ValueError(f"{path}:{number}: invalid source line") from error
        if name in declarations:
            raise ValueError(f"{path}:{number}: duplicate axiom name {name}")
        declarations[name] = (source, source_line)
    return declarations


def parse_fingerprints(text: str) -> dict[str, frozenset[str]]:
    result: dict[str, frozenset[str]] = {}
    for match in AXIOM_BLOCK_RE.finditer(text):
        name = match.group(1)
        axioms = frozenset(
            item.strip() for item in match.group(2).split(",") if item.strip()
        )
        if name in result:
            raise ValueError(f"duplicate fingerprint for {name}")
        result[name] = axioms
    for match in NO_AXIOM_RE.finditer(text):
        name = match.group(1)
        if name in result:
            raise ValueError(f"duplicate fingerprint for {name}")
        result[name] = frozenset()
    return result


def self_test() -> None:
    sample = """
'Example.one' depends on axioms: [propext,
 Classical.choice,
 Example.input]
'Example.two' does not depend on any axioms
"""
    parsed = parse_fingerprints(sample)
    assert parsed == {
        "Example.one": frozenset({"propext", "Classical.choice", "Example.input"}),
        "Example.two": frozenset(),
    }


def compare_set(label: str, actual: set[str] | frozenset[str],
    expected: set[str] | frozenset[str], errors: list[str]) -> None:
    missing = sorted(expected - actual)
    unexpected = sorted(actual - expected)
    if missing or unexpected:
        errors.append(f"{label}: missing={missing}, unexpected={unexpected}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--declarations", type=Path, required=True)
    parser.add_argument("--fingerprints", type=Path, required=True)
    parser.add_argument(
        "--allow-ea",
        action="store_true",
        help="permit the explicitly triggered single diffusion closed-form fallback",
    )
    args = parser.parse_args()

    try:
        self_test()
        declarations = read_declarations(args.declarations)
        fingerprints = parse_fingerprints(args.fingerprints.read_text(encoding="utf-8"))
    except (AssertionError, OSError, UnicodeError, ValueError) as error:
        print(f"ERROR: axiom-auditor setup/input failed: {error}", file=sys.stderr)
        return 2

    expected_declarations = {MI01, DISTANCE_INPUT}
    if args.allow_ea:
        expected_declarations.add(OPTIONAL_DIFFUSION_INPUT)
    errors: list[str] = []
    compare_set("axiom declarations", set(declarations), expected_declarations, errors)

    known_project = (
        expected_declarations
        | FORBIDDEN_DOCUMENTARY_INPUTS
        | {OPTIONAL_DIFFUSION_INPUT}
    )
    for theorem, expected_project_base in THEOREMS.items():
        if theorem not in fingerprints:
            errors.append(f"missing fingerprint: {theorem}")
            continue
        axioms = fingerprints[theorem]
        unknown = axioms - STANDARD_AXIOMS - known_project
        if unknown:
            errors.append(f"{theorem}: unknown axioms={sorted(unknown)}")
        project_axioms = axioms & known_project
        expected_project = set(expected_project_base)
        if theorem.endswith("resistanceSpeedNearCritical") and args.allow_ea:
            expected_project.add(OPTIONAL_DIFFUSION_INPUT)
        compare_set(f"{theorem} project fingerprint", project_axioms, expected_project, errors)
        unexpected_standard = (axioms - project_axioms) - STANDARD_AXIOMS
        if unexpected_standard:
            errors.append(
                f"{theorem}: unexpected standard/kernel axioms={sorted(unexpected_standard)}"
            )

    extra_fingerprints = sorted(set(fingerprints) - set(THEOREMS))
    if extra_fingerprints:
        errors.append(f"unexpected fingerprint blocks={extra_fingerprints}")

    documentary_leaks = {
        theorem: sorted(axioms & FORBIDDEN_DOCUMENTARY_INPUTS)
        for theorem, axioms in fingerprints.items()
        if axioms & FORBIDDEN_DOCUMENTARY_INPUTS
    }
    if documentary_leaks:
        errors.append(f"documentary inputs leaked into main theorems={documentary_leaks}")

    if not args.allow_ea and OPTIONAL_DIFFUSION_INPUT in declarations:
        errors.append("(E-a) exists although the explicit fallback trigger was not enabled")

    for theorem in THEOREMS:
        if theorem not in fingerprints:
            continue
        axioms = fingerprints[theorem]
        standard = sorted(axioms & STANDARD_AXIOMS)
        project = sorted(axioms - STANDARD_AXIOMS)
        print(f"{theorem}\tstandard={standard}\tproject={project}")

    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        print("project-axiom audit: FAIL")
        return 1
    print(
        f"project-axiom audit: PASS ({len(declarations)} declarations, "
        f"{len(THEOREMS)} theorem fingerprints)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
