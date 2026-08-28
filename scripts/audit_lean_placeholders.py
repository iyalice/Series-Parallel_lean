#!/usr/bin/env python3
"""Lexically audit Lean sources for forbidden proof escapes and list axioms.

The scanner deliberately ignores nested block comments, line comments, ordinary
and raw strings, and character literals.  It is small rather than a full Lean
parser, but it retains enough namespace/section structure to report fully
qualified names for ordinary ``axiom`` declarations.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import sys


FORBIDDEN = frozenset(
    {
        "admit",
        "implemented_by",
        "opaque",
        "sorry",
        "sorryAx",
        "unsafe",
    }
)


@dataclass(frozen=True)
class Token:
    text: str
    line: int


@dataclass(frozen=True)
class AxiomDeclaration:
    full_name: str
    path: str
    line: int


def _is_ident_start(char: str) -> bool:
    return char == "_" or char.isalpha() or ord(char) >= 128


def _is_ident_rest(char: str) -> bool:
    return _is_ident_start(char) or char.isdigit() or char in ".'"


def _raw_string_opener(text: str, index: int) -> tuple[int, str] | None:
    """Return ``(body_start, terminator)`` for a Lean raw string opener."""
    if text[index] != "r":
        return None
    cursor = index + 1
    while cursor < len(text) and text[cursor] == "#":
        cursor += 1
    if cursor >= len(text) or text[cursor] != '"':
        return None
    hashes = text[index + 1 : cursor]
    return cursor + 1, '"' + hashes


def lean_code_tokens(text: str) -> list[Token]:
    """Tokenize identifiers outside Lean comments and literal forms."""
    tokens: list[Token] = []
    index = 0
    line = 1
    length = len(text)

    while index < length:
        if text.startswith("--", index):
            newline = text.find("\n", index + 2)
            if newline < 0:
                break
            index = newline
            continue

        if text.startswith("/-", index):
            depth = 1
            index += 2
            while index < length and depth:
                if text.startswith("/-", index):
                    depth += 1
                    index += 2
                elif text.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    if text[index] == "\n":
                        line += 1
                    index += 1
            continue

        raw = _raw_string_opener(text, index)
        if raw is not None:
            body_start, terminator = raw
            end = text.find(terminator, body_start)
            if end < 0:
                line += text.count("\n", body_start)
                break
            line += text.count("\n", index, end + len(terminator))
            index = end + len(terminator)
            continue

        if text[index] == '"':
            index += 1
            while index < length:
                if text[index] == "\n":
                    line += 1
                if text[index] == "\\":
                    index += 2
                    continue
                if text[index] == '"':
                    index += 1
                    break
                index += 1
            continue

        if text[index] == "'":
            # Identifier apostrophes (for example ``f'``) were consumed by
            # the identifier branch.  Here, seek the unescaped terminator of
            # a character literal, including forms such as ``'\\u{03bb}'``.
            cursor = index + 1
            escaped = False
            while cursor < length and text[cursor] != "\n":
                if text[cursor] == "'" and not escaped:
                    index = cursor + 1
                    break
                if text[cursor] == "\\" and not escaped:
                    escaped = True
                else:
                    escaped = False
                cursor += 1
            if index == cursor + 1:
                continue

        char = text[index]
        if char == "\n":
            line += 1
            index += 1
            continue
        if _is_ident_start(char):
            start = index
            index += 1
            while index < length and _is_ident_rest(text[index]):
                index += 1
            tokens.append(Token(text[start:index], line))
            continue
        index += 1

    return tokens


def _qualify(namespace: list[str], name: str) -> str:
    if name.startswith("_root_."):
        return name[len("_root_.") :]
    if namespace:
        return ".".join([*namespace, name])
    return name


def declarations_in_tokens(tokens: list[Token], path: str) -> list[AxiomDeclaration]:
    """Collect ordinary axiom declarations with namespace-qualified names."""
    namespace: list[str] = []
    frames: list[int] = []
    declarations: list[AxiomDeclaration] = []
    index = 0
    while index < len(tokens):
        token = tokens[index]
        if token.text == "namespace" and index + 1 < len(tokens):
            frames.append(len(namespace))
            namespace.extend(part for part in tokens[index + 1].text.split(".") if part)
            index += 2
            continue
        if token.text == "section":
            frames.append(len(namespace))
            index += 1
            continue
        if token.text == "end" and frames:
            namespace = namespace[: frames.pop()]
            index += 1
            # An optional name after ``end`` is immaterial to the stack.
            continue
        if token.text == "axiom" and index + 1 < len(tokens):
            name_token = tokens[index + 1]
            declarations.append(
                AxiomDeclaration(
                    _qualify(namespace, name_token.text), path, token.line
                )
            )
        index += 1
    return declarations


def display_path(path: Path, root: Path) -> str:
    resolved = path.resolve()
    try:
        return resolved.relative_to(root).as_posix()
    except ValueError:
        return resolved.as_posix()


def source_files(inputs: list[Path]) -> list[Path]:
    files: set[Path] = set()
    for input_path in inputs:
        if input_path.is_dir():
            files.update(path.resolve() for path in input_path.rglob("*.lean"))
        elif input_path.is_file() and input_path.suffix == ".lean":
            files.add(input_path.resolve())
        else:
            raise FileNotFoundError(f"not a Lean source or directory: {input_path}")
    return sorted(files, key=lambda path: path.as_posix())


def self_test() -> None:
    negative = r'''
-- sorry admit sorryAx unsafe implemented_by opaque axiom Fake.line
/- opaque Fake.outer /- axiom Fake.inner : Prop -/ sorry -/
def ordinary := "sorry axiom Fake.string : Prop"
def escaped := "quote: \" unsafe"
def raw := r###"admit axiom Fake.raw : Prop"###
def character := 'x'
def unicodeCharacter := '\u{03bb}'
def apostrophe' := True
'''
    negative_tokens = lean_code_tokens(negative)
    assert not (FORBIDDEN & {token.text for token in negative_tokens})
    assert not declarations_in_tokens(negative_tokens, "negative.lean")

    positive = """
namespace Fixture.Inner
axiom permitted : Prop
section
axiom localInput : Prop
end
end Fixture.Inner
sorry admit sorryAx unsafe implemented_by opaque
"""
    positive_tokens = lean_code_tokens(positive)
    hits = [token.text for token in positive_tokens if token.text in FORBIDDEN]
    assert hits == ["sorry", "admit", "sorryAx", "unsafe", "implemented_by", "opaque"]
    names = [
        declaration.full_name
        for declaration in declarations_in_tokens(positive_tokens, "positive.lean")
    ]
    assert names == ["Fixture.Inner.permitted", "Fixture.Inner.localInput"]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--axiom-manifest",
        type=Path,
        required=True,
        help="deterministic TSV output for fully qualified axiom declarations",
    )
    parser.add_argument("inputs", nargs="+", type=Path)
    args = parser.parse_args()

    try:
        self_test()
        root = Path.cwd().resolve()
        files = source_files(args.inputs)
    except (AssertionError, OSError) as error:
        print(f"ERROR: lexical-auditor setup failed: {error}", file=sys.stderr)
        return 2

    forbidden_hits: list[tuple[str, int, str]] = []
    declarations: list[AxiomDeclaration] = []
    for path in files:
        shown = display_path(path, root)
        try:
            tokens = lean_code_tokens(path.read_text(encoding="utf-8"))
        except (OSError, UnicodeError) as error:
            print(f"ERROR: cannot read {shown}: {error}", file=sys.stderr)
            return 2
        forbidden_hits.extend(
            (shown, token.line, token.text)
            for token in tokens
            if token.text in FORBIDDEN
        )
        declarations.extend(declarations_in_tokens(tokens, shown))

    declarations.sort(key=lambda item: (item.full_name, item.path, item.line))
    manifest = "".join(
        f"{item.full_name}\t{item.path}\t{item.line}\n" for item in declarations
    )
    try:
        args.axiom_manifest.write_text(manifest, encoding="utf-8", newline="\n")
    except OSError as error:
        print(f"ERROR: cannot write {args.axiom_manifest}: {error}", file=sys.stderr)
        return 2

    for path, line, token in sorted(forbidden_hits):
        print(f"{path}:{line}:{token}")
    if forbidden_hits:
        print(f"placeholder/escape audit: FAIL ({len(forbidden_hits)} code-token hits)")
        return 1
    print(
        f"placeholder/escape audit: PASS ({len(files)} files, "
        f"{len(declarations)} axiom declarations)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
