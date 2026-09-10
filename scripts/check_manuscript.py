#!/usr/bin/env python3
"""Check the sole manuscript reference, its fingerprint, and report correspondence.

Run from the repository root. Pass --aux after compiling the manuscript to also
check all printed theorem/proposition/lemma numbers in the correspondence report.
Comments and literal false branches are removed without changing source lines.
"""
import argparse
from collections import Counter
import hashlib
from pathlib import Path
import re

MANUSCRIPT = "Series-Parallel_arxiv_submission.tex"
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



def audit(aux_path=None):
    errors = []
    files = sorted(path.name for path in Path('.').glob('*.tex'))
    if files != [MANUSCRIPT]:
        errors.append(f'expected exactly one manuscript: {files}')
    text = Path(MANUSCRIPT).read_text(encoding='utf-8')
    active = active_tex(text)
    labels = [(match[1], active.count('\n', 0, match.start()) + 1)
              for match in re.finditer(r'\\label\{([^{}]+)\}', active)]
    counts = Counter(label for label, _ in labels)
    if len(labels) != 136 or any(n != 1 for n in counts.values()):
        errors.append(f'expected 136 unique active labels, got {len(labels)}')
    appendix = re.search(r'\\appendix\b', active)
    if appendix is None:
        errors.append('missing appendix boundary')
        appendix_line = 0
    else:
        appendix_line = active.count('\n', 0, appendix.start()) + 1
    expected = [(label, line, 'main' if line < appendix_line else 'appendix')
                for label, line in labels]
    source_map = Path('SOURCE_MAP.md').read_text(encoding='utf-8')
    mapped = [(label, int(line), owner.strip()) for label, line, owner in re.findall(
        r'^\|\s*`([^`]+)`\s*\|\s*(\d+)\s*/\s*([^|]+?)\s*\|', source_map, re.M)]
    if mapped != expected:
        errors.append('source-map labels, line numbers, order, or owners differ')
    main_count = sum(owner == 'main' for _, _, owner in expected)
    if main_count != 101 or len(expected) - main_count != 35:
        errors.append('expected 101 main-text labels and 35 appendix labels')
    if f'command is at line {appendix_line}.' not in source_map:
        errors.append('source-map appendix boundary is stale')
    digest = hashlib.sha256(text.encode('utf-8')).hexdigest()
    if f'SHA-256 (UTF-8, LF-normalized): `{digest}`' not in source_map:
        errors.append('source-map fingerprint is stale')
    for report in ['README.md', 'SOURCE_MAP.md', 'FORMALIZATION_REPORT.md',
                   'MANUSCRIPT_LEAN_CORRESPONDENCE.md']:
        if MANUSCRIPT not in Path(report).read_text(encoding='utf-8'):
            errors.append(f'{report} does not identify the sole manuscript')
    for report in Path('.').glob('*.md'):
        refs = re.findall(r'[\w.-]+\.tex\b', report.read_text(encoding='utf-8'))
        if any(ref != MANUSCRIPT for ref in refs):
            errors.append(f'{report} refers to another TeX source: {refs}')
    if re.search(r'\b(?:AI|OpenAI|ChatGPT|Codex|Lean|formalization)\b|proof assistant',
                 text, re.I):
        errors.append('the manuscript contains an excluded declaration term')
    references = re.findall(r'\\(?:ref|eqref|autoref|cref|Cref)\{([^{}]+)\}', active)
    missing = sorted({label.strip() for ref in references for label in ref.split(',')
                      if label.strip() not in counts})
    if missing:
        errors.append(f'undefined TeX references: {missing}')
    if aux_path is not None:
        aux = aux_path.read_text(encoding='utf-8')
        numbers = dict(re.findall(r'\\newlabel\{([^{}]+)\}\{\{([^{}]+)\}', aux))
        printed = []
        for match in re.finditer(
                r'\\begin\{(theorem|proposition|lemma)\}(.*?)\\end\{\1\}', active, re.S):
            label = re.search(r'\\label\{([^{}]+)\}', match[2])
            if label is None or label[1] not in numbers:
                errors.append('a theorem-like environment has no compiled label number')
            else:
                printed.append((match[1].capitalize(), numbers[label[1]]))
        correspondence = Path('MANUSCRIPT_LEAN_CORRESPONDENCE.md').read_text(encoding='utf-8')
        reported = re.findall(r'^\| (Theorem|Proposition|Lemma) ([\dAB.]+)(?: |\s*\|)',
                              correspondence, re.M)
        if len(printed) != 29 or printed != reported:
            errors.append(f'printed correspondence differs: expected={printed}, reported={reported}')
    for error in errors:
        print(f'ERROR: {error}')
    if errors:
        return 1
    print(f'manuscript audit: PASS (136 labels; 101 main, 35 appendix; SHA-256 {digest})')
    if aux_path is not None:
        print('printed correspondence: PASS (29 results; 21 main, 8 appendix)')
    return 0


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--aux', type=Path, help='aux file from a fresh manuscript build')
    args = parser.parse_args()
    try:
        raise SystemExit(audit(args.aux))
    except (OSError, UnicodeError) as error:
        print(f'ERROR: {error}')
        raise SystemExit(2)
