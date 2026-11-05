"""Check the project's F90 portability rules beyond GNU's earliest F95 mode.

This is a lexical guard, not a replacement for compilation and source review.
Quoted text and comments are removed before inspecting language constructs.
"""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def code_only(line):
    result, quote, i = [], None, 0
    while i < len(line):
        char = line[i]
        if quote:
            if char == quote:
                if i + 1 < len(line) and line[i + 1] == quote:
                    i += 2
                    continue
                quote = None
            result.append(' ')
        elif char in "\"'":
            quote = char
            result.append(' ')
        elif char == '!':
            break
        else:
            result.append(char.lower())
        i += 1
    return ''.join(result)


def audit(path):
    failures, in_type = [], False
    for number, original in enumerate(path.read_text().splitlines(), 1):
        line = code_only(original)
        if len(original.rstrip()) > 120 and line.strip():
            failures.append((number, 'code line exceeds project limit of 120 columns'))
        if re.match(r'^\s*type\s*(?:::)?\s+[a-z]\w*\s*$', line):
            in_type = True
        if re.match(r'^\s*end\s*type\b', line):
            in_type = False
        if in_type and '::' in line and re.search(r'(?<![<>=/])=(?!=)', line):
            failures.append((number, 'derived component default initialization is later than F90'))
        if in_type and re.search(r'\ballocatable\b', line):
            failures.append((number, 'allocatable derived component is later than F90'))
        patterns = [
            r'=>\s*null\s*\(', r'\b(pure|elemental|forall|associate|abstract|extends|class|enum)\b',
            r'\b(iso_fortran_env|iso_c_binding|move_alloc|newunit|errmsg|iomsg|error\s+stop)\b',
            r'\b(select\s+type|do\s+concurrent|block\s*$|contiguous|volatile|asynchronous)\b',
            r'[\[\]]',
        ]
        if any(re.search(pattern, line) for pattern in patterns):
            failures.append((number, 'possible post-F90 language construct'))
        if any(len(token) > 31 for token in re.findall(r'\b[a-z][a-z0-9_]*\b', line)):
            failures.append((number, 'identifier exceeds F90 limit of 31 characters'))
    return failures


if __name__ == '__main__':
    sources = sorted((ROOT / 'src').glob('*.f90'))
    failures = [(path.name, number, reason) for path in sources for number, reason in audit(path)]
    for filename, number, reason in failures:
        print(f'{filename}:{number}: {reason}')
    if failures:
        raise SystemExit(1)
    print(f'F90 lexical portability audit: PASS ({len(sources)} production files).')
