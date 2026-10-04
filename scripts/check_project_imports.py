#!/usr/bin/env python3
"""Check the project's explicit import list without changing its order.

BC4lean.lean is an aggregator: one `import BC4lean.Module` per line,
with optional blank lines or line comments. Every .lean file under BC4lean/
must appear exactly once. This is a coverage check, not a Lean parser or proof audit.
"""
from collections import Counter
from pathlib import Path
import re
import sys


def check(root: Path) -> list[str]:
    expected = {
        ".".join(path.relative_to(root).with_suffix("").parts)
        for path in (root / "BC4lean").rglob("*.lean")
    }
    errors = []
    if not expected:
        errors.append("No Lean modules found under BC4lean/.")
    imports = []
    for number, line in enumerate((root / "BC4lean.lean").read_text(encoding="utf-8").splitlines(), 1):
        line = line.split("--", 1)[0].strip()
        if not line:
            continue
        match = re.fullmatch(r"import (BC4lean(?:\.[A-Za-z_][A-Za-z0-9_]*)+)", line)
        if not match:
            errors.append(f"BC4lean.lean:{number}: expected one plain project import.")
        else:
            imports.append(match.group(1))
    counts = Counter(imports)
    errors.extend(f"Missing import: {name}" for name in sorted(expected - counts.keys()))
    errors.extend(f"Import has no source file: {name}" for name in sorted(counts.keys() - expected))
    errors.extend(f"Duplicate import: {name}" for name, n in sorted(counts.items()) if n > 1)
    return errors


if __name__ == "__main__":
    project = Path(__file__).resolve().parent.parent
    try:
        problems = check(project)
    except OSError as error:
        print(error, file=sys.stderr)
        sys.exit(1)
    if problems:
        print("\n".join(problems), file=sys.stderr)
        sys.exit(1)
    print("All BC4lean modules are imported exactly once.")
