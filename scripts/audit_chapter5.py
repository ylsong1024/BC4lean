#!/usr/bin/env python3
"""Audit every Chapter 5 module declaration and blueprint link.

Build BC4lean first. This checks Lean declarations/axioms and reports unverified
blueprint targets separately. --require-complete also fails on those targets.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def code_only(s: str) -> str:
    """Remove Lean comments (including nested comments) and string literals."""
    out, i, depth, string = [], 0, 0, False
    while i < len(s):
        if depth:
            if s.startswith('/-', i):
                depth += 1
                i += 2
            elif s.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                i += 1
        elif string:
            if s[i] == '\\':
                i += 2
            elif s[i] == '"':
                string = False
                i += 1
            else:
                i += 1
        elif s.startswith('/-', i):
            depth, i = 1, i + 2
        elif s.startswith('--', i):
            j = s.find('\n', i)
            i = len(s) if j < 0 else j
        elif s[i] == '"':
            string = True
            i += 1
        else:
            out.append(s[i])
            i += 1
    return ''.join(out)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--require-complete', action='store_true')
    parser.add_argument('--output', type=Path, help='Write machine-readable audit evidence.')
    args = parser.parse_args()
    chapter = ROOT / 'blueprint/src/parts/05-equivariant-kk.tex'
    tex = chapter.read_text()
    links = sorted({n.strip() for group in re.findall(r'\\lean\{([^}]+)\}', tex)
                    for n in group.split(',') if n.strip()})
    notready = []
    for block in re.findall(r'\\begin\{(?:definition|proposition|theorem|lemma)\}.*?'
                           r'\\end\{(?:definition|proposition|theorem|lemma)\}', tex, re.S):
        if r'\notready' in block:
            label = re.search(r'\\label\{([^}]+)\}', block)
            notready.append(label.group(1) if label else '<unlabelled>')
    sources = sorted(p for p in (ROOT / 'BC4lean').glob('*.lean')
                     if 'namespace BC4lean.KKTheory' in p.read_text())
    violations = []
    for p in sources:
        tokens = re.findall(r'\b(?:sorry|admit|axiom)\b', code_only(p.read_text()))
        if tokens:
            violations.append((str(p.relative_to(ROOT)), tokens))
    if violations:
        raise RuntimeError(f'Forbidden proof tokens: {violations}')
    modules = [f'BC4lean.{p.stem}' for p in sources]
    module_array = '#[' + ', '.join(json.dumps(m) for m in modules) + ']'
    checks = '\n'.join(f'#check {n}\n#print axioms {n}' for n in links)
    lean = f'''import BC4lean
import Lean
open Lean Elab Command
{checks}
run_cmd do
  let env ← getEnv
  let modules := {module_array}
  let moduleNames := env.header.moduleNames
  let mut count : Nat := 0
  for (n, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let modName := moduleNames[idx]!
      if modules.contains modName.toString then
        let axioms ← collectAxioms n
        for a in axioms do
          unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
            throwError "Unexpected axiom {{a}} in {{n}}"
        let axiomText := String.intercalate "," (axioms.toList.map Name.toString)
        logInfo m!"AUDIT|{{modName.toString}}|{{n.toString}}|{{axiomText}}"
        count := count + 1
  logInfo m!"AUDIT_COUNT|{{count}}"
'''
    with tempfile.TemporaryDirectory(prefix='chapter5-audit-') as temp:
        source = Path(temp) / 'Chapter5Audit.lean'
        source.write_text(lean)
        result = subprocess.run(['lake', 'env', 'lean', '-j2', '-DwarningAsError=true', str(source)],
                                cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                text=True, env=os.environ)
    if result.returncode:
        print(result.stdout)
        return result.returncode
    declarations, axioms = [], set()
    for line in result.stdout.splitlines():
        if line.startswith('AUDIT|'):
            _, module, name, ax = line.split('|', 3)
            declarations.append({'module': module, 'name': name, 'axioms': ax})
            axioms.update(re.findall(r'\b(?:propext|Classical\.choice|Quot\.sound)\b', ax))
    if not declarations:
        raise RuntimeError('No module declarations audited.')
    count = re.search(r'^AUDIT_COUNT\|(\d+)$', result.stdout, re.M)
    if not count or int(count.group(1)) != len(declarations):
        raise RuntimeError('Declaration evidence does not match the Lean audit count.')
    if not axioms.issubset(ALLOWED):
        raise RuntimeError(f'Unexpected reported axioms: {axioms - ALLOWED}')
    module_counts = {m: sum(d['module'] == m for d in declarations) for m in modules}
    if any(n == 0 for n in module_counts.values()):
        raise RuntimeError(f'Unaudited Chapter 5 modules: {module_counts}')
    evidence = {
        'modules': modules, 'linked_declarations': links,
        'module_declaration_counts': module_counts,
        'declaration_count': len(declarations), 'declarations': sorted(declarations, key=lambda d: d['name']),
        'axioms': sorted(axioms), 'forbidden_source_tokens': violations,
        'notready_targets': notready, 'chapter_complete': not notready,
        'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in [*sources, chapter, ROOT / 'BC4lean.lean',
                                    ROOT / 'scripts/audit_chapter5.py']},
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(evidence, indent=2) + '\n')
    print(f'Checked {len(links)} blueprint links and audited {len(declarations)} declarations '
          f'across {len(modules)} Chapter 5 modules.')
    print('Reported axioms: ' + ', '.join(sorted(axioms)))
    print('Unverified targets: ' + (', '.join(notready) if notready else 'none'))
    if args.require_complete and notready:
        print('Full Chapter 5 verification has not been achieved.')
        return 2
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
