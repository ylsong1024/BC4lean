#!/usr/bin/env python3
"""Audit every Chapter 5 declaration, imported prerequisite and blueprint link.

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
REQUIRED_TARGETS = ('def:equivariant-kk', 'prop:kasparov-product', 'prop:kk-k-theory')

# These endpoints were matched to the original three mathematical statements.
# Readiness requires the actual definitions, full product laws and inverse
# comparisons; an unrelated proved declaration cannot certify a target.
REQUIRED_TARGET_DECLARATIONS = {
    "def:equivariant-kk": (
        "BC4lean.KKTheory.BundledGradedKasparovCycle.fullHomotopySetoid",
        "BC4lean.KKTheory.BundledOddKasparovCycle.fullHomotopySetoid",
        "BC4lean.KKTheory.BundledOddKasparovCycle.homotopic_iff_full",
        "BC4lean.KKTheory.CliffordCommutingRepresentation.maximalNorm_eq",
        "BC4lean.KKTheory.FullGradedKasparovHomotopy",
        "BC4lean.KKTheory.GradedKasparovCycle",
        "BC4lean.KKTheory.GradedKasparovHomotopyClass",
        "BC4lean.KKTheory.GroupUniverseCommonParityProduct.universeEquivalence",
        "BC4lean.KKTheory.GroupUniverseParityGroup.KKParityGroup",
        "BC4lean.KKTheory.GroupUniverseParityGroup.evenParityIdentification",
        "BC4lean.KKTheory.GroupUniverseParityGroup.kkParityGroupAddCommGroup",
        "BC4lean.KKTheory.GroupUniverseParityGroup.oddParityIdentification",
        "BC4lean.KKTheory.KasparovCycle",
        "BC4lean.KKTheory.KasparovHomotopyClass.instAddCommGroup",
        "BC4lean.KKTheory.OddKK",
        "BC4lean.KKTheory.OddKK.instAddCommGroup",
        "BC4lean.KKTheory.OddKasparovCycle",
        "BC4lean.KKTheory.cliffordTensorParityAddEquiv",
    ),
    "prop:kasparov-product": (
        "BC4lean.KKTheory.CliffordExternalOddCoefficient.grading_tmul",
        "BC4lean.KKTheory.CliffordExternalOddCoefficient.mul_tmul",
        "BC4lean.KKTheory.CliffordExternalOddCoefficient.starTensor_tmul",
        "BC4lean.KKTheory.CliffordTwoGradedTensor.grading_tensor",
        "BC4lean.KKTheory.CliffordTwoGradedTensor.star_tensor",
        "BC4lean.KKTheory.CliffordTwoGradedTensor.tensor_mul",
        "BC4lean.KKTheory.GradedKasparovConnection",
        "BC4lean.KKTheory.GroupUniverseCommonParityProduct.product",
        "BC4lean.KKTheory.GroupUniverseCommonParityProduct.productAddHom",
        "BC4lean.KKTheory.GroupUniverseCommonParityProduct.product_add_first",
        "BC4lean.KKTheory.GroupUniverseCommonParityProduct.product_add_second",
        "BC4lean.KKTheory.GroupUniverseCommonParityProduct.product_assoc",
        "BC4lean.KKTheory.GroupUniverseExternalOddSemantics.action_tmul",
        "BC4lean.KKTheory.GroupUniverseExternalOddSemantics.grading_tmul",
        "BC4lean.KKTheory.GroupUniverseExternalOddSemantics.inner_tmul",
        "BC4lean.KKTheory.GroupUniverseExternalOddSemantics.moduleEquiv",
        "BC4lean.KKTheory.GroupUniverseExternalOddSemantics.op_smul_tmul",
        "BC4lean.KKTheory.GroupUniverseExternalOddSemantics.operator_tmul",
        "BC4lean.KKTheory.GroupUniverseExternalOddSemantics.representation_tmul",
        "BC4lean.KKTheory.GroupUniverseMatrixMoritaBridge.addEquivalence",
        "BC4lean.KKTheory.GroupUniverseMatrixMoritaBridge.coefficient_roundtrip",
        "BC4lean.KKTheory.GroupUniverseMatrixMoritaBridge.matrix_roundtrip",
        "BC4lean.KKTheory.GroupUniverseMatrixMoritaProduct.toCoefficientClass_eq_product",
        "BC4lean.KKTheory.GroupUniverseMatrixMoritaProduct.toCoefficientClass_product",
        "BC4lean.KKTheory.GroupUniverseMatrixMoritaProduct.toMatrixClass_eq_product",
        "BC4lean.KKTheory.GroupUniverseOddFirstParityProduct.evenOddEvenProduct_assoc",
        "BC4lean.KKTheory.GroupUniverseOddFirstParityProduct.evenOddOddProduct_assoc",
        "BC4lean.KKTheory.GroupUniverseOddFirstParityProduct.oddEvenEvenProduct_assoc",
        "BC4lean.KKTheory.GroupUniverseOddFirstParityProduct.oddEvenOddProduct_assoc",
        "BC4lean.KKTheory.GroupUniverseOddFirstParityProduct.oddEvenProduct",
        "BC4lean.KKTheory.GroupUniverseOddFirstParityProduct.oddOddEvenProduct_assoc",
        "BC4lean.KKTheory.GroupUniverseOddFirstParityProduct.oddOddOddProduct_assoc",
        "BC4lean.KKTheory.GroupUniverseOddFirstParityProduct.oddOddProduct",
        "BC4lean.KKTheory.GroupUniverseOrdinaryEven.coefficientPushforward_shrink",
        "BC4lean.KKTheory.GroupUniverseOrdinaryOdd.coefficientPushforward_mk_coefficientTensor",
        "BC4lean.KKTheory.GroupUniverseParityFunctoriality.coefficientPushforwardHom",
        "BC4lean.KKTheory.GroupUniverseParityFunctoriality.coefficientPushforward_comp",
        "BC4lean.KKTheory.GroupUniverseParityFunctoriality.coefficientPushforward_graded_even",
        "BC4lean.KKTheory.GroupUniverseParityFunctoriality.coefficientPushforward_graded_odd",
        "BC4lean.KKTheory.GroupUniverseParityFunctoriality.coefficientPushforward_id",
        "BC4lean.KKTheory.GroupUniverseParityFunctoriality.coefficientPushforward_product",
        "BC4lean.KKTheory.GroupUniverseParityFunctoriality.coefficientPushforward_product_eq_sourcePullback",
        "BC4lean.KKTheory.GroupUniverseParityFunctoriality.homClass_leftProduct_eq_sourcePullback",
        "BC4lean.KKTheory.GroupUniverseParityFunctoriality.sourcePullbackHom",
        "BC4lean.KKTheory.GroupUniverseParityFunctoriality.sourcePullback_coefficientPushforward",
        "BC4lean.KKTheory.GroupUniverseParityFunctoriality.sourcePullback_comp",
        "BC4lean.KKTheory.GroupUniverseParityFunctoriality.sourcePullback_graded_even",
        "BC4lean.KKTheory.GroupUniverseParityFunctoriality.sourcePullback_graded_odd",
        "BC4lean.KKTheory.GroupUniverseParityFunctoriality.sourcePullback_id",
        "BC4lean.KKTheory.GroupUniverseParityFunctoriality.sourcePullback_product",
        "BC4lean.KKTheory.GroupUniverseParityProduct.evenEvenOddProduct_assoc",
        "BC4lean.KKTheory.GroupUniverseParityProduct.evenOddProduct",
        "BC4lean.KKTheory.GroupUniverseParityProduct.evenProduct",
        "BC4lean.KKTheory.GroupUniverseParityProduct.evenProduct_assoc",
        "BC4lean.KKTheory.GroupUniverseParityUnits.identity",
        "BC4lean.KKTheory.GroupUniverseParityUnits.left_identity",
        "BC4lean.KKTheory.GroupUniverseParityUnits.right_identity",
        "BC4lean.KKTheory.GroupUniverseProduct.bundledProduct_fullHomotopic_first",
        "BC4lean.KKTheory.GroupUniverseProduct.bundledProduct_fullHomotopic_second",
        "BC4lean.KKTheory.GroupUniverseProduct.identity",
        "BC4lean.KKTheory.GroupUniverseProduct.product",
        "BC4lean.KKTheory.GroupUniverseProduct.productOperator",
        "BC4lean.KKTheory.GroupUniverseProduct.productOperator_isProduct",
        "BC4lean.KKTheory.GroupUniverseProduct.product_assoc",
        "BC4lean.KKTheory.GroupUniverseProduct.product_left_identity",
        "BC4lean.KKTheory.GroupUniverseProduct.product_mk_eq_of_isProduct",
        "BC4lean.KKTheory.GroupUniverseProduct.product_right_identity",
        "BC4lean.KKTheory.IsGradedKasparovProductOperator",
        "BC4lean.KKTheory.exists_actualGradedKasparovProductOperator",
        "BC4lean.KKTheory.exists_fullGradedKasparovProductOperatorHomotopy",
        "BC4lean.KKTheory.exists_kasparovDiscreteTechnicalPartition",
        "BC4lean.KKTheory.exists_odd_gradedKasparovConnection",
    ),
    "prop:kk-k-theory": (
        "BC4lean.KKTheory.nonunitalRelativeK0KasparovMapAtUniverse_leftInverse",
        "BC4lean.KKTheory.nonunitalRelativeK0KasparovMapAtUniverse_rightInverse",
        "BC4lean.KKTheory.nonunitalRelativeK0KasparovMapAtZero_natural",
        "BC4lean.KKTheory.oddKKIndependentCoefficientPushforward_comparison_square",
        "BC4lean.KKTheory.oddKKOperatorK1AllModuleUniversesAddEquiv",
        "BC4lean.KKTheory.oddKKOperatorK1AllModuleUniversesAddEquiv_independentCoefficient_natural",
        "BC4lean.KKTheory.oddKKOperatorK1Index_independentCoefficientPushforward_anyModuleUniverse",
        "BC4lean.KKTheory.oddOperatorK1KKInverseAllModuleUniverses_independentCoefficient_natural",
        "BC4lean.KKTheory.oddOperatorK1KKInverseAllModuleUniverses_leftInverse_index",
        "BC4lean.KKTheory.oddOperatorK1KKInverseAllModuleUniverses_rightInverse_index",
        "BC4lean.KKTheory.scalarCliffordOperatorK1AllModuleUniversesAddEquiv",
        "BC4lean.KKTheory.scalarKKOperatorK0AddEquiv",
        "BC4lean.KKTheory.scalarKKOperatorK0AddEquiv_natural",
        "BC4lean.KKTheory.scalarKKOperatorK0IndexHom",
        "BC4lean.KKTheory.scalarKKOperatorK0IndexHom_natural",
        "BC4lean.KKTheory.scalarKKOperatorK0Index_universe",
    ),
}



def tex_code_only(s: str) -> str:
    """Remove TeX comments, preserving escaped percent signs."""
    lines = []
    for line in s.splitlines():
        for i, char in enumerate(line):
            if char != '%':
                continue
            preceding_slashes = len(line[:i]) - len(line[:i].rstrip('\\'))
            if preceding_slashes % 2 == 0:
                line = line[:i]
                break
        lines.append(line)
    return '\n'.join(lines)


def audit_blueprint(tex: str) -> tuple[list[str], list[str], dict[str, dict]]:
    """Require the three main statements even while they remain unverified.

    A missing statement, duplicate target, or ready marker without actual Lean
    links must never make the chapter completeness check succeed.
    """
    tex = tex_code_only(tex)
    links = sorted({n.strip() for group in re.findall(r'\\lean\{([^}]+)\}', tex)
                    for n in group.split(',') if n.strip()})
    blocks = re.findall(r'\\begin\{(definition|proposition|theorem|lemma)\}(.*?)'
                        r'\\end\{\1\}', tex, re.S)
    notready, targets = [], {name: [] for name in REQUIRED_TARGETS}
    for kind, body in blocks:
        labels = re.findall(r'\\label\{([^}]+)\}', body)
        pending = bool(re.search(r'\\notready\b', body))
        block_links = sorted({n.strip() for group in re.findall(r'\\lean\{([^}]+)\}', body)
                              for n in group.split(',') if n.strip()})
        if pending:
            notready.extend(labels or ['<unlabelled>'])
        for label in labels:
            if label in targets:
                targets[label].append({
                    'statement_kind': kind, 'notready': pending,
                    'linked_declarations': block_links,
                    'leanok': bool(re.search(r'\\leanok\b', body)),
                })
    inventory = {}
    for label, matches in targets.items():
        if len(matches) != 1:
            raise ValueError(f'Required Chapter 5 target {label!r} occurs {len(matches)} times.')
        target = matches[0]
        if not target['notready'] and (not target['leanok'] or not target['linked_declarations']):
            raise ValueError(f'Ready Chapter 5 target {label!r} needs Lean links and \\leanok.')
        required = REQUIRED_TARGET_DECLARATIONS[label]
        missing = sorted(set(required) - set(target['linked_declarations']))
        if not target['notready'] and missing:
            raise ValueError(f'Ready Chapter 5 target {label!r} is missing mathematical endpoint links: {missing}')
        target['required_declarations'] = list(required)
        target['missing_required_declarations'] = missing
        inventory[label] = target
    return links, sorted(set(notready)), inventory


def code_only(s: str) -> str:
    """Remove Lean comments (including nested comments) and string literals."""
    out, i, depth, string = [], 0, 0, False
    while i < len(s):
        if depth:
            if s.startswith('/-', i):
                depth += 1
                out.append('  ')
                i += 2
            elif s.startswith('-/', i):
                depth -= 1
                out.append('  ')
                i += 2
            else:
                out.append('\n' if s[i] == '\n' else ' ')
                i += 1
        elif string:
            if s[i] == '\\':
                out.append('  ')
                i += 2
            elif s[i] == '"':
                string = False
                out.append(' ')
                i += 1
            else:
                out.append('\n' if s[i] == '\n' else ' ')
                i += 1
        elif s.startswith('/-', i):
            out.append('  ')
            depth, i = 1, i + 2
        elif s.startswith('--', i):
            j = s.find('\n', i)
            out.append(' ' * ((len(s) if j < 0 else j) - i))
            i = len(s) if j < 0 else j
        elif s[i] == '"':
            string = True
            out.append(' ')
            i += 1
        else:
            out.append(s[i])
            i += 1
    return ''.join(out)


def chapter_source_modules(sources: dict[str, str]) -> list[str]:
    """Include actual project imports regardless of their declaration namespace."""
    codes = {m: code_only(s) for m, s in sources.items()}
    roots = [m for m, s in codes.items()
             if re.search(r'\bnamespace\s+(?:BC4lean\.)?KKTheory\b', s)]
    graph = {m: re.findall(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+'
                          r'(?:all\s+)?BC4lean\.(\S+)', s, re.M)
             for m, s in codes.items()}
    seen, active = set(), set()

    def visit(module: str) -> None:
        if module in active:
            raise ValueError(f'Chapter 5 import cycle at {module}.')
        if module in seen:
            return
        if module not in graph:
            raise ValueError(f'Missing Chapter 5 project prerequisite {module}.')
        active.add(module)
        for dependency in graph[module]:
            visit(dependency)
        active.remove(module)
        seen.add(module)

    for root in roots:
        visit(root)
    return sorted(seen)


def parse_kernel_evidence(output: str, links: list[str], modules: list[str]) -> tuple[list[dict], dict, set, dict]:
    """Require one complete, unique declaration inventory from the actual kernel run."""
    declarations, link_axioms, axioms, names = [], {}, set(), set()
    for line in output.splitlines():
        if line.startswith('LINK_AXIOMS|'):
            _, name, ax = line.split('|', 2)
            if name in link_axioms:
                raise RuntimeError(f'Duplicate blueprint-link axiom evidence: {name}')
            link_axioms[name] = ax
            axioms.update(a.strip() for a in ax.split(',') if a.strip())
        elif line.startswith('AUDIT|'):
            _, module, name, ax = line.split('|', 3)
            if name in names:
                raise RuntimeError(f'Duplicate declaration axiom evidence: {name}')
            if module not in modules:
                raise RuntimeError(f'Unexpected audited module: {module}')
            names.add(name)
            declarations.append({'module': module, 'name': name, 'axioms': ax})
            axioms.update(a.strip() for a in ax.split(',') if a.strip())
    if not declarations:
        raise RuntimeError('No module declarations audited.')
    if sorted(link_axioms) != sorted(links):
        raise RuntimeError('Blueprint-link axiom evidence does not match the link inventory.')
    counts = re.findall(r'^AUDIT_COUNT\|(\d+)$', output, re.M)
    if len(counts) != 1 or int(counts[0]) != len(declarations):
        raise RuntimeError('Declaration evidence does not match a unique Lean audit count.')
    if not axioms.issubset(ALLOWED):
        raise RuntimeError(f'Unexpected reported axioms: {axioms - ALLOWED}')
    module_counts = {m: sum(d['module'] == m for d in declarations) for m in modules}
    if any(n == 0 for n in module_counts.values()):
        raise RuntimeError(f'Unaudited Chapter 5 modules: {module_counts}')
    return declarations, link_axioms, axioms, module_counts


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--require-complete', action='store_true')
    parser.add_argument('--output', type=Path,
                        help='Write audit evidence and retain the kernel source and raw output beside it.')
    args = parser.parse_args()
    chapter = ROOT / 'blueprint/src/parts/05-equivariant-kk.tex'
    tex = chapter.read_text()
    links, notready, target_inventory = audit_blueprint(tex)
    project_sources = {p.stem: p for p in (ROOT / 'BC4lean').glob('*.lean')}
    project_bytes = {m: p.read_bytes() for m, p in project_sources.items()}
    source_modules = chapter_source_modules({m: data.decode()
                                           for m, data in project_bytes.items()})
    sources = [project_sources[m] for m in source_modules]
    input_bytes = {str(p.relative_to(ROOT)): project_bytes[m]
                   for m, p in project_sources.items()}
    for p in [chapter, ROOT / 'BC4lean.lean', ROOT / 'scripts/audit_chapter5.py',
              ROOT / 'scripts/test_audit_chapter5.py',
              ROOT / '.github/workflows/build-project.yml', ROOT / 'lean-toolchain',
              ROOT / 'lakefile.toml', ROOT / 'lake-manifest.json']:
        input_bytes[str(p.relative_to(ROOT))] = p.read_bytes()
    if input_bytes[str(chapter.relative_to(ROOT))].decode() != tex:
        raise RuntimeError('Blueprint changed during source capture.')
    input_hashes = {p: hashlib.sha256(data).hexdigest() for p, data in input_bytes.items()}
    object_paths = [ROOT / '.lake/build/lib/lean/BC4lean' / f'{m}.olean'
                    for m in project_sources]
    object_paths.append(ROOT / '.lake/build/lib/lean/BC4lean.olean')
    if any(not p.is_file() for p in object_paths):
        raise RuntimeError('Build every project module and BC4lean before the Chapter 5 audit.')
    object_hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                     for p in object_paths}
    gate_command = ['lake', '--wfail', '--no-build', '--no-cache', 'build', 'BC4lean']
    gate = subprocess.run(gate_command, cwd=ROOT, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, text=True, env=os.environ)
    if gate.returncode:
        print(gate.stdout)
        raise RuntimeError('Current sources do not have a successful cached strict build.')
    violations = []
    for p in sources:
        tokens = re.findall(r'\b(?:sorry|admit|axiom)\b', code_only(project_bytes[p.stem].decode()))
        if tokens:
            violations.append((str(p.relative_to(ROOT)), tokens))
    if violations:
        raise RuntimeError(f'Forbidden proof tokens: {violations}')
    modules = [f'BC4lean.{p.stem}' for p in sources]
    module_array = '#[' + ', '.join(json.dumps(m) for m in modules) + ']'
    link_array = '#[' + ', '.join(f'``{name}' for name in links) + ']'
    checks = '\n'.join(f'#check {n}\n#print axioms {n}' for n in links)
    lean = f'''import BC4lean
import Lean
open Lean Elab Command
{checks}
run_cmd do
  let env ← getEnv
  let modules := {module_array}
  let links := {link_array}
  for n in links do
    let axioms ← collectAxioms n
    for a in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "Unexpected axiom {{a}} in blueprint link {{n}}"
    let axiomText := String.intercalate "," (axioms.toList.map Name.toString)
    logInfo m!"LINK_AXIOMS|{{n.toString}}|{{axiomText}}"
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
    kernel_evidence = None
    retained = None
    with tempfile.TemporaryDirectory(prefix='chapter5-audit-') as temp:
        source = Path(temp) / 'Chapter5Audit.lean'
        source_bytes = lean.encode('utf-8')
        source.write_bytes(source_bytes)
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            retained = Path(tempfile.mkdtemp(prefix=args.output.name + '.kernel-',
                                             dir=args.output.parent)).resolve()
            (retained / source.name).write_bytes(source_bytes)
        kernel_command = ['lake', 'env', 'lean', '-j2', '-DwarningAsError=true',
                          '-DautoImplicit=false', '-DrelaxedAutoImplicit=false', str(source)]
        result = subprocess.run(kernel_command,
                                cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                env=os.environ)
        if retained is not None:
            raw_output = retained / 'stdout-stderr.log'
            raw_output.write_bytes(result.stdout)
            kernel_evidence = {
                'scope': 'Raw kernel subprocess evidence only; audit gates and chapter readiness '
                         'are reported separately in the successful audit result.',
                'command': kernel_command, 'exit_code': result.returncode,
                'generated_source': {'path': str(retained / source.name),
                                     'sha256': hashlib.sha256(source_bytes).hexdigest()},
                'stdout_stderr': {'path': str(raw_output),
                                  'sha256': hashlib.sha256(result.stdout).hexdigest()},
            }
            run_record = retained / 'kernel-run.json'
            run_record.write_text(json.dumps(kernel_evidence, indent=2) + '\n', encoding='utf-8')
            kernel_evidence['run_record'] = {
                'path': str(run_record), 'sha256': hashlib.sha256(run_record.read_bytes()).hexdigest()}
    # Match text-mode parsing while retaining the original bytes above.
    kernel_output = result.stdout.decode('utf-8').replace('\r\n', '\n').replace('\r', '\n')
    if result.returncode:
        print(kernel_output)
        return result.returncode
    declarations, link_axioms, axioms, module_counts = parse_kernel_evidence(
        kernel_output, links, modules)
    if {p.stem for p in (ROOT / 'BC4lean').glob('*.lean')} != set(project_sources):
        raise RuntimeError('Project source inventory changed during the kernel audit.')
    changed_inputs = [p for p, digest in input_hashes.items()
                      if not (ROOT / p).is_file()
                      or hashlib.sha256((ROOT / p).read_bytes()).hexdigest() != digest]
    changed_objects = [p for p, digest in object_hashes.items()
                       if not (ROOT / p).is_file()
                       or hashlib.sha256((ROOT / p).read_bytes()).hexdigest() != digest]
    if changed_inputs or changed_objects:
        raise RuntimeError(f'Kernel audit inputs changed: sources/controls {changed_inputs}, objects {changed_objects}')
    evidence = {
        'scope': 'Chapter 5 namespace modules and their full project import closure; '
                 'every declaration, including private/generated declarations and '
                 'prerequisites in other namespaces, is audited by module provenance.',
        'modules': modules, 'linked_declarations': links,
        'linked_declaration_axioms': link_axioms,
        'module_declaration_counts': module_counts,
        'declaration_count': len(declarations), 'declarations': sorted(declarations, key=lambda d: d['name']),
        'axioms': sorted(axioms), 'forbidden_source_tokens': violations,
        'notready_targets': notready, 'chapter_complete': not notready,
        'required_target_inventory': target_inventory,
        'source_sha256': input_hashes,
        'project_olean_sha256': object_hashes,
        'source_control_and_object_hashes_unchanged_during_kernel_audit': True,
        'cached_strict_build_gate': {'command': gate_command, 'exit_code': gate.returncode},
    }
    if args.output:
        evidence['kernel_evidence'] = kernel_evidence
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(evidence, indent=2) + '\n')
    print(f'Checked {len(links)} blueprint links and audited {len(declarations)} declarations '
          f'across {len(modules)} Chapter 5 modules and imported prerequisites.')
    print('Reported axioms: ' + ', '.join(sorted(axioms)))
    print('Unverified targets: ' + (', '.join(notready) if notready else 'none'))
    if args.require_complete and notready:
        print('Full Chapter 5 verification has not been achieved.')
        return 2
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
