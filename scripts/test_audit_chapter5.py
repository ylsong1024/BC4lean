#!/usr/bin/env python3
"""Regression checks for the Chapter 5 completeness inventory."""
from pathlib import Path
import unittest

from audit_chapter5 import (REQUIRED_TARGETS, REQUIRED_TARGET_DECLARATIONS,
                           audit_blueprint, chapter_source_modules, parse_kernel_evidence)


def statement(label: str, body: str = r'\notready') -> str:
    return rf'\begin{{proposition}}\label{{{label}}}{body}\end{{proposition}}'


class BlueprintInventoryTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tex = '\n'.join(statement(label) for label in REQUIRED_TARGETS)

    def test_actual_blueprint_has_all_main_targets(self) -> None:
        root = Path(__file__).resolve().parents[1]
        _, _, inventory = audit_blueprint(
            (root / 'blueprint/src/parts/05-equivariant-kk.tex').read_text())
        self.assertEqual(set(inventory), set(REQUIRED_TARGETS))

    def test_pending_targets_are_incomplete(self) -> None:
        _, pending, inventory = audit_blueprint(self.tex)
        self.assertEqual(pending, sorted(REQUIRED_TARGETS))
        self.assertTrue(all(target['notready'] for target in inventory.values()))

    def test_deleted_target_is_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, 'occurs 0 times'):
            audit_blueprint(self.tex.replace(statement(REQUIRED_TARGETS[0]), ''))

    def test_duplicate_target_is_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, 'occurs 2 times'):
            audit_blueprint(self.tex + statement(REQUIRED_TARGETS[0]))

    def test_ready_target_needs_links_and_marker(self) -> None:
        for body in ('', r'\leanok', r'\lean{Some.theorem}', r'\lean{ , }\leanok'):
            with self.subTest(body=body), self.assertRaisesRegex(ValueError, 'needs Lean links'):
                audit_blueprint(self.tex.replace(statement(REQUIRED_TARGETS[0]),
                                                 statement(REQUIRED_TARGETS[0], body)))

    def test_commented_links_do_not_certify_target(self) -> None:
        body = '% \\lean{Some.theorem}\\leanok\n'
        with self.assertRaisesRegex(ValueError, 'needs Lean links'):
            audit_blueprint(self.tex.replace(statement(REQUIRED_TARGETS[0]),
                                             statement(REQUIRED_TARGETS[0], body)))

    def test_ready_target_records_its_own_links(self) -> None:
        required = sorted(REQUIRED_TARGET_DECLARATIONS[REQUIRED_TARGETS[0]])
        ready = statement(REQUIRED_TARGETS[0], r'\lean{' + ','.join(required) + r'}\leanok')
        links, pending, inventory = audit_blueprint(
            self.tex.replace(statement(REQUIRED_TARGETS[0]), ready))
        self.assertEqual(links, required)
        self.assertNotIn(REQUIRED_TARGETS[0], pending)
        self.assertEqual(inventory[REQUIRED_TARGETS[0]]['linked_declarations'], links)

    def test_unrelated_proved_link_does_not_certify_main_target(self) -> None:
        ready = statement(REQUIRED_TARGETS[0], r'\lean{True.intro}\leanok')
        with self.assertRaisesRegex(ValueError, 'missing mathematical endpoint'):
            audit_blueprint(self.tex.replace(statement(REQUIRED_TARGETS[0]), ready))

    def test_omitted_inverse_or_product_law_does_not_certify_target(self) -> None:
        for label in REQUIRED_TARGETS:
            required = REQUIRED_TARGET_DECLARATIONS[label]
            ready = statement(label, r'\lean{' + ','.join(required[:-1]) + r'}\leanok')
            with self.subTest(label=label), self.assertRaisesRegex(ValueError, 'missing mathematical endpoint'):
                audit_blueprint(self.tex.replace(statement(label), ready))


class SourceCoverageTests(unittest.TestCase):
    def test_other_namespace_prerequisites_are_audited(self) -> None:
        sources = {
            'Comparison': 'import BC4lean.Julia\nnamespace BC4lean.KKTheory',
            'Julia': 'import BC4lean.Orthogonal\nnamespace BC4lean.OperatorKTheory',
            'Orthogonal': 'namespace BC4lean.OperatorKTheory',
            'Unrelated': 'namespace Elsewhere',
        }
        self.assertEqual(chapter_source_modules(sources),
                         ['Comparison', 'Julia', 'Orthogonal'])

    def test_comments_and_strings_do_not_add_roots_or_imports(self) -> None:
        sources = {
            'Actual': 'namespace BC4lean\nnamespace KKTheory\n'
                      '-- import BC4lean.Missing\n',
            'Comment': '/- namespace BC4lean.KKTheory -/',
            'String': 'def text := "namespace BC4lean.KKTheory"',
        }
        self.assertEqual(chapter_source_modules(sources), ['Actual'])

    def test_missing_prerequisite_is_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, 'Missing.*Absent'):
            chapter_source_modules({'Root': 'import BC4lean.Absent\n'
                                   'namespace BC4lean.KKTheory'})

    def test_import_cycle_is_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, 'import cycle'):
            chapter_source_modules({
                'Root': 'import BC4lean.Other\nnamespace BC4lean.KKTheory',
                'Other': 'import BC4lean.Root',
            })

    def test_comments_separate_namespace_and_import_tokens(self) -> None:
        self.assertEqual(chapter_source_modules({
            'Root': 'import/- nested /- comment -/ -/BC4lean.Helper\n'
                    'namespace/- comment -/BC4lean.KKTheory',
            'Helper': 'namespace Elsewhere',
        }), ['Helper', 'Root'])

    def test_supported_module_import_modifiers_keep_prerequisites(self) -> None:
        self.assertEqual(chapter_source_modules({
            'Root': 'module\npublic import BC4lean.Public\n'
                    'meta import BC4lean.Meta\npublic meta import BC4lean.Both\n'
                    'import all BC4lean.All\nnamespace BC4lean.KKTheory',
            'Public': '', 'Meta': '', 'Both': '', 'All': '',
        }), ['All', 'Both', 'Meta', 'Public', 'Root'])


class KernelEvidenceTests(unittest.TestCase):
    def setUp(self) -> None:
        self.modules = ['BC4lean.A', 'BC4lean.B']
        self.links = ['BC4lean.A.public']
        self.output = ('LINK_AXIOMS|BC4lean.A.public|propext\n'
                       'AUDIT|BC4lean.A|BC4lean.A.public|propext\n'
                       'AUDIT|BC4lean.B|_private.B.0.helper|Classical.choice,Quot.sound\n'
                       'AUDIT_COUNT|2\n')

    def test_private_and_other_namespace_evidence_is_retained(self) -> None:
        declarations, _, axioms, counts = parse_kernel_evidence(
            self.output, self.links, self.modules)
        self.assertEqual(declarations[1]['name'], '_private.B.0.helper')
        self.assertEqual(axioms, {'propext', 'Classical.choice', 'Quot.sound'})
        self.assertEqual(counts, {'BC4lean.A': 1, 'BC4lean.B': 1})

    def test_duplicate_declaration_is_rejected(self) -> None:
        duplicate = self.output.replace('AUDIT_COUNT|2',
                                        'AUDIT|BC4lean.A|BC4lean.A.public|propext\nAUDIT_COUNT|3')
        with self.assertRaisesRegex(RuntimeError, 'Duplicate declaration'):
            parse_kernel_evidence(duplicate, self.links, self.modules)

    def test_ambiguous_or_wrong_count_is_rejected(self) -> None:
        for output in (self.output + 'AUDIT_COUNT|2\n',
                       self.output.replace('AUDIT_COUNT|2', 'AUDIT_COUNT|1')):
            with self.subTest(output=output), self.assertRaisesRegex(RuntimeError, 'unique Lean audit count'):
                parse_kernel_evidence(output, self.links, self.modules)

    def test_unexpected_axiom_is_rejected(self) -> None:
        with self.assertRaisesRegex(RuntimeError, 'Unexpected reported axioms'):
            parse_kernel_evidence(self.output.replace('propext', 'sorryAx'),
                                  self.links, self.modules)

    def test_missing_module_or_link_is_rejected(self) -> None:
        for output in (self.output.replace('LINK_AXIOMS|BC4lean.A.public|propext\n', ''),
                       self.output.replace('AUDIT|BC4lean.B|_private.B.0.helper|Classical.choice,Quot.sound\n', '')
                       .replace('AUDIT_COUNT|2', 'AUDIT_COUNT|1')):
            with self.subTest(output=output), self.assertRaises(RuntimeError):
                parse_kernel_evidence(output, self.links, self.modules)

    def test_duplicate_blueprint_link_is_rejected(self) -> None:
        with self.assertRaisesRegex(RuntimeError, 'Duplicate blueprint-link'):
            parse_kernel_evidence('LINK_AXIOMS|BC4lean.A.public|propext\n' + self.output,
                                  self.links, self.modules)


if __name__ == '__main__':
    unittest.main()
