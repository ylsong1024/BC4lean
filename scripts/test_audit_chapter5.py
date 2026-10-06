#!/usr/bin/env python3
"""Regression checks for the Chapter 5 completeness inventory."""
from pathlib import Path
import unittest

from audit_chapter5 import REQUIRED_TARGETS, audit_blueprint


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
        ready = statement(REQUIRED_TARGETS[0], r'\lean{Some.theorem}\leanok')
        links, pending, inventory = audit_blueprint(
            self.tex.replace(statement(REQUIRED_TARGETS[0]), ready))
        self.assertEqual(links, ['Some.theorem'])
        self.assertNotIn(REQUIRED_TARGETS[0], pending)
        self.assertEqual(inventory[REQUIRED_TARGETS[0]]['linked_declarations'], links)


if __name__ == '__main__':
    unittest.main()
