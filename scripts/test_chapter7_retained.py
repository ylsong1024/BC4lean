#!/usr/bin/env python3
"""Portable read-only retained-proof/provider safeguards; never run Lean/Lake."""
import json
import os
from pathlib import Path
import sys
import types
import unittest

import check_chapter7_retained as retained

ROOT = Path(os.environ.get('BC4LEAN_TEST_ROOT', Path(__file__).resolve().parents[1])).resolve()


class ProductionProviderTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest = retained.load_manifest(retained.MANIFEST_PATH.read_bytes())
        cls.reader = retained.RepositoryReader(ROOT)
        cls.sources = retained.verified_helper_sources(cls.reader, cls.manifest)

    def test_manifest_is_fixed_930_source_145_input_21_artifact_snapshot(self):
        self.assertEqual(len(self.manifest['proof_sources']),930)
        self.assertEqual(len(self.manifest['original_inputs']),145)
        self.assertEqual(len(self.manifest['canonical_artifacts']),21)

    def test_actual_registered_source_baseline_is_preserved_without_new_native_claim(self):
        path=ROOT/'docs/audits/chapter8/inventory.json'
        modules=json.loads(path.read_bytes())['modules'] if path.exists() else []
        value=retained.validate(retained.RepositoryReader(ROOT),self.manifest,modules)
        self.assertEqual(value.receipt['proof_sources_preserved'],930)
        self.assertFalse(value.receipt['chapter8_complete'])
        self.assertFalse(value.receipt['new_native_chapter7_census_performed'])

    def test_forged_public_digest_marker_does_not_establish_module_provenance(self):
        name='check_chapter7_website';fake=types.ModuleType(name)
        fake._retained_verified_source_sha256=self.manifest['trusted_pure_helpers']['scripts/check_chapter7_website.py']
        sys.modules[name]=fake
        try:
            with self.assertRaisesRegex(ValueError,'Preexisting/unverified'):
                with self.sources.open():pass
            self.assertIs(sys.modules[name],fake)
        finally:sys.modules.pop(name,None)

    def test_context_module_identity_code_and_cleanup_are_checked(self):
        with self.assertRaisesRegex(ValueError,'mutated'):
            with self.sources.open() as helpers:
                helpers['check_chapter7_website'].validate_general_conjecture_scope=lambda *_:{}
        self.assertTrue(all(name not in sys.modules for name,_ in retained.HELPERS))
        with self.sources.open() as helpers:
            self.assertTrue(callable(helpers['check_chapter7_website'].validate_general_conjecture_scope))

    def test_complete_canonical_pending_graph_accepts_only_unfilled_orange_node(self):
        retained.verify_pending_graph('.renderDot(`digraph { node [label="\\N",penwidth=1.8]; "conj:baum-connes" [color="#ffaa33",shape=ellipse,label="Conjecture"]; }`)')

    def test_all_fills_and_inherited_styles_reject(self):
        node='"conj:baum-connes" [color="#FFAA33",shape=ellipse,label="Conjecture"];'
        for value in ['#1cac78','green','lime','white']:
            with self.subTest(value=value),self.assertRaises(ValueError):
                retained.verify_pending_graph('.renderDot(`digraph { '+node.replace('shape=ellipse','fillcolor="'+value+'",shape=ellipse')+' }`)')
        with self.assertRaises(ValueError):
            retained.verify_pending_graph('.renderDot(`digraph { node [style=filled][fillcolor=green];'+node+' }`)')

    def test_duplicate_node_and_unconsumed_dot_reject(self):
        node='"conj:baum-connes" [color="#FFAA33",shape=ellipse,label="Conjecture"];'
        for extra in [node,'"conj:baum-connes" [style=filled][fillcolor=green];','<unsupported>']:
            with self.subTest(extra=extra),self.assertRaises(ValueError):
                retained.verify_pending_graph('.renderDot(`digraph { '+node+extra+' }`)')

    def test_javascript_quote_injection_interpolation_and_nonliteral_arguments_reject(self):
        attacks=[r'.renderDot(`digraph { "conj:baum-connes" [color="#FFAA33",shape=ellipse,label="Conjecture\x22,fillcolor=green,style=filled,tooltip=\x22Conjecture"]; }`)',
                 r'.renderDot(`digraph { "conj:baum-connes" [color="#FFAA33",shape=ellipse,label="${malicious}"]; }`)',
                 '.renderDot(variable)']
        for value in attacks:
            with self.subTest(value=value),self.assertRaises(ValueError):retained.verify_pending_graph(value)

    def test_original_105_scope_rule_remains_strict(self):
        with self.sources.open() as helpers:
            a=helpers['audit_chapter7'];prefix=b'import BC4lean.Old\n';digest=retained.digest(prefix)
            with self.assertRaises(RuntimeError):
                a.check_scope_coverage(prefix+b'import BC4lean.New\nimport BC4lean.Unregistered\n',prefix,['BC4lean.New'],digest)


if __name__=='__main__':unittest.main(verbosity=2)
