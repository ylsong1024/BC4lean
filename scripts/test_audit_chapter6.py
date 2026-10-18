#!/usr/bin/env python3
"""Regression checks for Chapter 6 audit coverage and readiness safeguards."""
from __future__ import annotations

import json
import hashlib
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import audit_chapter6
from audit_chapter6 import (ROOT, TARGETS, audit_blueprint, check_proof_tokens, code_only,
                           generate_query, load_inventory, parse_kernel_evidence,
                           pending_blueprint_targets, run_expected_types)
from check_project_imports import check_chapter5_core_evidence


def statement(label: str, body: str = r"\notready") -> str:
    return rf"\begin{{proposition}}\label{{{label}}}{body}\end{{proposition}}"


class InventoryTests(unittest.TestCase):
    def test_scope_and_nonempty_endpoint_inventory_are_mandatory(self) -> None:
        valid = {"schema_version": 1, "modules": ["BC4lean.A"],
                 "targets": {label: {"required_declarations": ["BC4lean.RealEndpoint"]}
                             for label in TARGETS}}
        broken = []
        for change in ("missing_target", "empty_endpoint", "duplicate_module", "nonexact_name"):
            data = json.loads(json.dumps(valid))
            if change == "missing_target":
                del data["targets"][TARGETS[0]]
            elif change == "empty_endpoint":
                data["targets"][TARGETS[0]]["required_declarations"] = []
            elif change == "duplicate_module":
                data["modules"] *= 2
            else:
                data["targets"][TARGETS[0]]["required_declarations"] = ["SomeAlias"]
            broken.append(data)
        for data in broken:
            with self.subTest(data=data), self.assertRaises(ValueError):
                load_inventory(Path("unused"), json.dumps(data).encode())


class BlueprintTests(unittest.TestCase):
    def setUp(self) -> None:
        self.inventory = {"targets": {label: {"required_declarations": [f"BC4lean.Endpoint{i}"]}
                                      for i, label in enumerate(TARGETS)}}
        self.tex = "\n".join(statement(label) for label in TARGETS)

    def test_pending_is_not_complete(self) -> None:
        _, targets = audit_blueprint(self.tex, self.inventory)
        self.assertTrue(all(not target["ready"] for target in targets.values()))

    def test_deleted_or_duplicate_target_is_rejected(self) -> None:
        for text in (self.tex.replace(statement(TARGETS[0]), ""),
                     self.tex + statement(TARGETS[0]), self.tex + rf"\label{{{TARGETS[0]}}}"):
            with self.subTest(text=text), self.assertRaisesRegex(ValueError, "occurs"):
                audit_blueprint(text, self.inventory)

    def test_marker_or_unrelated_theorem_cannot_certify_target(self) -> None:
        for body in (r"\leanok", r"\lean{BC4lean.Unrelated}\leanok",
                     "% \\lean{BC4lean.Endpoint0}\\leanok\n"):
            with self.subTest(body=body), self.assertRaisesRegex(ValueError, "mathematical endpoint"):
                audit_blueprint(self.tex.replace(statement(TARGETS[0]),
                                                 statement(TARGETS[0], body)), self.inventory)

    def test_endpoint_link_and_marker_are_both_required(self) -> None:
        ready = statement(TARGETS[0], r"\lean{BC4lean.Endpoint0}\leanok")
        links, targets = audit_blueprint(self.tex.replace(statement(TARGETS[0]), ready), self.inventory)
        self.assertEqual(links, ["BC4lean.Endpoint0"])
        self.assertTrue(targets[TARGETS[0]]["ready"])
        self.assertFalse(targets[TARGETS[1]]["ready"])

    def test_contradictory_markers_are_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, "contradictory"):
            audit_blueprint(self.tex.replace(r"\notready", r"\notready\leanok", 1), self.inventory)

    def test_empty_support_link_is_rejected_and_pending_support_is_recorded(self) -> None:
        with self.assertRaisesRegex(ValueError, "Empty exact"):
            audit_blueprint(self.tex + r"\lean{}", self.inventory)
        pending = pending_blueprint_targets(self.tex + statement("lemma:support"))
        self.assertIn("lemma:support", pending)


class CoverageTests(unittest.TestCase):
    def setUp(self) -> None:
        self.modules, self.links = ["BC4lean.A", "BC4lean.B"], ["BC4lean.A.public"]
        self.output = ("CH6_START|1\n"
                       "CH6_DECL|BC4lean.A|BC4lean.A.public|propext\n"
                       "CH6_DECL|BC4lean.B|_private.B.0.helper|Classical.choice,Quot.sound\n"
                       "CH6_LINK|BC4lean.A.public|BC4lean.A|propext\n"
                       "CH6_MODULE|BC4lean.A|1\nCH6_MODULE|BC4lean.B|1\nCH6_END|2|1\n")

    def test_private_and_generated_names_are_retained_by_origin(self) -> None:
        report = parse_kernel_evidence(self.output, self.modules, self.links)
        self.assertEqual(report["declaration_count"], 2)
        self.assertIn("_private.B.0.helper", [d["name"] for d in report["declarations"]])

    def test_duplicate_and_incomplete_evidence_is_rejected(self) -> None:
        broken = [self.output + "CH6_END|2|1\n", self.output.replace("CH6_END|2|1", "CH6_END|1|1"),
                  self.output.replace("CH6_MODULE|BC4lean.B|1\n", ""),
                  self.output.replace("CH6_LINK|BC4lean.A.public|BC4lean.A|propext\n", ""),
                  self.output.replace("CH6_MODULE|BC4lean.B|1", "CH6_MODULE|BC4lean.B|2"),
                  self.output.replace("CH6_START|1", "CH6_START|1\nCH6_START|1")]
        for output in broken:
            with self.subTest(output=output), self.assertRaises(RuntimeError):
                parse_kernel_evidence(output, self.modules, self.links)

    def test_sorry_axiom_and_unexpected_origins_are_rejected(self) -> None:
        for output in (self.output.replace("propext", "sorryAx"),
                       self.output.replace("CH6_DECL|BC4lean.B", "CH6_DECL|BC4lean.Omitted"),
                       self.output.replace("CH6_LINK|BC4lean.A.public|BC4lean.A",
                                           "CH6_LINK|BC4lean.A.public|BC4lean.Wrong")):
            with self.subTest(output=output), self.assertRaises(RuntimeError):
                parse_kernel_evidence(output, self.modules, self.links)

    def test_query_uses_all_imports_and_module_origins(self) -> None:
        query = generate_query(self.modules, self.links, ["BC4lean.A.public"])
        self.assertIn("import all BC4lean.B", query)
        self.assertIn("env.getModuleIdxFor? name", query)
        self.assertIn("collectAxioms name", query)
        self.assertNotIn("import BC4lean\n", query)

    def test_source_tokens_in_comments_and_strings_do_not_count(self) -> None:
        source = '/- sorry /- axiom -/ admit -/\ndef s := "sorry\\\"admit"\n-- axiom\n'
        self.assertNotIn("sorry", code_only(source))
        self.assertIn("axiom", code_only("axiom bad : False"))


class ExpectedTypeTests(unittest.TestCase):
    def test_strict_fixture_check_retains_actual_exit_log_and_source_hash(self) -> None:
        for exit_code in (0, 7):
            with self.subTest(exit_code=exit_code), tempfile.TemporaryDirectory() as directory:
                fixture, output = Path(directory) / "ExpectedTypes.lean", Path(directory) / "audit.json"
                fixture.write_text("example : True := True.intro\n")
                source_hash = hashlib.sha256(fixture.read_bytes()).hexdigest()
                stdout = b"retained expected-type check output\n"
                with patch("audit_chapter6.subprocess.run", return_value=SimpleNamespace(
                        returncode=exit_code, stdout=stdout)) as run:
                    if exit_code:
                        with self.assertRaisesRegex(RuntimeError, "Expected-type check failed"):
                            run_expected_types(fixture, output, source_hash)
                    else:
                        run_expected_types(fixture, output, source_hash)
                command = ["lake", "env", "lean", "-j1", "-DwarningAsError=true",
                           "-DautoImplicit=false", "-DrelaxedAutoImplicit=false", str(fixture)]
                self.assertEqual(run.call_args.args[0], command)
                record = json.loads(output.with_suffix(".expected-types-run.json").read_text())
                self.assertEqual(record["command"], command)
                self.assertEqual(record["exit_code"], exit_code)
                self.assertEqual(record["source_sha256"], source_hash)
                self.assertEqual(record["stdout_stderr_sha256"], hashlib.sha256(stdout).hexdigest())
                self.assertEqual(output.with_suffix(".expected-types.log").read_bytes(), stdout)

    def test_fixture_rejects_assumed_axioms_and_proof_holes(self) -> None:
        for token in ("axiom", "sorry", "admit", "sorryAx"):
            with self.subTest(token=token), self.assertRaisesRegex(RuntimeError, "Expected-type fixture"):
                check_proof_tokens(f"example : False := {token}\n", "Expected-type fixture")
        check_proof_tokens('/- axiom sorry -/\ndef text := "admit sorryAx"\n', "Expected-type fixture")

    def test_generate_only_captures_fixture_without_running_lean(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "audit.json"
            def git_only(command, **_kwargs):
                self.assertEqual(command[0], "git")
                return SimpleNamespace(returncode=0, stdout="fixture-revision\n")
            with patch("sys.argv", ["audit_chapter6.py", "--generate-only", "--output", str(output)]), \
                    patch("audit_chapter6.subprocess.run", side_effect=git_only), \
                    patch("audit_chapter6.run_expected_types") as check, patch("builtins.print"):
                self.assertEqual(audit_chapter6.main(), 0)
            check.assert_not_called()
            evidence = json.loads(output.read_text())
            fixture = "docs/audits/chapter6/ExpectedTypes.lean"
            self.assertEqual(evidence["source_sha256"][fixture],
                             hashlib.sha256((ROOT / fixture).read_bytes()).hexdigest())
            self.assertEqual(evidence["status"], "generated_only")
            self.assertFalse(evidence["chapter_complete"])

    def test_fixture_failure_cannot_publish_completed_audit(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "audit.json"
            original_digest = audit_chapter6.digest
            def digest(path):
                return "0" * 64 if str(path).endswith((".olean", ".olean.private")) else original_digest(path)
            def external(command, **_kwargs):
                if command[0] == "git":
                    return SimpleNamespace(returncode=0, stdout="fixture-revision\n")
                if command[:2] == ["lake", "--wfail"]:
                    return SimpleNamespace(returncode=0, stdout=b"strict build current\n")
                self.assertEqual(Path(command[-1]), ROOT / "docs/audits/chapter6/ExpectedTypes.lean")
                return SimpleNamespace(returncode=9, stdout=b"independent expected type mismatch\n")
            with patch("sys.argv", ["audit_chapter6.py", "--output", str(output)]), \
                    patch("audit_chapter6.subprocess.run", side_effect=external), \
                    patch("audit_chapter6.digest", side_effect=digest):
                with self.assertRaisesRegex(RuntimeError, "Expected-type check failed"):
                    audit_chapter6.main()
            evidence = json.loads(output.read_text())
            self.assertEqual(evidence["status"], "generated_only")
            self.assertFalse(evidence["chapter_complete"])
            record = json.loads(output.with_suffix(".expected-types-run.json").read_text())
            self.assertEqual(record["exit_code"], 9)
            self.assertFalse(output.with_suffix(".kernel-run.json").exists())


class HistoricalImportAppendTests(unittest.TestCase):
    """Exercise the append branch, holding unrelated historical hashes fixed.

The retained checker owns validation of the historical snapshot. These tests
substitute known historical source/hash pairs so its new prefix branch can be
tested without repeatedly reading 817 unrelated files. Aggregate and archive
bytes use real SHA-256 throughout. No repository file is written.
"""

    file_bytes: dict[Path, bytes] = {}

    def setUp(self) -> None:
        self.original = (ROOT / "docs/audits/chapter6/Chapter5Imports.lean").read_bytes()
        self.aggregate = self.original + b"import BC4lean.NewChapter6\n"
        evidence = json.loads((ROOT / "docs/audits/chapter5/core-evidence.json").read_text())
        self.fixed_hashes = {b"\x00historical-source-fixture:" + path.encode(): sha
                             for path, sha in evidence["source_sha256"].items()
                             if path != "BC4lean.lean"}

    def errors(self, aggregate: bytes | None = None, archive: bytes | None = None,
               coverage: list[str] | None = None) -> list[str]:
        original_read = Path.read_bytes
        original_sha256 = hashlib.sha256
        overrides = {ROOT / "BC4lean.lean": self.aggregate if aggregate is None else aggregate,
                     ROOT / "docs/audits/chapter6/Chapter5Imports.lean":
                     self.original if archive is None else archive}

        def read(path: Path) -> bytes:
            if path in overrides:
                return overrides[path]
            marker = b"\x00historical-source-fixture:" + str(path.relative_to(ROOT)).encode()
            if marker in self.fixed_hashes:
                return marker
            if path not in self.file_bytes:
                self.file_bytes[path] = original_read(path)
            return self.file_bytes[path]

        def sha256(data: bytes = b"", *args, **kwargs):
            if data in self.fixed_hashes:
                return SimpleNamespace(hexdigest=lambda: self.fixed_hashes[data])
            return original_sha256(data, *args, **kwargs)

        with patch.object(Path, "read_bytes", read), patch("check_project_imports.check",
                return_value=[] if coverage is None else coverage), \
                patch("check_project_imports.hashlib.sha256", sha256):
            return check_chapter5_core_evidence(ROOT)

    def test_only_new_import_append_preserves_historical_evidence(self) -> None:
        self.assertEqual(self.errors(), [])

    def test_changed_historical_prefix_is_rejected(self) -> None:
        self.assertIn("unchanged prefix", " ".join(self.errors(b"-- changed prefix\n" + self.aggregate)))

    def test_repeated_historical_import_is_rejected(self) -> None:
        historical_import = next(line for line in self.original.splitlines() if line.startswith(b"import "))
        self.assertIn("repeats an audited module", " ".join(self.errors(self.aggregate + historical_import + b"\n")))

    def test_wrong_archived_prefix_hash_is_rejected(self) -> None:
        self.assertIn("wrong hash", " ".join(self.errors(archive=self.original + b"\n")))

    def test_append_still_requires_global_import_coverage(self) -> None:
        self.assertIn("complete module coverage", " ".join(self.errors(coverage=["Missing import"])))


if __name__ == "__main__":
    unittest.main()
