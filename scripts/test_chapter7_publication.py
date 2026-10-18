#!/usr/bin/env python3
"""Publication safeguards using temporary files and synthetic process evidence.

These tests do not execute Lean, Git, or mutate a retained historical record.
They exercise rejected claims, raw evidence integrity, exact source locations,
and preservation of the existing finder blocks.
"""
from __future__ import annotations

from contextlib import contextmanager
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import audit_chapter7 as audit
import test_audit_chapter7 as audit_tests
import update_chapter7_finder as finder

REVISION = "a" * 40


class FinderTests(unittest.TestCase):
    @contextmanager
    def project(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            fixture = audit_tests.ProcessAndPublicationTests()
            fixture.make_project(root)
            (root / "BC4lean/A.lean").write_text(
                "namespace BC4lean.A\n"
                "private theorem helper : True := True.intro\n"
                "theorem endpoint : True := True.intro\n"
                "end BC4lean.A\n")
            fixture.run_main(root)
            output = root / "result/audit.json"
            report = json.loads(output.read_text())
            report["source_revision"] = REVISION
            output.write_text(json.dumps(report))
            with patch.object(finder, "ROOT", root), patch.object(finder, "AUDIT", output), \
                    patch.object(finder, "INVENTORY", root / "docs/audits/chapter7/inventory.json"), \
                    patch.object(finder, "BLUEPRINT", root / "blueprint/src/parts/07-assembly-map.tex"):
                yield root, output, report

    def save(self, output: Path, report: dict) -> None:
        output.write_text(json.dumps(report))

    def test_verified_milestone_is_publishable_while_all_originals_remain_pending(self) -> None:
        with self.project() as (_, output, report):
            loaded, sha = finder.load_audit(REVISION)
            self.assertEqual(loaded, report)
            self.assertEqual(sha, hashlib.sha256(output.read_bytes()).hexdigest())
            self.assertFalse(loaded["chapter_complete"])
            self.assertEqual(set(loaded["notready_targets"]), set(audit.TARGETS))

    def test_generated_failed_unbound_and_false_complete_claims_are_rejected(self) -> None:
        changes = [("status", "generated_only"), ("status", "verification_failed"),
                   ("status", "verified_complete"), ("chapter_complete", True),
                   ("notready_targets", []), ("milestone_verified", False),
                   ("module_sources_match_revision", False), ("source_revision", "b" * 40),
                   ("inputs_unchanged_during_audit", False), ("schema_version", 9)]
        for key, value in changes:
            with self.subTest(key=key, value=value), self.project() as (_, output, report):
                report[key] = value
                self.save(output, report)
                with self.assertRaises(ValueError):
                    finder.load_audit(REVISION)

    def test_one_verified_original_target_and_four_pending_targets_publish_honestly(self) -> None:
        with self.project() as (root, output, _):
            inventory = json.loads(finder.INVENTORY.read_text())
            target = "def:cutoff-projection"
            inventory["targets"][target].update(status="implemented", required_declarations=["BC4lean.A.endpoint"])
            finder.INVENTORY.write_text(json.dumps(inventory))
            text = finder.BLUEPRINT.read_text().replace(
                audit_tests.statement(target),
                audit_tests.statement(target, r"\lean{BC4lean.A.endpoint}\leanok"))
            finder.BLUEPRINT.write_text(text)
            audit_tests.ProcessAndPublicationTests().run_main(root)
            report = json.loads(output.read_text())
            report["source_revision"] = REVISION
            self.save(output, report)
            loaded, _ = finder.load_audit(REVISION)
            self.assertTrue(loaded["target_inventory"][target]["ready"])
            self.assertEqual(len(loaded["notready_targets"]), 4)
            self.assertFalse(loaded["chapter_complete"])

    def test_wrong_revision_and_missing_type_fixture_binding_are_rejected(self) -> None:
        with self.project() as (_, output, report):
            for revision in ("main", "a" * 12, "g" * 40):
                with self.subTest(revision=revision), self.assertRaises(ValueError):
                    finder.load_audit(revision)
            report["expected_types_run"]["fixture"] = "/tmp/unrelated/ExpectedTypes.lean"
            self.save(output, report)
            with self.assertRaisesRegex(ValueError, "expected-type check"):
                finder.load_audit(REVISION)

    def test_changed_source_and_removed_control_hashes_are_rejected(self) -> None:
        with self.project() as (root, _, _):
            (root / "BC4lean/A.lean").write_text("theorem unrelated : True := True.intro\n")
            with self.assertRaisesRegex(ValueError, "Source no longer matches"):
                finder.load_audit(REVISION)
        for control in ("scripts/audit_chapter7.py", "docs/audits/chapter7/ExpectedTypes.lean",
                        "BC4lean.lean", "BC4lean/A.lean"):
            with self.subTest(control=control), self.project() as (_, output, report):
                del report["source_sha256"][control]
                self.save(output, report)
                with self.assertRaisesRegex(ValueError, "hash|source"):
                    finder.load_audit(REVISION)

    def test_missing_census_module_cannot_be_hidden_by_updating_source_hash(self) -> None:
        with self.project() as (root, output, report):
            aggregate = root / "BC4lean.lean"
            aggregate.write_bytes(aggregate.read_bytes() + b"import BC4lean.Omitted\n")
            report["source_sha256"]["BC4lean.lean"] = hashlib.sha256(aggregate.read_bytes()).hexdigest()
            self.save(output, report)
            with self.assertRaisesRegex(RuntimeError, "exactly cover"):
                finder.load_audit(REVISION)

    def test_raw_log_mutation_and_json_census_mutation_are_rejected(self) -> None:
        for stage in ("kernel", "expected-types", "build-gate", "historical-imports"):
            with self.subTest(stage=stage), self.project() as (_, output, _):
                output.with_suffix(f".{stage}.log").write_bytes(b"changed raw process output\n")
                with self.assertRaisesRegex(ValueError, "record/log"):
                    finder.load_audit(REVISION)
        with self.project() as (_, output, report):
            report["declaration_count"] = 99
            self.save(output, report)
            with self.assertRaisesRegex(ValueError, "raw kernel census"):
                finder.load_audit(REVISION)

    def test_patched_weak_commands_cannot_reuse_successful_exit_codes(self) -> None:
        cases = {"expected-types": "expected_types_run", "kernel": "kernel_run",
                 "build-gate": "cached_strict_build_gate", "historical-imports": "historical_imports_run"}
        for stage, key in cases.items():
            with self.subTest(stage=stage), self.project() as (_, output, report):
                command = report[key]["command"]
                if stage in {"expected-types", "kernel"}:
                    command.remove("-DwarningAsError=true")
                elif stage == "build-gate":
                    command.remove("--wfail")
                else:
                    command[-1] = "scripts/skip_historical_check.py"
                output.with_suffix(f".{stage}-run.json").write_text(json.dumps(report[key]))
                self.save(output, report)
                with self.assertRaisesRegex(ValueError, "strict audited command"):
                    finder.load_audit(REVISION)

    def test_capped_or_rewritten_query_is_rejected_even_when_hashes_are_updated(self) -> None:
        with self.project() as (_, output, report):
            query = output.with_suffix(".lean")
            query.write_text(query.read_text().replace("env.constants.toList", "env.constants.toList.take 1"))
            report["query_sha256"] = hashlib.sha256(query.read_bytes()).hexdigest()
            self.save(output, report)
            with self.assertRaisesRegex(ValueError, "uncapped inventory-generated census"):
                finder.load_audit(REVISION)

    def test_private_evidence_omission_is_rejected_even_with_consistent_counts(self) -> None:
        with self.project() as (_, output, report):
            log = output.with_suffix(".kernel.log")
            text = log.read_text().replace(
                "CH7_DECL|BC4lean.A|_private.BC4lean.A.0.helper|Classical.choice\n", "")
            text = text.replace("CH7_MODULE|BC4lean.A|2", "CH7_MODULE|BC4lean.A|1").replace(
                "CH7_END|3|1|1", "CH7_END|2|1|1")
            log.write_text(text)
            record = report["kernel_run"]
            record["stdout_stderr_sha256"] = hashlib.sha256(log.read_bytes()).hexdigest()
            output.with_suffix(".kernel-run.json").write_text(json.dumps(record))
            inventory = audit.load_inventory(finder.INVENTORY)
            report.update(audit.parse_kernel_evidence(text, inventory["modules"],
                                                      ["BC4lean.A.endpoint"], ["BC4lean.A.endpoint"]))
            self.save(output, report)
            with self.assertRaisesRegex(RuntimeError, "Private declarations missing"):
                finder.load_audit(REVISION)

    def test_unexpected_axioms_and_unhashed_objects_cannot_be_published(self) -> None:
        with self.project() as (_, output, report):
            report["linked_declarations"]["BC4lean.A.endpoint"]["axioms"] = ["sorryAx"]
            self.save(output, report)
            with self.assertRaisesRegex(ValueError, "Invalid retained"):
                finder.load_audit(REVISION)
        with self.project() as (_, output, report):
            del report["module_olean_sha256"][".lake/build/lib/lean/BC4lean/A.olean"]
            self.save(output, report)
            with self.assertRaisesRegex(ValueError, "compiled objects"):
                finder.load_audit(REVISION)

    def test_locations_require_exact_explicit_commands_at_pinned_revision(self) -> None:
        with self.project():
            def git(*args):
                return "BC4lean/A.lean" if args[0] == "ls-tree" else ""
            with patch.object(finder, "git", side_effect=git):
                locations, _ = finder.load_locations(REVISION)
            self.assertEqual(locations, {"BC4lean.A.endpoint": ("BC4lean/A.lean", 3)})
            with patch.object(finder, "git", return_value=""):
                with self.assertRaisesRegex(ValueError, "absent from pinned"):
                    finder.load_locations(REVISION)
            with patch.object(finder, "git", side_effect=["BC4lean/A.lean", "BC4lean/A.lean"]):
                with self.assertRaisesRegex(ValueError, "differs from pinned"):
                    finder.load_locations(REVISION)


class HtmlTests(unittest.TestCase):
    def setUp(self) -> None:
        self.previous = ("<!-- BEGIN GENERATED CHAPTER 6 SOURCE INDEX -->\n"
                         '<section id="chapter6-source-index">Historical block</section>\n'
                         "<!-- END GENERATED CHAPTER 6 SOURCE INDEX -->\n")
        self.base = "<html><body>Unchanged prefix\n" + self.previous + "Unchanged suffix</body></html>"
        self.locations = {"BC4lean.A.endpoint": ("BC4lean/A.lean", 3)}
        self.sha = "b" * 64

    def render(self, base: str | None = None) -> str:
        return finder.render(self.base if base is None else base, self.locations, REVISION, self.sha)

    def test_render_is_stable_and_preserves_all_historical_bytes(self) -> None:
        text = self.render()
        finder.verify_html(text, self.locations, REVISION, self.sha)
        self.assertEqual(finder.BLOCK.sub("", text), self.base)
        self.assertEqual(self.render(finder.BLOCK.sub("", text)), text)
        self.assertIn(self.previous, text)
        self.assertLess(text.index("chapter6-source-index"), text.index("chapter7-source-index"))

    def test_existing_canonical_fragment_is_not_duplicated(self) -> None:
        text = self.render(self.base + '<div id="doc/BC4lean.A.endpoint"></div>')
        finder.verify_html(text, self.locations, REVISION, self.sha)
        self.assertEqual(text.count('id="doc/BC4lean.A.endpoint"'), 1)

    def test_missing_or_duplicate_historical_insertion_point_is_rejected(self) -> None:
        for base in ("<html></html>", self.base + self.previous):
            with self.subTest(base=base), self.assertRaises(ValueError):
                self.render(base)

    def test_duplicate_fragments_stale_revision_and_incorrect_source_lines_are_rejected(self) -> None:
        text = self.render()
        for changed in (text + '<div id="doc/BC4lean.A.endpoint"></div>',
                        text.replace("#L3", "#L4"), text.replace(REVISION, "c" * 40),
                        text.replace(self.sha, "d" * 64),
                        text.replace('data-chapter7-declaration="BC4lean.A.endpoint"',
                                     'data-chapter7-declaration="BC4lean.Unrelated"')):
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                finder.verify_html(changed, self.locations, REVISION, self.sha)


if __name__ == "__main__":
    unittest.main()
