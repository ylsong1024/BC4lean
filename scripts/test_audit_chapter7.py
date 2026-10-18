#!/usr/bin/env python3
"""Regression checks for uncapped coverage and honest Chapter 7 milestones."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import audit_chapter7 as audit


def statement(label: str, body: str = r"\notready", kind: str | None = None) -> str:
    kind = kind or audit.TARGET_KINDS.get(label, "lemma")
    return rf"\begin{{{kind}}}\label{{{label}}}{body}\end{{{kind}}}"


def inventory() -> dict:
    return {"schema_version": 1, "modules": ["BC4lean.A", "BC4lean.B"],
            "additional_source_modules": [],
            "targets": {label: {"status": "pending", "description": "Original mathematical target",
                                "required_declarations": [], "blocked_reason": "Still unimplemented"}
                        for label in audit.TARGETS},
            "milestones": {"lemma:real-milestone": {"description": "A proved supporting lemma",
                                                     "required_declarations": ["BC4lean.A.endpoint"]}}}


def blueprint() -> str:
    return "\n".join([*(statement(label) for label in audit.TARGETS),
                       statement("lemma:real-milestone", r"\lean{BC4lean.A.endpoint}\leanok")])


def kernel_output() -> str:
    return ("CH7_START|1\n"
            "CH7_DECL|BC4lean.A|BC4lean.A.endpoint|propext\n"
            "CH7_DECL|BC4lean.A|_private.BC4lean.A.0.helper|Classical.choice\n"
            "CH7_DECL|BC4lean.B|BC4lean.B.generated._proof_1|Quot.sound\n"
            "CH7_LINK|BC4lean.A.endpoint|BC4lean.A|propext\n"
            "CH7_MODULE|BC4lean.A|2\nCH7_MODULE|BC4lean.B|1\n"
            "CH7_ENDPOINT|BC4lean.A.endpoint|BC4lean.A|propext\n"
            "CH7_END|3|1|1\n")


class InventoryTests(unittest.TestCase):
    def test_pending_targets_need_reasons_and_no_invented_endpoints(self) -> None:
        for change in ("missing_target", "fake_endpoint", "no_reason", "unknown_status",
                       "no_milestone", "empty_milestone", "reused_original_label",
                       "duplicate_module", "overlapping_source", "nonexact_endpoint"):
            data = inventory()
            first = data["targets"][audit.TARGETS[0]]
            if change == "missing_target":
                del data["targets"][audit.TARGETS[0]]
            elif change == "fake_endpoint":
                first["required_declarations"] = ["BC4lean.NotImplemented"]
            elif change == "no_reason":
                first["blocked_reason"] = " "
            elif change == "unknown_status":
                first["status"] = "verified"
            elif change == "no_milestone":
                data["milestones"] = {}
            elif change == "empty_milestone":
                data["milestones"]["lemma:real-milestone"]["required_declarations"] = []
            elif change == "reused_original_label":
                data["milestones"][audit.TARGETS[0]] = data["milestones"].pop("lemma:real-milestone")
            elif change == "duplicate_module":
                data["modules"] *= 2
            elif change == "overlapping_source":
                data["additional_source_modules"] = ["BC4lean.A"]
            else:
                data["milestones"]["lemma:real-milestone"]["required_declarations"] = ["Alias"]
            with self.subTest(change=change), self.assertRaises(ValueError):
                audit.load_inventory(Path("unused"), json.dumps(data).encode())

    def test_implemented_targets_need_real_nonempty_endpoint_inventories(self) -> None:
        data = inventory()
        data["targets"][audit.TARGETS[0]]["status"] = "implemented"
        with self.assertRaises(ValueError):
            audit.load_inventory(Path("unused"), json.dumps(data).encode())
        data["targets"][audit.TARGETS[0]]["required_declarations"] = ["BC4lean.A.endpoint"]
        self.assertEqual(audit.load_inventory(Path("unused"), json.dumps(data).encode()), data)


class BlueprintTests(unittest.TestCase):
    def test_milestones_never_make_original_targets_ready(self) -> None:
        links, targets, milestones = audit.audit_blueprint(blueprint(), inventory())
        self.assertEqual(links, ["BC4lean.A.endpoint"])
        self.assertTrue(all(not target["ready"] for target in targets.values()))
        self.assertTrue(milestones["lemma:real-milestone"]["ready"])
        self.assertEqual(set(audit.pending_blueprint_targets(blueprint())), set(audit.TARGETS))

    def test_partial_support_cannot_certify_a_pending_original_target(self) -> None:
        for body in (r"\leanok", r"\lean{BC4lean.A.endpoint}\leanok", "", r"\notready\leanok"):
            text = blueprint().replace(statement(audit.TARGETS[0]), statement(audit.TARGETS[0], body))
            with self.subTest(body=body), self.assertRaisesRegex(ValueError, "Pending original|contradictory"):
                audit.audit_blueprint(text, inventory())

    def test_deleted_duplicate_or_retyped_original_target_is_rejected(self) -> None:
        first = statement(audit.TARGETS[0])
        for text in (blueprint().replace(first, ""), blueprint() + first,
                     blueprint() + rf"\label{{{audit.TARGETS[0]}}}",
                     blueprint().replace(first, statement(audit.TARGETS[0], kind="lemma"))):
            with self.subTest(text=text), self.assertRaises(ValueError):
                audit.audit_blueprint(text, inventory())

    def test_milestone_requires_exact_links_and_one_ready_marker(self) -> None:
        old = statement("lemma:real-milestone", r"\lean{BC4lean.A.endpoint}\leanok")
        for body in (r"\leanok", r"\lean{BC4lean.Unrelated}\leanok", r"\notready",
                     r"\lean{BC4lean.A.endpoint}\leanok\leanok",
                     "% \\lean{BC4lean.A.endpoint}\\leanok\n"):
            with self.subTest(body=body), self.assertRaises(ValueError):
                audit.audit_blueprint(blueprint().replace(old, statement("lemma:real-milestone", body)), inventory())

    def test_empty_links_are_rejected_and_extra_pending_statements_are_retained(self) -> None:
        with self.assertRaisesRegex(ValueError, "Empty exact"):
            audit.audit_blueprint(blueprint() + r"\lean{}", inventory())
        pending = audit.pending_blueprint_targets(blueprint() + statement("lemma:unfinished-support"))
        self.assertIn("lemma:unfinished-support", pending)


class ScopeAndSourceTests(unittest.TestCase):
    def setUp(self) -> None:
        self.baseline = b"import BC4lean.Historical\n"
        self.sha = hashlib.sha256(self.baseline).hexdigest()
        self.aggregate = self.baseline + b"import BC4lean.A\nimport BC4lean.B\n"

    def check(self, aggregate: bytes, baseline: bytes | None = None) -> None:
        audit.check_scope_coverage(aggregate, self.baseline if baseline is None else baseline,
                                   ["BC4lean.A", "BC4lean.B"], self.sha)

    def test_new_imports_exactly_match_census_and_allow_comments(self) -> None:
        self.check(self.aggregate + b"-- explanation\n")

    def test_omitted_added_repeated_historical_or_rewritten_imports_are_rejected(self) -> None:
        for aggregate in (self.aggregate.replace(b"import BC4lean.B\n", b""),
                          self.aggregate + b"import BC4lean.C\n",
                          self.aggregate + b"import BC4lean.A\n",
                          self.aggregate + b"import BC4lean.Historical\n",
                          b"-- altered prefix\n" + self.aggregate,
                          self.aggregate + b"set_option autoImplicit true\n"):
            with self.subTest(aggregate=aggregate), self.assertRaises(RuntimeError):
                self.check(aggregate)
        with self.assertRaisesRegex(RuntimeError, "wrong hash"):
            self.check(self.aggregate, self.baseline + b"\n")

    def test_real_frozen_chapter6_sources_are_unchanged(self) -> None:
        captured = audit.historical_inputs()
        self.assertIn(audit.ROOT / "docs/audits/chapter6/audit.json", captured)
        self.assertGreater(len(captured), 20)

    def test_proof_holes_axioms_and_option_weakening_are_rejected(self) -> None:
        for token in ("sorry", "admit", "axiom", "sorryAx"):
            with self.subTest(token=token), self.assertRaises(RuntimeError):
                audit.check_proof_tokens(f"example : False := {token}", "fixture")
        for option in ("autoImplicit true", "relaxedAutoImplicit true", "warningAsError false",
                       "debug.skipKernelTC true"):
            with self.subTest(option=option), self.assertRaises(RuntimeError):
                audit.check_strict_options(f"set_option {option} in\nexample : True := trivial", "fixture")
        source = '/- sorry /- axiom -/ admit -/\ndef text := "sorryAx"\n-- set_option autoImplicit true\n'
        audit.check_proof_tokens(source, "fixture")
        audit.check_strict_options(source, "fixture")

    def test_new_mathematics_cannot_patch_the_census_or_kernel_environment(self) -> None:
        for source in ("unsafe def replacement := 0", "run_cmd pure ()", "initialize pure ()",
                       "macro_rules | _ => unreachable!", "elab_rules : command | _ => pure ()",
                       "@[command_elab bad] def patch := 0", "attribute [implemented_by fake] real",
                       "#eval IO.println 0", "set_option debug.skipKernelTC true",
                       "instance : Lean.MonadEnv Fake := ⟨pure default, fun _ => pure ()⟩",
                       "import UncensusedLocalModule", "meta import Mathlib.Tactic",
                       'notation "Lean.collectAxioms" => fake', 'local infix "++" => fake',
                       'def hidden := s!"{(by run_tac patch : Nat)}"'):
            with self.subTest(source=source), self.assertRaises(RuntimeError):
                audit.check_strict_options(source, "fixture")
                audit.check_no_environment_patches(source, "fixture")
        audit.check_no_environment_patches('/- run_cmd initialize -/\ndef text := "macro unsafe"', "fixture")
        audit.check_no_environment_patches("import BC4lean.Known\nimport Mathlib.Tactic\n", "fixture")

    def test_private_declarations_need_actual_kernel_evidence(self) -> None:
        with self.assertRaisesRegex(RuntimeError, "Private declarations missing"):
            audit.check_private_coverage({"BC4lean.A": "private theorem helper : True := trivial"}, [])


class KernelEvidenceTests(unittest.TestCase):
    def parse(self, output: str) -> dict:
        return audit.parse_kernel_evidence(output, ["BC4lean.A", "BC4lean.B"],
                                           ["BC4lean.A.endpoint"], ["BC4lean.A.endpoint"])

    def test_private_and_generated_declarations_are_kept_by_module_origin(self) -> None:
        report = self.parse(kernel_output())
        self.assertEqual(report["declaration_count"], 3)
        self.assertEqual(report["module_declaration_counts"], {"BC4lean.A": 2, "BC4lean.B": 1})
        self.assertEqual(report["axioms"], ["Classical.choice", "Quot.sound", "propext"])
        self.assertIn("_private.BC4lean.A.0.helper", [row["name"] for row in report["declarations"]])

    def test_query_has_no_cap_or_name_prefix_filter_and_checks_actual_axiom_closure(self) -> None:
        query = audit.generate_query(["BC4lean.A", "BC4lean.B"], ["BC4lean.A.endpoint"],
                                     ["BC4lean.A.endpoint"])
        self.assertIn("for (name, info) in env.constants.toList", query)
        self.assertIn("env.getModuleIdxFor? name", query)
        self.assertIn("collectAxioms name", query)
        self.assertIn("env := (← Lean.getEnv).setExporting false", query)
        self.assertIn("Lean.collectAxioms name", query)
        self.assertIn("Lean.Elab.Command.liftIO <|", query)
        self.assertIn(".axiomInfo", query)
        self.assertIn("CH7_ENDPOINT", query)
        self.assertNotIn("import BC4lean\n", query)
        self.assertNotIn(".take ", query)
        self.assertNotIn("name.toString.startsWith", query)
        self.assertNotIn("CH6_", query)

    def test_duplicate_truncated_missing_and_inconsistent_records_are_rejected(self) -> None:
        output = kernel_output()
        broken = [output + "CH7_END|3|1|1\n", output.replace("CH7_END|3|1|1", "CH7_END|2|1|1"),
                  output.replace("CH7_START|1", "CH7_START|1\nCH7_START|1"),
                  output.replace("CH7_MODULE|BC4lean.B|1\n", ""),
                  output.replace("CH7_MODULE|BC4lean.A|2", "CH7_MODULE|BC4lean.A|1"),
                  output.replace("CH7_ENDPOINT|BC4lean.A.endpoint|BC4lean.A|propext\n", ""),
                  output.replace("CH7_LINK|BC4lean.A.endpoint|BC4lean.A|propext\n", ""),
                  output.replace("CH7_LINK|BC4lean.A.endpoint|BC4lean.A|propext",
                                 "CH7_LINK|BC4lean.A.endpoint|BC4lean.A|Quot.sound"),
                  output.replace("CH7_END|3|1|1", "")]
        for text in broken:
            with self.subTest(text=text), self.assertRaises(RuntimeError):
                self.parse(text)

    def test_sorry_axioms_outside_origins_and_uncensused_endpoints_are_rejected(self) -> None:
        output = kernel_output()
        for text in (output.replace("propext", "sorryAx"),
                     output.replace("Classical.choice", "BC4lean.HiddenAxiom"),
                     output.replace("CH7_DECL|BC4lean.B", "CH7_DECL|BC4lean.Omitted"),
                     output.replace("CH7_ENDPOINT|BC4lean.A.endpoint|BC4lean.A",
                                    "CH7_ENDPOINT|BC4lean.A.endpoint|BC4lean.Old"),
                     output.replace("CH7_DECL|BC4lean.A|BC4lean.A.endpoint",
                                    "CH7_DECL|BC4lean.A|BC4lean.A.other")):
            with self.subTest(text=text), self.assertRaises(RuntimeError):
                self.parse(text)


class ProcessAndPublicationTests(unittest.TestCase):
    """Execute orchestration with tiny files; never invoke Lean in these tests."""

    def make_project(self, root: Path) -> None:
        baseline = (audit.ROOT / "docs/audits/chapter7/Chapter6Imports.lean").read_bytes()
        files = {"docs/audits/chapter7/inventory.json": json.dumps(inventory()),
                 "blueprint/src/parts/07-assembly-map.tex": blueprint(),
                 "docs/audits/chapter7/ExpectedTypes.lean": "example : True := True.intro\n",
                 "BC4lean/A.lean": "private theorem helper : True := True.intro\n",
                 "BC4lean/B.lean": "theorem generated : True := True.intro\n",
                 "scripts/audit_chapter7.py": "# synthetic audited control\n",
                 "scripts/test_audit_chapter7.py": "# synthetic audited control\n",
                 "scripts/update_chapter7_finder.py": "# synthetic audited control\n",
                 "scripts/test_chapter7_publication.py": "# synthetic audited control\n",
                 "scripts/check_chapter7_website.py": "# synthetic audited control\n",
                 "scripts/test_chapter7_website.py": "# synthetic audited control\n",
                 ".github/workflows/chapter7.yml": "name: synthetic\n",
                 "lean-toolchain": "leanprover/lean4:test\n", "lakefile.toml": "name = 'test'\n",
                 "lake-manifest.json": "{}\n",
                 ".lake/build/lib/lean/BC4lean/A.olean": "synthetic object A\n",
                 ".lake/build/lib/lean/BC4lean/B.olean": "synthetic object B\n"}
        for relative, text in files.items():
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        (root / "docs/audits/chapter7/Chapter6Imports.lean").write_bytes(baseline)
        (root / "BC4lean.lean").write_bytes(baseline + b"import BC4lean.A\nimport BC4lean.B\n")

    def run_main(self, root: Path, flags: list[str] | None = None, fail: str | None = None,
                 mutate: str | None = None) -> tuple[int, list[list[str]]]:
        calls = []

        def external(command, **kwargs):
            calls.append(command)
            if command[0] == "git":
                return SimpleNamespace(returncode=0, stdout="source-revision\n")
            if command[0] == sys.executable:
                stage, stdout = "historical-imports", b"historical imports current\n"
            elif command[1] == "--wfail":
                stage, stdout = "build-gate", b"strict aggregate current\n"
            elif command[-1].endswith("ExpectedTypes.lean"):
                stage, stdout = "expected-types", b"independent types checked\n"
            else:
                stage, stdout = "kernel", kernel_output().encode()
                if mutate:
                    (root / mutate).write_text("changed during verification\n")
            return SimpleNamespace(returncode=7 if fail == stage else 0, stdout=stdout)

        argv = ["audit_chapter7.py", "--output", str(root / "result/audit.json"), *(flags or [])]
        with patch.object(audit, "ROOT", root), patch.object(audit, "historical_inputs", return_value={}), \
                patch.object(audit.subprocess, "run", side_effect=external), patch("sys.argv", argv), \
                patch("builtins.print"):
            result = audit.main()
        return result, calls

    def test_generate_only_never_runs_lean_or_claims_verification(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            self.make_project(root)
            result, calls = self.run_main(root, ["--generate-only", "--require-complete"])
            self.assertEqual(result, 0)
            self.assertTrue(all(command[0] == "git" for command in calls))
            report = json.loads((root / "result/audit.json").read_text())
            self.assertEqual(report["status"], "generated_only")
            self.assertFalse(report["chapter_complete"])
            self.assertFalse(report["milestone_verified"])
            self.assertIn("docs/audits/chapter7/ExpectedTypes.lean", report["source_sha256"])

    def test_actual_process_records_hashes_and_pending_status_are_retained(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            self.make_project(root)
            result, calls = self.run_main(root, ["--require-complete"])
            self.assertEqual(result, 2)
            report = json.loads((root / "result/audit.json").read_text())
            self.assertEqual(report["status"], "verified_milestone")
            self.assertTrue(report["milestone_verified"])
            self.assertFalse(report["chapter_complete"])
            self.assertEqual(set(report["notready_targets"]), set(audit.TARGETS))
            self.assertIn(["lake", "--wfail", "--no-build", "--no-cache", "build", "BC4lean"], calls)
            self.assertEqual(len(report["module_olean_sha256"]), 2)
            for suffix in ("historical-imports", "build-gate", "expected-types", "kernel"):
                record = json.loads((root / f"result/audit.{suffix}-run.json").read_text())
                log = root / f"result/audit.{suffix}.log"
                self.assertEqual(record["exit_code"], 0)
                self.assertEqual(record["stdout_stderr_sha256"], hashlib.sha256(log.read_bytes()).hexdigest())
            command = report["expected_types_run"]["command"]
            for flag in ("-j1", "-DwarningAsError=true", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false"):
                self.assertIn(flag, command)

    def test_process_failures_never_publish_verified_evidence(self) -> None:
        for stage in ("historical-imports", "build-gate", "expected-types", "kernel"):
            with self.subTest(stage=stage), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                self.make_project(root)
                with self.assertRaisesRegex(RuntimeError, f"{stage} failed"):
                    self.run_main(root, fail=stage)
                report = json.loads((root / "result/audit.json").read_text())
                self.assertEqual(report["status"], "verification_failed")
                self.assertFalse(report["milestone_verified"])
                self.assertFalse(report["chapter_complete"])
                record = json.loads((root / f"result/audit.{stage}-run.json").read_text())
                self.assertEqual(record["exit_code"], 7)
                if stage == "expected-types":
                    self.assertFalse((root / "result/audit.kernel-run.json").exists())

    def test_a_genuine_original_endpoint_can_be_ready_while_four_others_remain_pending(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            self.make_project(root)
            data = inventory()
            target = "def:cutoff-projection"
            data["targets"][target].update(status="implemented", required_declarations=["BC4lean.A.endpoint"])
            (root / "docs/audits/chapter7/inventory.json").write_text(json.dumps(data))
            text = blueprint().replace(statement(target),
                                       statement(target, r"\lean{BC4lean.A.endpoint}\leanok"))
            (root / "blueprint/src/parts/07-assembly-map.tex").write_text(text)
            result, _ = self.run_main(root, ["--require-complete"])
            self.assertEqual(result, 2)
            report = json.loads((root / "result/audit.json").read_text())
            self.assertTrue(report["target_inventory"][target]["ready"])
            self.assertEqual(len(report["notready_targets"]), 4)
            self.assertTrue(report["milestone_verified"])
            self.assertFalse(report["chapter_complete"])

    def test_source_object_fixture_and_query_mutation_prevent_publication(self) -> None:
        for relative in ("BC4lean/A.lean", ".lake/build/lib/lean/BC4lean/A.olean",
                         "docs/audits/chapter7/ExpectedTypes.lean", "result/audit.lean"):
            with self.subTest(relative=relative), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                self.make_project(root)
                with self.assertRaisesRegex(RuntimeError, "changed during verification"):
                    self.run_main(root, mutate=relative)
                report = json.loads((root / "result/audit.json").read_text())
                self.assertEqual(report["status"], "verification_failed")
                self.assertFalse(report["chapter_complete"])

    def test_expected_fixture_changed_before_check_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Path(directory) / "ExpectedTypes.lean"
            fixture.write_text("example : True := True.intro\n")
            with self.assertRaisesRegex(RuntimeError, "fixture changed before"):
                audit.run_expected_types(fixture, Path(directory) / "audit.json", "0" * 64)


if __name__ == "__main__":
    unittest.main()
