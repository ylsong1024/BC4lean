#!/usr/bin/env python3
"""Check retained-proof rendering and isolation from frozen blueprint inputs."""

import hashlib
from html import escape
import json
from pathlib import Path
import re
import runpy
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
BUILD = runpy.run_path(str(ROOT / "blueprint/src/build_web.py"))
PARSER = runpy.run_path(str(ROOT / "scripts/audit_chapter5.py"))
AUDIT = json.loads((ROOT / "docs/audits/chapter5/core-audit.json").read_text(encoding="utf-8"))
ORIGINAL = (ROOT / BUILD["CHAPTER5"]).read_bytes().decode("utf-8")


def rebound_audit(tex):
    """Exercise inventory guards independently of the production hash guard."""
    audit = dict(AUDIT)
    audit["source_sha256"] = dict(AUDIT["source_sha256"])
    audit["source_sha256"][BUILD["CHAPTER5"]] = hashlib.sha256(tex.encode("utf-8")).hexdigest()
    return audit


class RetainedProofRenderingTests(unittest.TestCase):
    def test_rendered_proofs_preserve_all_statements_links_and_existing_proofs(self):
        rendered = BUILD["verified_chapter5_tex"](ORIGINAL, AUDIT, PARSER)
        self.assertEqual(PARSER["audit_blueprint"](rendered), PARSER["audit_blueprint"](ORIGINAL))
        self.assertEqual(len(re.findall(r"\\begin\{proof\}", rendered)), 58)
        self.assertEqual(rendered.count(BUILD["RETAINED_PROOF_NOTE"]), 46)
        existing = re.findall(r"\\begin\{proof\}.*?\\end\{proof\}", ORIGINAL, re.S)
        self.assertEqual(len(existing), 12)
        for proof in existing:
            self.assertEqual(rendered.count(proof), 1)
        self.assertEqual((ROOT / BUILD["CHAPTER5"]).read_bytes().decode("utf-8"), ORIGINAL)

    def test_changed_source_cannot_inherit_retained_proof_status(self):
        with self.assertRaisesRegex(RuntimeError, "source hash differs"):
            BUILD["verified_chapter5_tex"](ORIGINAL + "\n", AUDIT, PARSER)

    def test_incomplete_audit_cannot_supply_proof_status(self):
        audit = dict(AUDIT, chapter_complete=False)
        with self.assertRaisesRegex(RuntimeError, "not complete"):
            BUILD["verified_chapter5_tex"](ORIGINAL, audit, PARSER)

    def test_new_statement_label_requires_explicit_inventory_review(self):
        tex = ORIGINAL.replace("prop:rectangular-module-compactness", "prop:unreviewed-target")
        with self.assertRaisesRegex(RuntimeError, "proof-label inventories changed"):
            BUILD["verified_chapter5_tex"](tex, rebound_audit(tex), PARSER)

    def test_unchecked_statement_cannot_be_promoted(self):
        tex = ORIGINAL.replace(
            "\\begin{proposition}\\label{prop:rectangular-module-compactness}",
            "\\begin{proposition}\\label{prop:rectangular-module-compactness}\\notready")
        with self.assertRaisesRegex(RuntimeError, "inventory differ"):
            BUILD["verified_chapter5_tex"](tex, rebound_audit(tex), PARSER)

    def test_existing_proof_is_never_replaced_to_hide_missing_status(self):
        tex = ORIGINAL.replace("\\begin{proof}\n\\leanok", "\\begin{proof}", 1)
        with self.assertRaisesRegex(RuntimeError, "existing proof.*not marked checked"):
            BUILD["verified_chapter5_tex"](tex, rebound_audit(tex), PARSER)

    def test_both_plastex_passes_use_the_temporary_source(self):
        with tempfile.TemporaryDirectory(prefix="test-blueprint-isolation-") as directory:
            temporary = Path(directory)
            source = temporary / "src"
            (source / "parts").mkdir(parents=True)
            (source / "macros").mkdir()
            (source / "parts/05-equivariant-kk.tex").write_text(ORIGINAL, encoding="utf-8")
            (source / "macros/web.tex").write_text("dep_by=chapter,", encoding="utf-8")
            (source / "web.tex").write_text("test input", encoding="utf-8")
            before = {p.relative_to(source): p.read_bytes() for p in source.rglob("*") if p.is_file()}
            calls = []

            def fake_plastex(command, *, cwd, check):
                cwd = Path(cwd)
                calls.append((cwd, (cwd / "macros/web.tex").read_text(),
                              (cwd / "parts/05-equivariant-kk.tex").read_text()))
                self.assertTrue(check)
                (cwd / "web.paux").write_text("plasTeX auxiliary output", encoding="utf-8")
                output = Path(command[command.index("--dir") + 1])
                output.mkdir(parents=True, exist_ok=True)
                (output / "dep_graph_document.html").write_text("overall graph", encoding="utf-8")

            rendered = BUILD["verified_chapter5_tex"](ORIGINAL, AUDIT, PARSER)
            output = temporary / "published"
            with patch("subprocess.run", side_effect=fake_plastex):
                BUILD["build_documents"](source, output, ["plastex"], rendered)
            self.assertEqual(len(calls), 2)
            self.assertEqual(calls[0][0], calls[1][0])
            self.assertNotEqual(calls[0][0], source)
            self.assertIn("dep_by=chapter,", calls[0][1])
            self.assertNotIn("dep_by=chapter,", calls[1][1])
            self.assertEqual([call[2] for call in calls], [rendered, rendered])
            after = {p.relative_to(source): p.read_bytes() for p in source.rglob("*") if p.is_file()}
            self.assertEqual(before, after)
            self.assertEqual((output / "dep_graph_document.html").read_text(), "overall graph")


class GeneratedStatusValidationTests(unittest.TestCase):
    def write_site(self, output):
        blocks = re.findall(r"\\begin\{(definition|proposition)\}(.*?)\\end\{\1\}", ORIGINAL, re.S)
        nodes, modals, statement_ids = [], [], []
        for kind, body in blocks:
            label = re.search(r"\\label\{([^}]+)\}", body)[1]
            declarations = {name.strip() for group in re.findall(r"\\lean\{([^}]+)\}", body)
                            for name in group.split(",") if name.strip()}
            shape = "box" if kind == "definition" else "ellipse"
            nodes.append(f'"{label}" [color=green, fillcolor="#1CAC78", style=filled, label="{label}", shape={shape}];')
            anchors = "".join(f'<a href="docs/find/#doc/{escape(name, quote=True)}">Lean</a>'
                              for name in sorted(declarations))
            modals.append(f'<div class="dep-modal-container" id="{label}_modal">'
                          f'<div class="dep-modal-content">{anchors}</div></div>')
            statement_ids.append(f'<div id="{label}">{anchors}</div>')
        graph = '<script>render.renderDot(`strict digraph { ' + "".join(nodes) + ' }`)</script>'
        for filename in ("dep_graph_chapter_5.html", "dep_graph_document.html"):
            (output / filename).write_text(graph + "".join(modals), encoding="utf-8")
        chapter = ("".join(statement_ids) + '<div class="proof_content"></div>' * 58
                   + "rendered from the retained Chapter 5 kernel evidence" * 46)
        (output / "ch-equivariant-kk.html").write_text(chapter, encoding="utf-8")

    def test_validates_both_graphs_and_all_435_links(self):
        with tempfile.TemporaryDirectory(prefix="test-rendered-status-") as directory:
            output = Path(directory)
            self.write_site(output)
            counts = BUILD["validate_rendered_chapter5"](output, ORIGINAL, PARSER)
            self.assertEqual(counts["statements"], 75)
            self.assertEqual(counts["lean_links"], 435)
            self.assertEqual(list(counts["required_endpoints"].values()), [18, 72, 16])
            self.assertEqual(len(counts["graphs"]), 2)

    def test_missing_proof_fill_fails_even_when_statement_border_is_green(self):
        with tempfile.TemporaryDirectory(prefix="test-rendered-status-") as directory:
            output = Path(directory)
            self.write_site(output)
            graph = output / "dep_graph_chapter_5.html"
            graph.write_text(graph.read_text().replace('fillcolor="#1CAC78",', "", 1))
            with self.assertRaisesRegex(RuntimeError, "lacks verified statement/proof colors"):
                BUILD["validate_rendered_chapter5"](output, ORIGINAL, PARSER)

    def test_global_graph_link_loss_fails_independently_of_chapter_graph(self):
        with tempfile.TemporaryDirectory(prefix="test-rendered-status-") as directory:
            output = Path(directory)
            self.write_site(output)
            graph = output / "dep_graph_document.html"
            graph.write_text(re.sub(r'<a href="[^"]+">Lean</a>', "", graph.read_text(), count=1))
            with self.assertRaisesRegex(RuntimeError, "dep_graph_document.html.*links differ"):
                BUILD["validate_rendered_chapter5"](output, ORIGINAL, PARSER)

    def test_fill_color_without_filled_style_is_rejected(self):
        with tempfile.TemporaryDirectory(prefix="test-rendered-status-") as directory:
            output = Path(directory)
            self.write_site(output)
            graph = output / "dep_graph_chapter_5.html"
            graph.write_text(graph.read_text().replace("style=filled,", "", 1))
            with self.assertRaisesRegex(RuntimeError, "lacks filled style"):
                BUILD["validate_rendered_chapter5"](output, ORIGINAL, PARSER)

    def test_rendered_page_must_explain_retained_proof_status(self):
        with tempfile.TemporaryDirectory(prefix="test-rendered-status-") as directory:
            output = Path(directory)
            self.write_site(output)
            page = output / "ch-equivariant-kk.html"
            page.write_text(page.read_text().replace(
                "rendered from the retained Chapter 5 kernel evidence", "", 1))
            with self.assertRaisesRegex(RuntimeError, "retained-evidence explanations"):
                BUILD["validate_rendered_chapter5"](output, ORIGINAL, PARSER)


if __name__ == "__main__":
    unittest.main()
