#!/usr/bin/env python3
"""Adversarial rendered-site fixtures for Chapter 7's mixed readiness status.

The fixtures use the real frozen _Chapter5HTML parser and the actual theorem,
proof, DOT, and popup shapes emitted by plasTeX/leanblueprint. They do not run
Lean or a renderer, or change historical source/website records.
"""
from __future__ import annotations

from contextlib import contextmanager
from copy import deepcopy
from html import escape
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

import audit_chapter7 as audit
import check_chapter7_website as check

ROOT = Path(__file__).resolve().parents[1]
REVISION = "a" * 40
SOURCE_BASE = "https://ylsong1024.github.io/BC4lean/docs/find/"
CUTOFF = "def:cutoff-projection"
FOUNDATION = "def:fixture-foundation"
LAW = "prop:fixture-law"
GRAPHS = ("dep_graph_chapter_7.html", "dep_graph_document.html")


def statement(label, body):
    kind = audit.TARGET_KINDS.get(label, "definition" if label == FOUNDATION else "proposition")
    return rf"\begin{{{kind}}}\label{{{label}}}{body}\end{{{kind}}}"


def source_fixture():
    inventory = {"schema_version": 1, "modules": ["BC4lean.A", "BC4lean.B"],
                 "additional_source_modules": [],
                 "targets": {label: {"description": "An original target", "status": "pending",
                                     "required_declarations": [], "blocked_reason": "Not implemented"}
                             for label in audit.TARGETS},
                 "milestones": {
                     FOUNDATION: {"description": "A supporting construction",
                                  "required_declarations": ["BC4lean.A.foundation"]},
                     LAW: {"description": "A supporting checked theorem",
                           "required_declarations": ["BC4lean.B.law"]}}}
    inventory["targets"][CUTOFF].update(status="implemented", required_declarations=["BC4lean.A.cutoff"])
    bodies = {
        "def:reduced-descent": r"\notready\lean{BC4lean.A.partial}",
        CUTOFF: r"\lean{BC4lean.A.cutoff}\leanok\uses{def:reduced-descent}",
        "def:assembly-piece": r"\notready\uses{def:cutoff-projection}",
        "prop:assembly-compatibility": r"\notready\uses{def:assembly-piece}",
        "def:assembly-map": r"\notready\uses{prop:assembly-compatibility}",
        FOUNDATION: r"\lean{BC4lean.A.foundation}\leanok",
        LAW: r"\lean{BC4lean.B.law}\leanok\uses{prop:assembly-compatibility}"}
    tex = "\n".join(statement(label, body) for label, body in bodies.items())
    tex += "\n" + r"\begin{proof}\leanok The linked theorem proves the law.\end{proof}"
    links, targets, milestones = audit.audit_blueprint(tex, inventory)
    evidence = {"blueprint_links": links, "target_inventory": targets, "milestone_inventory": milestones,
                "notready_targets": audit.pending_blueprint_targets(tex), "chapter_complete": False}
    return inventory, tex, evidence


def source_link(name):
    return f'<a class="lean-link" href="{SOURCE_BASE}#doc/{escape(name, quote=True)}">Lean</a>'


def proof_wrapper():
    return ('<div class="proof_wrapper"><div class="proof_heading">Proof</div>'
            '<div class="proof_content">A checked proof.</div></div>')


class WebsiteTests(unittest.TestCase):
    @contextmanager
    def fixture(self):
        with tempfile.TemporaryDirectory(prefix="chapter7-site-test-") as directory:
            root = Path(directory).resolve()
            inventory, tex, evidence = source_fixture()
            source = root / "blueprint/src"
            (source / "parts").mkdir(parents=True)
            (source / "parts/07-assembly-map.tex").write_text(tex)
            shutil.copyfile(ROOT / "blueprint/src/build_web.py", source / "build_web.py")
            inventory_file = root / "docs/audits/chapter7/inventory.json"
            inventory_file.parent.mkdir(parents=True)
            inventory_file.write_text(json.dumps(inventory))
            site = root / "site"
            output = site / "blueprint"
            output.mkdir(parents=True)
            self.write_rendered(output, evidence)
            (site / "docs/find").mkdir(parents=True)
            (site / "docs/find/index.html").write_text(
                f'<section data-chapter7-source-revision="{REVISION}"></section>')
            (site / "index.html").write_text(
                "<p>Chapter 7 has verified foundations; the assembly map remains incomplete.</p>")
            with patch.object(check, "ROOT", root):
                yield root, output, tex, evidence

    def write_rendered(self, output, evidence):
        items = {**evidence["target_inventory"], **evidence["milestone_inventory"]}
        chapter, nodes, modals = [], [], []
        for label, item in items.items():
            links = "".join(source_link(name) for name in item["linked_declarations"])
            kind = item["statement_kind"]
            chapter.append(f'<div class="{kind}_thmwrapper theorem-style-definition" id="{label}">'
                           f'<div class="{kind}_thmheading">{links}</div>'
                           f'<div class="{kind}_thmcontent">Statement.</div></div>')
            if label == LAW:
                chapter.append(proof_wrapper())
            shape = "box" if kind == "definition" else "ellipse"
            if item["ready"]:
                fill = "#B0ECA3" if kind == "definition" else "#9CEC8B"
                colors = f'color=green, fillcolor="{fill}", style=filled, '
            else:
                colors = 'color="#FFAA33", '
            nodes.append(f'"{label}" [{colors}label="{label}", shape={shape}];')
            modals.append(f'<div class="dep-modal-container" id="{label}_modal">'
                          '<div class="dep-modal-content">'
                          f'<div class="thm" id="{label}" style="display: none">{links}'
                          f'<a class="latex_link" href="ch-assembly-map.html#{label}">LaTeX</a>'
                          '</div></div></div>')
        edges = [('def:reduced-descent', CUTOFF), (CUTOFF, 'def:assembly-piece'),
                 ('def:assembly-piece', 'prop:assembly-compatibility'),
                 ('prop:assembly-compatibility', 'def:assembly-map'),
                 ('prop:assembly-compatibility', LAW)]
        dot = "".join(nodes) + "".join(f'"{a}" -> "{b}" [style=dashed];' for a, b in edges)
        graph = '<script>render.renderDot(`strict digraph { ' + dot + ' }`)</script>'
        for filename in GRAPHS:
            (output / filename).write_text(graph + "".join(modals))
        (output / "ch-assembly-map.html").write_text("".join(chapter))

    def validate(self, output, tex, evidence):
        return check.validate_rendered_chapter7(output, tex, evidence)

    def mutate(self, output, relative, old, new):
        path = output / relative
        text = path.read_text()
        self.assertIn(old, text)
        path.write_text(text.replace(old, new, 1))

    def test_one_verified_original_four_pending_and_direct_checked_proof_are_accepted(self):
        with self.fixture() as (_, output, tex, evidence):
            result = self.validate(output, tex, evidence)
            self.assertFalse(result["chapter_complete"])
            self.assertTrue(result["original_targets"][CUTOFF])
            self.assertEqual(sum(result["original_targets"].values()), 1)
            self.assertEqual(result["explicit_proofs"], 1)
            self.assertEqual(result["statements"], 7)
            self.assertEqual(set(result["graphs"]), set(GRAPHS))

    def test_fully_checked_proof_fill_is_also_accepted(self):
        with self.fixture() as (_, output, tex, evidence):
            for filename in GRAPHS:
                self.mutate(output, filename, '#9CEC8B', '#1CAC78')
            self.validate(output, tex, evidence)

    def test_pending_original_cannot_have_green_border_or_green_fill_independently(self):
        for filename in GRAPHS:
            for colors in ('color=green, ', 'color=darkgreen, ',
                           'color="#FFAA33", fillcolor="#B0ECA3", style=filled, ',
                           'color="#FFAA33", fillcolor="#9CEC8B", style=filled, ',
                           'color="#FFAA33", fillcolor="#1CAC78", style=filled, '):
                with self.subTest(filename=filename, colors=colors), self.fixture() as (_, output, tex, evidence):
                    self.mutate(output, filename, '"def:reduced-descent" [color="#FFAA33", ',
                                '"def:reduced-descent" [' + colors)
                    with self.assertRaisesRegex(ValueError, "pending original.*false checked/readiness"):
                        self.validate(output, tex, evidence)

    def test_definition_and_proof_fills_are_not_interchangeable(self):
        for before, after in (('#B0ECA3', '#9CEC8B'), ('#9CEC8B', '#B0ECA3')):
            with self.subTest(before=before), self.fixture() as (_, output, tex, evidence):
                self.mutate(output, GRAPHS[0], before, after)
                with self.assertRaisesRegex(ValueError, "definition/proof fill"):
                    self.validate(output, tex, evidence)

    def test_unfilled_substring_does_not_count_as_filled_style(self):
        with self.fixture() as (_, output, tex, evidence):
            self.mutate(output, GRAPHS[0], "style=filled", "style=unfilled")
            with self.assertRaisesRegex(ValueError, "fill style"):
                self.validate(output, tex, evidence)

    def test_pending_original_cannot_claim_a_checked_source_proof(self):
        with self.fixture() as (_, output, tex, evidence):
            marker = statement('prop:assembly-compatibility', r'\notready\uses{def:assembly-piece}')
            tex = tex.replace(marker, marker + r'\begin{proof}\leanok\end{proof}')
            with self.assertRaisesRegex(ValueError, "pending original.*checked proof"):
                self.validate(output, tex, evidence)

    def test_checked_proposition_requires_an_explicit_checked_source_proof(self):
        for replacement in ('', r'\begin{proof}Unverified draft.\end{proof}',
                            r'\begin{proof}\notready\leanok\end{proof}'):
            with self.subTest(replacement=replacement), self.fixture() as (_, output, tex, evidence):
                tex = tex.replace(r'\begin{proof}\leanok The linked theorem proves the law.\end{proof}', replacement)
                with self.assertRaisesRegex(ValueError, "explicit checked proof"):
                    self.validate(output, tex, evidence)

    def test_missing_duplicate_and_stale_chapter_graph_nodes_are_rejected(self):
        for filename in GRAPHS:
            with self.subTest(filename=filename), self.fixture() as (_, output, tex, evidence):
                node = '"def:assembly-map" [color="#FFAA33", label="def:assembly-map", shape=box];'
                self.mutate(output, filename, node, '')
                with self.assertRaisesRegex(ValueError, "missing Chapter 7 nodes"):
                    self.validate(output, tex, evidence)
        with self.fixture() as (_, output, tex, evidence):
            node = '"def:assembly-map" [color="#FFAA33", label="def:assembly-map", shape=box];'
            self.mutate(output, GRAPHS[0], node, node + node)
            with self.assertRaisesRegex(ValueError, "duplicate node"):
                self.validate(output, tex, evidence)
        with self.fixture() as (_, output, tex, evidence):
            self.mutate(output, GRAPHS[0], 'strict digraph { ',
                        'strict digraph { "def:removed-milestone" [label="stale", shape=box];')
            with self.assertRaisesRegex(ValueError, "unexpected Chapter 7 graph node"):
                self.validate(output, tex, evidence)

    def test_global_graph_stale_chapter_popup_is_rejected_but_other_chapters_are_allowed(self):
        for target, accepted in (("ch-prior.html#def:prior", True),
                                 ("ch-assembly-map.html#def:prior", False)):
            with self.subTest(target=target), self.fixture() as (_, output, tex, evidence):
                self.mutate(output, GRAPHS[1], 'strict digraph { ',
                            'strict digraph { "def:prior" [label="prior", shape=box];')
                path = output / GRAPHS[1]
                path.write_text(path.read_text() + f'<div class="dep-modal-container" id="def:prior_modal">'
                                f'<a href="{target}">LaTeX</a></div>')
                if accepted:
                    self.validate(output, tex, evidence)
                else:
                    with self.assertRaisesRegex(ValueError, "stale Chapter 7 node/popup"):
                        self.validate(output, tex, evidence)

    def test_dependency_paths_allow_transitive_reduction_but_reject_missing_relations(self):
        with self.fixture() as (_, output, tex, evidence):
            # The renderer correctly removes descent -> piece as redundant:
            # descent -> cutoff -> piece already witnesses that dependency.
            tex = tex.replace(r'\uses{def:cutoff-projection}',
                              r'\uses{def:cutoff-projection,def:reduced-descent}')
            self.validate(output, tex, evidence)
        for filename in GRAPHS:
            with self.subTest(filename=filename), self.fixture() as (_, output, tex, evidence):
                self.mutate(output, filename,
                            '"def:cutoff-projection" -> "def:assembly-piece" [style=dashed];', '')
                with self.assertRaisesRegex(ValueError, "missing source dependency path"):
                    self.validate(output, tex, evidence)

    def test_global_popup_link_loss_is_detected_independently_of_chapter_graph(self):
        with self.fixture() as (_, output, tex, evidence):
            self.mutate(output, GRAPHS[1], source_link("BC4lean.A.cutoff"), '')
            with self.assertRaisesRegex(ValueError, "dep_graph_document.html.*source-link popup"):
                self.validate(output, tex, evidence)

    def test_duplicate_or_missing_popups_are_rejected(self):
        for replacement in ('id="missing_modal"', 'id="def:cutoff-projection_modal"'):
            with self.subTest(replacement=replacement), self.fixture() as (_, output, tex, evidence):
                path = output / GRAPHS[0]
                if replacement == 'id="missing_modal"':
                    self.mutate(output, GRAPHS[0], 'id="def:cutoff-projection_modal"', replacement)
                else:
                    path.write_text(path.read_text() + '<div class="dep-modal-container" '
                                    + replacement + '></div>')
                with self.assertRaisesRegex(ValueError, "source-link popup"):
                    self.validate(output, tex, evidence)

    def test_swapped_statement_links_cannot_hide_behind_unchanged_total_link_set(self):
        with self.fixture() as (_, output, tex, evidence):
            path = output / "ch-assembly-map.html"
            text = path.read_text().replace("BC4lean.A.cutoff", "TEMP")
            text = text.replace("BC4lean.A.foundation", "BC4lean.A.cutoff").replace("TEMP", "BC4lean.A.foundation")
            path.write_text(text)
            with self.assertRaisesRegex(ValueError, "statement declaration links differ"):
                self.validate(output, tex, evidence)

    def test_moved_proof_cannot_hide_behind_unchanged_total_proof_count(self):
        with self.fixture() as (_, output, tex, evidence):
            path = output / "ch-assembly-map.html"
            text = path.read_text().replace(proof_wrapper(), '')
            text = text.replace(f'<div class="definition_thmwrapper theorem-style-definition" id="def:assembly-map">',
                                proof_wrapper() + f'<div class="definition_thmwrapper theorem-style-definition" id="def:assembly-map">')
            path.write_text(text)
            with self.assertRaisesRegex(ValueError, "proofs belong to different statements"):
                self.validate(output, tex, evidence)

    def test_stale_rendered_statement_wrapper_and_forged_audit_completeness_are_rejected(self):
        with self.fixture() as (_, output, tex, evidence):
            path = output / "ch-assembly-map.html"
            path.write_text(path.read_text() + '<div class="definition_thmwrapper" id="def:stale"></div>')
            with self.assertRaisesRegex(ValueError, "stale, missing, or duplicate"):
                self.validate(output, tex, evidence)
        for key, value in (("chapter_complete", True), ("notready_targets", []), ("blueprint_links", [])):
            with self.subTest(key=key), self.fixture() as (_, output, tex, evidence):
                forged = deepcopy(evidence)
                forged[key] = value
                with self.assertRaisesRegex(ValueError, "declaration/pending/completeness inventory"):
                    self.validate(output, tex, forged)

    def check_site(self, root, evidence):
        locations = {name: ("BC4lean/A.lean", 1) for name in evidence["blueprint_links"]}
        with patch.object(check, "check_site", return_value={"pages": {}}) as historical, \
                patch.object(check, "load_locations", return_value=(locations, "b" * 64)), \
                patch.object(check, "verify_html"), \
                patch.object(check, "load_audit", return_value=(evidence, "b" * 64)):
            result = check.check_chapter7_site(root / "site", REVISION)
            historical.assert_called_once_with(root / "site", REVISION)
            return result

    def test_site_manifest_records_mixed_status_after_unchanged_historical_checks(self):
        with self.fixture() as (root, _, _, evidence):
            manifest = self.check_site(root, evidence)
            self.assertEqual(manifest["chapter7_mathematical_source_revision"], REVISION)
            self.assertFalse(manifest["chapter7"]["chapter_complete"])
            self.assertEqual(sum(manifest["chapter7"]["original_targets"].values()), 1)
            self.assertIn("blueprint/ch-assembly-map.html", manifest["pages"])
            self.assertIn("blueprint/dep_graph_chapter_7.html", manifest["pages"])

    def test_source_link_wrong_host_path_or_scheme_is_rejected_even_with_correct_fragments(self):
        for destination in ("http://ylsong1024.github.io/BC4lean/docs/find/",
                            "https://example.org/BC4lean/docs/find/",
                            "https://ylsong1024.github.io/BC4lean/docs/find-old/"):
            with self.subTest(destination=destination), self.fixture() as (root, output, _, evidence):
                self.mutate(output, GRAPHS[1], SOURCE_BASE, destination)
                with self.assertRaisesRegex(ValueError, "source-link destination"):
                    self.check_site(root, evidence)

    def test_homepage_cannot_hide_false_completion_behind_correct_incomplete_sentence(self):
        for text in ("Chapter 7 is verified.", "Chapter 7 is fully complete.", "Status omitted."):
            with self.subTest(text=text), self.fixture() as (root, _, _, evidence):
                homepage = root / "site/index.html"
                if text == "Status omitted.":
                    homepage.write_text(text)
                else:
                    homepage.write_text(homepage.read_text() + f"<p>{text}</p>")
                with self.assertRaisesRegex(ValueError, "milestone/incomplete status"):
                    self.check_site(root, evidence)


if __name__ == "__main__":
    unittest.main()
