"""Build chapter pages and graphs, plus the overall dependency graph."""

from pathlib import Path
from collections import Counter
from html.parser import HTMLParser
import hashlib
import json
import re
import runpy
import shutil
import subprocess
import sys
import tempfile
from urllib.parse import unquote, urlsplit


CHAPTER5 = "blueprint/src/parts/05-equivariant-kk.tex"
EXISTING_PROOFS = frozenset({
    "prop:module-inner-separation",
    "prop:module-action-bound",
    "prop:adjointable-module-map-laws",
    "prop:module-rank-one-laws",
    "prop:standard-module-rank-one",
    "prop:adjointable-module-norms",
    "prop:complete-adjointable-algebra",
    "prop:compact-module-ideal",
    "prop:equivariant-compact-conjugation",
    "prop:standard-module-compact-algebra",
    "prop:standard-identity-cycle",
    "prop:scalar-creation-map-caution",
})
RETAINED_PROOFS = frozenset({
    "prop:rectangular-module-compactness",
    "prop:hilbert-module-direct-sum",
    "prop:kasparov-cycle-direct-sum",
    "prop:compact-perturbation-operator-homotopy",
    "prop:continuous-section-hilbert-module",
    "prop:injective-star-hom-positivity",
    "prop:hilbert-module-gram-positivity",
    "prop:hilbert-module-completion",
    "prop:balanced-module-tensor-positivity",
    "prop:nonunital-cstar-hom-range",
    "prop:coefficient-au-on-modules",
    "prop:positive-module-form-quotient",
    "prop:completed-interior-module-tensor",
    "prop:interior-tensor-operators",
    "prop:standard-tensor-essential-range",
    "prop:complex-clifford-one",
    "prop:clifford-coefficient-tensor",
    "prop:cycle-sum-unitaries-and-inverse-rotation",
    "prop:operator-path-as-interval-cycle",
    "prop:interior-tensor-creation",
    "prop:interior-tensor-countable-generation",
    "prop:actual-interior-creation-counterexample",
    "prop:gram-coefficient-quadratic-positivity",
    "prop:arbitrary-hilbert-module-fibres",
    "prop:arbitrary-module-fibre-quotient-norm",
    "prop:compact-au-acts-strongly",
    "prop:arbitrary-interval-cycle-fibres",
    "prop:compact-fibre-epimorphism-and-kernel",
    "prop:cone-hilbert-module",
    "prop:module-separability-countable-generation",
    "prop:matched-module-compact-pullback",
    "prop:full-interval-homotopy-relation",
    "prop:full-homotopy-direct-sums",
    "prop:even-full-homotopy-group",
    "prop:countable-hilbert-module-sum",
    "prop:module-julia-unitary",
    "prop:module-contractive-normalization",
    "prop:module-compact-positive-part",
    "prop:cstar-sequential-internal-au",
    "prop:standard-module-synthesis",
    "prop:standard-module-stabilization",
    "prop:compact-module-coordinate-cutoffs",
    "prop:localized-module-functional-calculus",
    "prop:completed-tensor-unitary-and-sum-compatibility",
    "prop:kasparov-product",
    "prop:kk-k-theory",
})
RETAINED_PROOF_NOTE = r"""
\begin{proof}
\leanok
The linked Lean declarations supply the checked proof. This proof status is
rendered from the retained Chapter 5 kernel evidence; see the
\href{https://github.com/ylsong1024/BC4lean/blob/main/docs/CHAPTER5_VERIFICATION.md}{Chapter 5 verification record}.
\end{proof}
"""


def verified_chapter5_tex(tex, audit, parser):
    r"""Expose retained proof evidence to leanblueprint without changing its source.

    A statement-level ``\leanok`` gives a green border. Proof backgrounds need
    a proof-level marker, absent from these 46 already checked propositions.
    This adapter is deliberately bound to the retained source and inventories;
    it cannot promote a new or changed statement to verified status.
    """
    def require(condition, message):
        if not condition:
            raise RuntimeError(f"Chapter 5 proof-status rendering: {message}")

    require(hashlib.sha256(tex.encode("utf-8")).hexdigest() == audit["source_sha256"][CHAPTER5],
            "source hash differs from the retained kernel audit")
    require(audit["chapter_complete"] is True and audit["notready_targets"] == [],
            "retained chapter is not complete")
    links, pending, targets = parser["audit_blueprint"](tex)
    require(not pending and len(links) == 435 and links == audit["linked_declarations"]
            and targets == audit["required_target_inventory"],
            "blueprint links or target inventory differ from the retained audit")
    require(all(name in audit["linked_declaration_axioms"] for name in links),
            "a linked declaration has no retained kernel evidence")

    blocks = list(re.finditer(
        r"\\begin\{(definition|proposition)\}(.*?)\\end\{\1\}", tex, re.S))
    require(len(blocks) == 75 and sum(m[1] == "definition" for m in blocks) == 17,
            "expected 17 definitions and 58 propositions")
    labels, existing, retained, insertions = set(), set(), set(), []
    for block in blocks:
        body = parser["tex_code_only"](block[2])
        names = re.findall(r"\\label\{([^}]+)\}", body)
        require(len(names) == 1 and names[0] not in labels,
                "expected one unique label per statement")
        label = names[0]
        labels.add(label)
        block_links = {name.strip() for group in re.findall(r"\\lean\{([^}]+)\}", body)
                       for name in group.split(",") if name.strip()}
        require(re.search(r"\\leanok\b", body) and not re.search(r"\\notready\b", body)
                and block_links and block_links <= set(links),
                f"statement {label} lacks ready markers or audited links")
        if block[1] == "definition":
            continue
        following = parser["tex_code_only"](tex[block.end():]).lstrip()
        if following.startswith(r"\begin{proof}"):
            proof = re.match(r"\\begin\{proof\}(.*?)\\end\{proof\}", following, re.S)
            require(proof is not None and re.search(r"\\leanok\b", proof[1]),
                    f"existing proof for {label} is not marked checked")
            existing.add(label)
        else:
            retained.add(label)
            insertions.append(block.end())
    require(existing == EXISTING_PROOFS and retained == RETAINED_PROOFS,
            "the exact existing/retained proof-label inventories changed")
    require(len(re.findall(r"\\begin\{proof\}", parser["tex_code_only"](tex))) == 12,
            "unexpected proof environment outside the existing inventory")
    rendered = tex
    for position in reversed(insertions):
        rendered = rendered[:position] + RETAINED_PROOF_NOTE + rendered[position:]
    require(parser["audit_blueprint"](rendered) == (links, pending, targets),
            "rendering changed mathematical statements or declaration links")
    return rendered


def build_documents(source, output, command, chapter5_tex):
    # Both renders run from this copy; even plasTeX's auxiliary files stay out
    # of the checked-in source directory and its frozen Chapter 5 snapshot.
    with tempfile.TemporaryDirectory(prefix="blueprint-render-") as directory:
        temporary = Path(directory)
        render_source = temporary / "src"
        shutil.copytree(source, render_source)
        (render_source / "parts/05-equivariant-kk.tex").write_text(chapter5_tex, encoding="utf-8")
        subprocess.run([*command, "--dir", str(output), "web.tex"],
                       cwd=render_source, check=True)

        # Keep chapter navigation/graphs above, and add one overall graph.
        macros = render_source / "macros" / "web.tex"
        contents = macros.read_text(encoding="utf-8")
        option = "dep_by=chapter,"
        if contents.count(option) != 1:
            raise RuntimeError("Expected one dep_by=chapter option in macros/web.tex")
        macros.write_text(contents.replace(option, ""), encoding="utf-8")
        overall_output = temporary / "web"
        subprocess.run(
            [*command, "--dir", str(overall_output), "web.tex"],
            cwd=render_source,
            check=True,
        )
        shutil.copy2(overall_output / "dep_graph_document.html", output)


class _Chapter5HTML(HTMLParser):
    """Read declaration links inside each graph modal without matching HTML text."""

    def __init__(self, labels):
        super().__init__()
        self.labels = labels
        self.statement_ids = Counter()
        self.modal_counts = Counter()
        self.modal_links = {label: set() for label in labels}
        self.links = set()
        self.proof_count = 0
        self.modal = None
        self.depth = 0

    def handle_starttag(self, tag, attributes):
        attrs = dict(attributes)
        classes = set(attrs.get("class", "").split())
        identity = attrs.get("id", "")
        if identity in self.labels:
            self.statement_ids[identity] += 1
        if tag == "div":
            if self.modal is not None:
                self.depth += 1
            elif "dep-modal-container" in classes and identity.removesuffix("_modal") in self.labels:
                self.modal = identity.removesuffix("_modal")
                self.modal_counts[self.modal] += 1
                self.depth = 1
            if "proof_content" in classes:
                self.proof_count += 1
        if tag == "a":
            fragment = unquote(urlsplit(attrs.get("href", "")).fragment)
            if fragment.startswith("doc/"):
                declaration = fragment.removeprefix("doc/")
                self.links.add(declaration)
                if self.modal is not None:
                    self.modal_links[self.modal].add(declaration)

    def handle_endtag(self, tag):
        if tag == "div" and self.modal is not None:
            self.depth -= 1
            if self.depth == 0:
                self.modal = None


def validate_rendered_chapter5(output, original_tex, parser):
    """Validate built or assembled blueprint HTML; return its checked counts.

    ``parser`` is the dictionary returned by runpy.run_path on the retained
    scripts/audit_chapter5.py. No renderer or Lean process runs in this check.
    """
    def require(condition, message):
        if not condition:
            raise RuntimeError(f"Chapter 5 rendered status: {message}")

    links, pending, targets = parser["audit_blueprint"](original_tex)
    blocks = re.findall(r"\\begin\{(definition|proposition)\}(.*?)\\end\{\1\}",
                        parser["tex_code_only"](original_tex), re.S)
    expected = {}
    for kind, body in blocks:
        labels = re.findall(r"\\label\{([^}]+)\}", body)
        require(len(labels) == 1 and labels[0] not in expected, "ambiguous source statement labels")
        expected[labels[0]] = (kind, {name.strip() for group in re.findall(r"\\lean\{([^}]+)\}", body)
                                    for name in group.split(",") if name.strip()})
    require(not pending and len(links) == 435 and len(expected) == 75
            and sum(kind == "definition" for kind, _ in expected.values()) == 17,
            "expected the complete 75-statement/435-link source inventory")
    labels = set(expected)
    checked_graphs = {}
    for filename in ("dep_graph_chapter_5.html", "dep_graph_document.html"):
        html = (Path(output) / filename).read_text(encoding="utf-8")
        dots = re.findall(r"\.renderDot\(\s*`(.*?)`\s*\)", html, re.S)
        require(len(dots) == 1, f"{filename}: expected one embedded DOT graph")
        nodes = {}
        for label, attributes in re.findall(r'"([^"\n]+)"\s*\[([^\[\]]*)\];', dots[0], re.S):
            attrs = dict(re.findall(r'(\w+)\s*=\s*("[^"\n]*"|[^,\s;\]]+)', attributes))
            if "label" not in attrs:
                continue
            require(label not in nodes, f"{filename}: duplicate node {label}")
            nodes[label] = attrs
        require(labels <= nodes.keys(), f"{filename}: Chapter 5 graph nodes are missing")
        if filename == "dep_graph_chapter_5.html":
            require(set(nodes) == labels, f"{filename}: unexpected chapter nodes")
        document = _Chapter5HTML(labels)
        document.feed(html)
        for label, (kind, declarations) in expected.items():
            attrs = nodes[label]
            require(attrs.get("color") == "green"
                    and attrs.get("fillcolor") in {'"#B0ECA3"', '"#1CAC78"'},
                    f"{filename}: {label} lacks verified statement/proof colors")
            require("filled" in {style.strip() for style in attrs.get("style", "").strip('"').split(",")},
                    f"{filename}: {label} lacks filled style")
            require(attrs.get("shape") == ("box" if kind == "definition" else "ellipse"),
                    f"{filename}: {label} has the wrong statement shape")
            require(document.modal_counts[label] == 1
                    and document.modal_links[label] == declarations,
                    f"{filename}: {label} declaration links differ from source")
        checked_graphs[filename] = {"chapter5_nodes": len(labels), "verified_fills": len(labels),
                                    "lean_links": len(set().union(*document.modal_links.values()))}
    html = (Path(output) / "ch-equivariant-kk.html").read_text(encoding="utf-8")
    chapter = _Chapter5HTML(labels)
    chapter.feed(html)
    require(all(chapter.statement_ids[label] == 1 for label in labels)
            and chapter.links == set(links), "chapter page statement anchors or declaration links differ")
    require(chapter.proof_count == 58
            and html.count("rendered from the retained Chapter 5 kernel evidence") == 46,
            "chapter page lacks its 58 proofs or 46 retained-evidence explanations")
    return {"statements": len(labels), "definitions": 17, "propositions": 58,
            "lean_links": len(links),
            "required_endpoints": {label: len(target["required_declarations"])
                                   for label, target in targets.items()},
            "graphs": checked_graphs}


def main():
    source = Path(__file__).resolve().parent
    root = source.parents[1]
    checks = runpy.run_path(str(root / "scripts/check_project_imports.py"))
    errors = checks["check_chapter5_core_evidence"](root)
    if errors:
        raise RuntimeError("\n".join(errors))
    audit = json.loads((root / "docs/audits/chapter5/core-audit.json").read_text(encoding="utf-8"))
    parser = runpy.run_path(str(root / "scripts/audit_chapter5.py"))
    chapter5 = (root / CHAPTER5).read_bytes().decode("utf-8")
    rendered_chapter5 = verified_chapter5_tex(chapter5, audit, parser)
    plastex = Path(sys.executable).with_name("plastex")
    build_documents(source, source.parent / "web", [str(plastex), "-c", "plastex.cfg"],
                    rendered_chapter5)
    counts = validate_rendered_chapter5(source.parent / "web", chapter5, parser)
    print(f"Chapter 5 rendered status checked: {counts['statements']} statements, "
          f"{counts['lean_links']} Lean links, verified fills in both graphs.")


if __name__ == "__main__":
    main()
