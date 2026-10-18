#!/usr/bin/env python3
"""Validate the assembled Pages content and record its revision and page hashes."""

import argparse
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import runpy
import subprocess
from urllib.parse import unquote, urlsplit

from audit_chapter6 import TARGETS, tex_code_only
from update_chapter5_finder import load_locations, verify_html
from update_chapter6_finder import load_audit as load_chapter6_audit
from update_chapter6_finder import load_locations as load_chapter6_locations
from update_chapter6_finder import verify_html as verify_chapter6_html


ROOT = Path(__file__).resolve().parents[1]


class Page(HTMLParser):
    def __init__(self, text):
        super().__init__()
        self.identifiers = set()
        self.links = []
        self.words = []
        self.hidden = 0
        self.feed(text)

    def handle_starttag(self, tag, attributes):
        attrs = dict(attributes)
        if tag in {"script", "style"}:
            self.hidden += 1
        if attrs.get("id"):
            self.identifiers.add(attrs["id"])
        if tag == "a" and attrs.get("href"):
            self.links.append(attrs["href"])

    def handle_endtag(self, tag):
        if tag in {"script", "style"}:
            self.hidden -= 1

    def handle_data(self, data):
        if not self.hidden:
            self.words.append(data)

    @property
    def text(self):
        return " ".join(" ".join(self.words).split())


def validate_rendered_chapter6(output, original_tex, audit, build):
    """Check real source readiness markers and both generated Chapter 6 graphs.

    Chapter 6 supplies its proof-level markers in the blueprint itself. This
    check never inserts markers or changes the renderer's source.
    """
    def require(condition, message):
        if not condition:
            raise ValueError(f"Chapter 6 rendered status: {message}")

    tex = tex_code_only(original_tex)
    blocks = list(re.finditer(
        r"\\begin\{(definition|proposition|theorem|lemma)\}(.*?)\\end\{\1\}", tex, re.S))
    expected, proof_count = {}, 0
    for block in blocks:
        kind, body = block[1], block[2]
        labels = re.findall(r"\\label\{([^}]+)\}", body)
        require(len(labels) == 1 and labels[0] not in expected,
                "expected one unique source label per statement")
        label = labels[0]
        declarations = {name.strip() for group in re.findall(r"\\lean\{([^}]+)\}", body)
                        for name in group.split(",") if name.strip()}
        require(re.search(r"\\leanok\b", body) and not re.search(r"\\notready\b", body)
                and declarations, f"{label} lacks ready markers or declaration links")
        following = tex[block.end():].lstrip()
        proof = re.match(r"\\begin\{proof\}(.*?)\\end\{proof\}", following, re.S)
        require(kind == "definition" or proof is not None,
                f"{label} lacks an explicit checked proof in blueprint source")
        if proof:
            require(re.search(r"\\leanok\b", proof[1])
                    and not re.search(r"\\notready\b", proof[1]),
                    f"{label} proof is not explicitly marked checked in blueprint source")
            proof_count += 1
        expected[label] = (kind, declarations)
    require(set(TARGETS) <= set(expected), "an original Chapter 6 mathematical target is missing")
    require(proof_count == len(re.findall(r"\\begin\{proof\}", tex)),
            "unexpected proof environment outside the source statement inventory")
    require(not re.search(r"\\notready\b", tex), "source still contains an unready Chapter 6 target")
    links = set(audit["blueprint_links"])
    require(set().union(*(declarations for _, declarations in expected.values())) == links,
            "source statement declarations differ from retained kernel links")
    for label in TARGETS:
        require(expected[label][1] == set(audit["target_inventory"][label]["linked_declarations"])
                and audit["target_inventory"][label]["ready"],
                f"{label} differs from its verified mathematical endpoint inventory")

    labels, checked_graphs = set(expected), {}
    for filename in ("dep_graph_chapter_6.html", "dep_graph_document.html"):
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
        require(labels <= nodes.keys(), f"{filename}: Chapter 6 graph nodes are missing")
        if filename == "dep_graph_chapter_6.html":
            require(set(nodes) == labels, f"{filename}: unexpected chapter nodes")
        document = build["_Chapter5HTML"](labels)
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
            require(document.modal_counts[label] == 1 and document.modal_links[label] == declarations,
                    f"{filename}: {label} declaration links differ from source")
        checked_graphs[filename] = {"chapter6_nodes": len(labels), "verified_fills": len(labels),
                                    "lean_links": len(set().union(*document.modal_links.values()))}
    chapter = build["_Chapter5HTML"](labels)
    chapter.feed((Path(output) / "ch-topological-k-homology.html").read_text(encoding="utf-8"))
    require(all(chapter.statement_ids[label] == 1 for label in labels) and chapter.links == links,
            "chapter page statement anchors or declaration links differ from source")
    require(chapter.proof_count == proof_count, "chapter page differs from explicit source proof inventory")
    return {"statements": len(labels),
            "definitions": sum(kind == "definition" for kind, _ in expected.values()),
            "propositions": sum(kind != "definition" for kind, _ in expected.values()),
            "proofs": proof_count, "lean_links": len(links), "graphs": checked_graphs}


def check_site(site, revision):
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("Expected the full deployed Git revision.")
    head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, check=True,
                          capture_output=True, text=True).stdout.strip()
    dirty = subprocess.run(["git", "status", "--porcelain=v1", "--untracked-files=no"],
                           cwd=ROOT, check=True, capture_output=True, text=True).stdout
    if head != revision or dirty:
        raise ValueError("Website revision must match the clean checked-out commit.")
    site = site.resolve(strict=True)
    homepage = Page((site / "index.html").read_text(encoding="utf-8"))
    if "Chapter 5 is verified." not in homepage.text:
        raise ValueError("Homepage does not report Chapter 5 completion.")
    if "Chapter 6 is verified." not in homepage.text:
        raise ValueError("Homepage does not report Chapter 6 completion.")
    if "eventually equivariant KK-theory" in homepage.text:
        raise ValueError("Homepage still contains the old KK-theory status.")
    if "general universal proper-space construction and assembly map remain work in progress" in homepage.text:
        raise ValueError("Homepage still contains the old Chapter 4 status.")
    if ("topological-side and assembly constructions remain later milestones" in homepage.text
            or "6–7 — Topological side and assembly map" in homepage.text):
        raise ValueError("Homepage still contains the old Chapter 6 status.")
    required_links = {
        "blueprint/ch-proper-actions.html",
        "blueprint/ch-equivariant-kk.html",
        "blueprint/dep_graph_chapter_5.html",
        "blueprint/ch-topological-k-homology.html",
        "blueprint/dep_graph_chapter_6.html",
        "docs/find/",
        "https://github.com/ylsong1024/BC4lean/blob/main/docs/CHAPTER5_COMPLETION.md",
        "https://github.com/ylsong1024/BC4lean/blob/main/docs/CHAPTER6_COMPLETION.md",
    }
    if not required_links.issubset(homepage.links):
        raise ValueError("Homepage is missing verification or source navigation.")
    for href in homepage.links:
        link = urlsplit(href)
        if link.scheme or link.netloc:
            continue
        target = site / unquote(link.path)
        if target.is_dir():
            target /= "index.html"
        if not target.resolve().is_relative_to(site) or not target.is_file():
            raise ValueError(f"Broken local homepage link: {href}")
        if link.fragment:
            page = Page(target.read_text(encoding="utf-8"))
            if unquote(link.fragment) not in page.identifiers:
                raise ValueError(f"Broken homepage fragment: {href}")

    checks = runpy.run_path(str(ROOT / "scripts/check_project_imports.py"))
    errors = checks["check_chapter5_core_evidence"](ROOT)
    if errors:
        raise ValueError("\n".join(errors))
    build = runpy.run_path(str(ROOT / "blueprint/src/build_web.py"))
    parser = runpy.run_path(str(ROOT / "scripts/audit_chapter5.py"))
    original_tex = (ROOT / "blueprint/src/parts/05-equivariant-kk.tex").read_text(encoding="utf-8")
    build["validate_rendered_chapter5"](site / "blueprint", original_tex, parser)

    finder = (site / "docs/find/index.html").read_text(encoding="utf-8")
    pinned = re.search(r'data-source-revision="([0-9a-f]{40})"', finder)
    if not pinned:
        raise ValueError("Published source finder has no immutable source revision.")
    locations, audit_hash = load_locations(pinned[1])
    verify_html(finder, locations, pinned[1])
    for relative in ["ch-equivariant-kk.html", "dep_graph_chapter_5.html", "dep_graph_document.html"]:
        page = Page((site / "blueprint" / relative).read_text(encoding="utf-8"))
        seen = set()
        for href in page.links:
            target = urlsplit(href)
            fragment = unquote(target.fragment)
            if not fragment.startswith("doc/") or fragment[4:] not in locations:
                continue
            if (target.scheme, target.netloc, target.path) != (
                    "https", "ylsong1024.github.io", "/BC4lean/docs/find/"):
                raise ValueError(f"Incorrect Chapter 5 source-link destination: {href}")
            seen.add(fragment[4:])
        if seen != set(locations):
            raise ValueError(f"Incomplete Chapter 5 source-link inventory in {relative}.")
    chapter6_pin = re.search(r'data-chapter6-source-revision="([0-9a-f]{40})"', finder)
    if not chapter6_pin:
        raise ValueError("Published Chapter 6 source finder has no immutable source revision.")
    chapter6_locations, chapter6_audit_hash = load_chapter6_locations(chapter6_pin[1])
    verify_chapter6_html(finder, chapter6_locations, chapter6_pin[1], chapter6_audit_hash)
    chapter6_audit, _ = load_chapter6_audit(chapter6_pin[1])
    chapter6_tex = (ROOT / "blueprint/src/parts/06-topological-k-homology.tex").read_text(encoding="utf-8")
    chapter6_counts = validate_rendered_chapter6(site / "blueprint", chapter6_tex, chapter6_audit, build)
    for relative in ["ch-topological-k-homology.html", "dep_graph_chapter_6.html", "dep_graph_document.html"]:
        page = Page((site / "blueprint" / relative).read_text(encoding="utf-8"))
        seen = set()
        for href in page.links:
            target = urlsplit(href)
            fragment = unquote(target.fragment)
            if not fragment.startswith("doc/") or fragment[4:] not in chapter6_locations:
                continue
            if (target.scheme, target.netloc, target.path) != (
                    "https", "ylsong1024.github.io", "/BC4lean/docs/find/"):
                raise ValueError(f"Incorrect Chapter 6 source-link destination: {href}")
            seen.add(fragment[4:])
        if seen != set(chapter6_locations):
            raise ValueError(f"Incomplete Chapter 6 source-link inventory in {relative}.")
    scope = Page((site / "blueprint/ch-scope.html").read_text(encoding="utf-8"))
    if "This is a structural draft" in scope.text or "remain unverified" in scope.text:
        raise ValueError("Blueprint overview still contains its old verification summary.")
    if "Chapter 5 verifies the full" not in scope.text:
        raise ValueError("Blueprint overview is missing the verified Chapter 5 scope.")
    if "Chapter 6 verifies" not in scope.text:
        raise ValueError("Blueprint overview is missing the verified Chapter 6 scope.")
    if "topological-side and assembly constructions remain later milestones" in scope.text:
        raise ValueError("Blueprint overview still contains the old Chapter 6 status.")

    pages = [
        "index.html", "docs/find/index.html", "blueprint/ch-scope.html",
        "blueprint/ch-equivariant-kk.html", "blueprint/dep_graph_chapter_5.html",
        "blueprint/ch-topological-k-homology.html", "blueprint/dep_graph_chapter_6.html",
        "blueprint/dep_graph_document.html", "blueprint/ch-conjecture-and-examples.html",
    ]
    hashes = {}
    for relative in pages:
        contents = (site / relative).read_bytes()
        hashes[relative] = {"sha256": hashlib.sha256(contents).hexdigest(), "bytes": len(contents)}
    return {
        "schema": "BC4lean.published-website.v1",
        "revision": revision,
        "mathematical_source_revision": pinned[1],
        "chapter5_core_audit_sha256": audit_hash,
        "chapter5_blocks": 75,
        "chapter5_propositions_with_verified_proof_status": 58,
        "chapter5_source_links_checked": len(locations),
        "chapter6_mathematical_source_revision": chapter6_pin[1],
        "chapter6_core_audit_sha256": chapter6_audit_hash,
        "chapter6_blocks": chapter6_counts["statements"],
        "chapter6_propositions_with_verified_proof_status": chapter6_counts["propositions"],
        "chapter6_source_links_checked": len(chapter6_locations),
        "chapter6_targets": {label: chapter6_audit["target_inventory"][label]["ready"]
                             for label in TARGETS},
        "homepage_local_links_checked": True,
        "rendered_chapter_and_overall_graph_checked": True,
        "pages": hashes,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("site", type=Path)
    parser.add_argument("--revision", required=True)
    args = parser.parse_args()
    manifest = check_site(args.site, args.revision)
    (args.site / "site-version.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(f"Verified assembled website: revision {args.revision}; 75 Chapter 5 nodes, "
          "58 proof statuses, 435 declaration links; "
          f'{manifest["chapter6_blocks"]} Chapter 6 nodes, '
          f'{manifest["chapter6_source_links_checked"]} declaration links; '
          "page hashes in site-version.json.")


if __name__ == "__main__":
    main()
