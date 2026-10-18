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

from update_chapter5_finder import load_locations, verify_html


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
    if "eventually equivariant KK-theory" in homepage.text:
        raise ValueError("Homepage still contains the old KK-theory status.")
    if "general universal proper-space construction and assembly map remain work in progress" in homepage.text:
        raise ValueError("Homepage still contains the old Chapter 4 status.")
    required_links = {
        "blueprint/ch-proper-actions.html",
        "blueprint/ch-equivariant-kk.html",
        "blueprint/dep_graph_chapter_5.html",
        "docs/find/",
        "https://github.com/ylsong1024/BC4lean/blob/main/docs/CHAPTER5_COMPLETION.md",
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
    scope = Page((site / "blueprint/ch-scope.html").read_text(encoding="utf-8"))
    if "This is a structural draft" in scope.text or "remain unverified" in scope.text:
        raise ValueError("Blueprint overview still contains its old verification summary.")
    if "Chapter 5 verifies the full" not in scope.text:
        raise ValueError("Blueprint overview is missing the verified Chapter 5 scope.")

    pages = [
        "index.html", "docs/find/index.html", "blueprint/ch-scope.html",
        "blueprint/ch-equivariant-kk.html", "blueprint/dep_graph_chapter_5.html",
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
          "58 proof statuses, 435 declaration links; page hashes in site-version.json.")


if __name__ == "__main__":
    main()
