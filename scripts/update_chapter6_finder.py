#!/usr/bin/env python3
"""Maintain exact Chapter 6 declaration anchors and immutable source links.

The retained kernel audit supplies declaration origins and source hashes. Run
this script after that audit, using --source-revision for the audited source
commit, then use --check as a publication preflight. No Lean process runs here.
The generated block follows Chapter 5's block so both generators stay stable.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import html
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import subprocess
from urllib.parse import quote

from audit_chapter6 import ALLOWED_AXIOMS, TARGETS, audit_blueprint, load_inventory
from update_chapter5_finder import BLOCK as CHAPTER5_BLOCK, code_only, declaration_lines

ROOT = Path(__file__).resolve().parents[1]
FINDER = ROOT / "home_page/docs/find/index.html"
AUDIT = ROOT / "docs/audits/chapter6/audit.json"
INVENTORY = ROOT / "docs/audits/chapter6/inventory.json"
BLUEPRINT = ROOT / "blueprint/src/parts/06-topological-k-homology.tex"
SOURCE_URL = "https://github.com/ylsong1024/BC4lean/blob/"
BEGIN = "<!-- BEGIN GENERATED CHAPTER 6 SOURCE INDEX -->"
END = "<!-- END GENERATED CHAPTER 6 SOURCE INDEX -->"
BLOCK = re.compile(re.escape(BEGIN) + r".*?" + re.escape(END) + r"\n?", re.S)


def git(*args: str) -> str:
    return subprocess.run(["git", *args], cwd=ROOT, check=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          text=True).stdout.strip()


def load_audit(revision: str) -> tuple[dict, str]:
    """Require current, complete kernel evidence before publishing source links."""
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("Expected a full immutable Chapter 6 source commit hash")
    audit_bytes = AUDIT.read_bytes()
    audit = json.loads(audit_bytes)
    if (audit.get("status") != "verified" or audit.get("chapter_complete") is not True
            or audit.get("notready_targets")):
        raise ValueError("Chapter 6 source finder requires a complete verified kernel audit")
    if audit.get("source_revision") != revision or audit.get("module_sources_match_revision") is not True:
        raise ValueError("Chapter 6 audit is not bound to the requested immutable source revision")
    if (audit.get("inputs_unchanged_during_audit") is not True
            or audit.get("kernel_run", {}).get("exit_code") != 0
            or audit.get("cached_strict_build_gate", {}).get("exit_code") != 0
            or audit.get("expected_types_run", {}).get("exit_code") != 0):
        raise ValueError("Chapter 6 audit lacks successful unchanged-input kernel/build evidence")
    links, targets = audit_blueprint(BLUEPRINT.read_text(), load_inventory(INVENTORY))
    if not links or audit.get("blueprint_links") != links:
        raise ValueError("Chapter 6 blueprint links differ from the retained kernel audit")
    if (audit.get("target_inventory") != targets or set(targets) != set(TARGETS)
            or not all(target["ready"] for target in targets.values())):
        raise ValueError("Chapter 6 mathematical endpoints differ from the complete retained audit")
    hashes = audit.get("source_sha256", {})
    fixture = "docs/audits/chapter6/ExpectedTypes.lean"
    expected_types = audit["expected_types_run"]
    if (expected_types.get("fixture") != fixture
            or expected_types.get("source_sha256") != hashes.get(fixture)
            or not re.fullmatch(r"[0-9a-f]{64}", expected_types.get("stdout_stderr_sha256", ""))):
        raise ValueError("Chapter 6 expected-type check is not hash-bound to the audited fixture")
    controls = {str(path.relative_to(ROOT)) for path in (BLUEPRINT, INVENTORY)} | {fixture}
    if not hashes or not controls <= hashes.keys():
        raise ValueError("Chapter 6 audit has no bound blueprint/inventory source hashes")
    for relative, expected in hashes.items():
        path = Path(relative)
        if path.is_absolute() or ".." in path.parts:
            raise ValueError(f"Unexpected audited source path: {relative}")
        if hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != expected:
            raise ValueError(f"Source no longer matches retained Chapter 6 kernel audit: {relative}")
    origins = audit.get("linked_declarations", {})
    if not isinstance(origins, dict) or set(origins) != set(links):
        raise ValueError("Chapter 6 audit lacks exact linked declaration origins")
    for name, record in origins.items():
        if (record.get("name") != name or not isinstance(record.get("axioms"), list)
                or set(record["axioms"]) - ALLOWED_AXIOMS):
            raise ValueError(f"Invalid retained Chapter 6 declaration evidence: {name}")
    return audit, hashlib.sha256(audit_bytes).hexdigest()


def load_locations(revision: str) -> tuple[dict[str, tuple[str, int]], str]:
    audit, audit_hash = load_audit(revision)
    origins = audit["linked_declarations"]
    modules = sorted({record["module"] for record in origins.values()})
    commands, paths = {}, {}
    for module in modules:
        if not re.fullmatch(r"BC4lean(?:\.[A-Za-z0-9_]+)+", module):
            raise ValueError(f"Unexpected audited Chapter 6 source module: {module}")
        path = module.replace(".", "/") + ".lean"
        source = (ROOT / path).read_bytes()
        if hashlib.sha256(source).hexdigest() != audit["source_sha256"].get(path):
            raise ValueError(f"Linked source is absent from Chapter 6 audit hashes: {path}")
        # Reuse the Chapter 5 locator, including its nested-comment/string filter.
        # Kernel origins choose the file; exact source commands choose the line.
        commands[module] = declaration_lines(code_only(source.decode("utf-8")))
        paths[module] = path
    committed = set(git("ls-tree", "-r", "--name-only", revision, "--", *paths.values()).splitlines())
    missing = sorted(set(paths.values()) - committed)
    if missing:
        raise ValueError(f"Chapter 6 source absent from pinned GitHub revision: {missing}")
    changed = git("diff", "--name-only", "--no-ext-diff", revision, "--", *paths.values())
    if changed:
        raise ValueError(f"Chapter 6 source differs from pinned GitHub revision:\n{changed}")
    locations = {}
    for name in audit["blueprint_links"]:
        module = origins[name]["module"]
        if name not in commands[module]:
            raise ValueError(f"No exact declaration command for {name} in {paths[module]}")
        locations[name] = (paths[module], commands[module][name])
    return locations, audit_hash


def source_link(name: str, location: tuple[str, int], revision: str) -> str:
    path, line = location
    href = f"{SOURCE_URL}{revision}/{quote(path)}#L{line}"
    return (f'<a class="chapter6-source" data-chapter6-declaration="{html.escape(name)}" '
            f'href="{href}">{html.escape(path)}:{line}</a>')


def render(base: str, locations: dict[str, tuple[str, int]], revision: str, audit_hash: str) -> str:
    existing = set(re.findall(r'\bid="doc/([^"]+)"', base))
    rows = []
    for name, location in locations.items():
        escaped = html.escape(name)
        anchor = "" if name in existing else f' id="doc/{escaped}"'
        rows.append(f'<tr{anchor}><td><a href="#doc/{escaped}"><code>{escaped}</code></a></td>'
                    f'<td>{source_link(name, location, revision)}</td></tr>')
    block = "\n".join([
        BEGIN,
        '<style>#chapter6-source-index table{border-collapse:collapse;width:100%}'
        '#chapter6-source-index td,#chapter6-source-index th{padding:8px;text-align:left;'
        'vertical-align:top;border-bottom:1px solid #dce1e8}'
        '#chapter6-source-index tr:target{background:#ffedab;scroll-margin-top:30px}'
        '#chapter6-source-index td:last-child{overflow-wrap:anywhere}</style>',
        f'<section id="chapter6-source-index" data-chapter6-source-revision="{revision}" '
        f'data-chapter6-audit-sha256="{audit_hash}">',
        '<h2>Chapter 6: Audited declaration source index</h2>',
        f'<p>All {len(locations)} Lean declaration links in the Chapter 6 blueprint. '
        'Declaration modules come from the complete retained kernel audit. Source links '
        'point to exact declaration lines at commit '
        f'<a href="https://github.com/ylsong1024/BC4lean/commit/{revision}">'
        f'<code>{revision[:12]}</code></a>, whose files match the audited SHA-256 hashes.</p>',
        '<table><thead><tr><th scope="col">Lean declaration</th><th scope="col">GitHub source</th>'
        '</tr></thead><tbody>',
        *rows,
        '</tbody></table></section>',
        END,
        "",
    ])
    chapters = list(CHAPTER5_BLOCK.finditer(base))
    if len(chapters) != 1:
        raise ValueError("Expected one existing Chapter 5 source index before Chapter 6")
    insertion = chapters[0].end()
    return base[:insertion] + block + base[insertion:]


class FinderParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.ids: Counter[str] = Counter()
        self.sources: dict[str, list[str]] = {}
        self.revisions: list[str] = []
        self.audit_hashes: list[str] = []

    def handle_starttag(self, tag: str, attributes: list[tuple[str, str | None]]) -> None:
        attrs = dict(attributes)
        if identifier := attrs.get("id"):
            self.ids[identifier] += 1
        if attrs.get("id") == "chapter6-source-index":
            self.revisions.append(attrs.get("data-chapter6-source-revision", ""))
            self.audit_hashes.append(attrs.get("data-chapter6-audit-sha256", ""))
        if tag == "a" and (name := attrs.get("data-chapter6-declaration")):
            self.sources.setdefault(name, []).append(attrs.get("href", ""))


def verify_html(text: str, locations: dict[str, tuple[str, int]], revision: str,
                audit_hash: str) -> None:
    parsed = FinderParser()
    parsed.feed(text)
    if parsed.revisions != [revision] or parsed.audit_hashes != [audit_hash]:
        raise ValueError("Chapter 6 finder revision or retained audit hash differs")
    if set(parsed.sources) != set(locations):
        raise ValueError("Chapter 6 finder source-link inventory differs from audited blueprint links")
    for name, (path, line) in locations.items():
        if parsed.ids[f"doc/{name}"] != 1:
            raise ValueError(f"Expected one canonical Chapter 6 declaration fragment: {name}")
        expected = f"{SOURCE_URL}{revision}/{quote(path)}#L{line}"
        if parsed.sources[name] != [expected]:
            raise ValueError(f"Incorrect or duplicate Chapter 6 source file/line link: {name}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Check without changing files.")
    parser.add_argument("--source-revision", help="Immutable source commit recorded by the Chapter 6 audit.")
    args = parser.parse_args()
    current = FINDER.read_text()
    pinned = re.search(r'data-chapter6-source-revision="([0-9a-f]{40})"', current)
    recorded = json.loads(AUDIT.read_bytes()).get("source_revision")
    revision = git("rev-parse", "--verify",
                   f'{args.source_revision or (pinned[1] if pinned else recorded) or "HEAD"}^{{commit}}')
    base = BLOCK.sub("", current)
    locations, audit_hash = load_locations(revision)
    expected = render(base, locations, revision, audit_hash)
    verify_html(expected, locations, revision, audit_hash)
    if args.check:
        verify_html(current, locations, revision, audit_hash)
        if current != expected:
            raise ValueError("Chapter 6 finder is stale; run scripts/update_chapter6_finder.py")
    else:
        FINDER.write_text(expected)
    print(f'{"Checked" if args.check else "Updated"} {len(locations)} Chapter 6 declaration '
          f'anchors and source file/line links at {revision[:12]}.')


if __name__ == "__main__":
    main()
