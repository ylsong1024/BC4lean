#!/usr/bin/env python3
"""Maintain exact Chapter 7 declaration anchors and immutable source links.

The retained kernel audit supplies declaration origins and source hashes. Run
this script after that audit, using --source-revision for the audited source
commit, then use --check as a publication preflight. No Lean process runs here.
The generated block follows Chapter 6's block so the generators stay stable.
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

from audit_chapter7 import (ALLOWED_AXIOMS, TARGETS, audit_blueprint, check_private_coverage,
                           check_scope_coverage, generate_query, load_inventory,
                           parse_kernel_evidence, pending_blueprint_targets)
from update_chapter6_finder import BLOCK as CHAPTER6_BLOCK
from update_chapter5_finder import code_only, declaration_lines

ROOT = Path(__file__).resolve().parents[1]
FINDER = ROOT / "home_page/docs/find/index.html"
AUDIT = ROOT / "docs/audits/chapter7/audit.json"
INVENTORY = ROOT / "docs/audits/chapter7/inventory.json"
BLUEPRINT = ROOT / "blueprint/src/parts/07-assembly-map.tex"
SOURCE_URL = "https://github.com/ylsong1024/BC4lean/blob/"
BEGIN = "<!-- BEGIN GENERATED CHAPTER 7 SOURCE INDEX -->"
END = "<!-- END GENERATED CHAPTER 7 SOURCE INDEX -->"
BLOCK = re.compile(re.escape(BEGIN) + r".*?" + re.escape(END) + r"\n?", re.S)


def git(*args: str) -> str:
    return subprocess.run(["git", *args], cwd=ROOT, check=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          text=True).stdout.strip()


def load_audit(revision: str) -> tuple[dict, str]:
    """Require actual current milestone evidence, preserving pending originals."""
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("Expected a full immutable Chapter 7 source commit hash")
    audit_bytes = AUDIT.read_bytes()
    audit = json.loads(audit_bytes)
    if (audit.get("schema_version") != 1
            or audit.get("status") not in {"verified_milestone", "verified_complete"}
            or audit.get("milestone_verified") is not True):
        raise ValueError("Chapter 7 source finder requires a verified kernel milestone audit")
    if audit.get("source_revision") != revision or audit.get("module_sources_match_revision") is not True:
        raise ValueError("Chapter 7 audit is not bound to the requested immutable source revision")
    if (audit.get("inputs_unchanged_during_audit") is not True
            or audit.get("kernel_run", {}).get("exit_code") != 0
            or audit.get("cached_strict_build_gate", {}).get("exit_code") != 0
            or audit.get("historical_imports_run", {}).get("exit_code") != 0
            or audit.get("expected_types_run", {}).get("exit_code") != 0):
        raise ValueError("Chapter 7 audit lacks successful unchanged-input kernel/build evidence")
    inventory = load_inventory(INVENTORY)
    blueprint = BLUEPRINT.read_text()
    links, targets, milestones = audit_blueprint(blueprint, inventory)
    pending = pending_blueprint_targets(blueprint)
    complete = all(target["ready"] for target in targets.values()) and not pending
    if (audit.get("chapter_complete") is not complete
            or audit.get("status") != ("verified_complete" if complete else "verified_milestone")
            or audit.get("notready_targets") != pending):
        raise ValueError("Chapter 7 audit completeness/pending status contradicts the original blueprint targets")
    if (audit.get("modules") != inventory["modules"]
            or audit.get("source_modules") != sorted(inventory["modules"] + inventory["additional_source_modules"])):
        raise ValueError("Chapter 7 audit census/source module inventory differs")
    if not links or audit.get("blueprint_links") != links:
        raise ValueError("Chapter 7 blueprint links differ from the retained kernel audit")
    if (audit.get("target_inventory") != targets or set(targets) != set(TARGETS)
            or audit.get("milestone_inventory") != milestones
            or not all(milestone["ready"] for milestone in milestones.values())):
        raise ValueError("Chapter 7 mathematical endpoints differ from the retained milestone audit")
    hashes = audit.get("source_sha256", {})
    fixture = "docs/audits/chapter7/ExpectedTypes.lean"
    expected_types = audit["expected_types_run"]
    if (expected_types.get("fixture") != fixture
            or expected_types.get("source_sha256") != hashes.get(fixture)
            or not re.fullmatch(r"[0-9a-f]{64}", expected_types.get("stdout_stderr_sha256", ""))):
        raise ValueError("Chapter 7 expected-type check is not hash-bound to the audited fixture")
    controls = {str(path.relative_to(ROOT)) for path in (BLUEPRINT, INVENTORY)} | {
        fixture, "BC4lean.lean", "docs/audits/chapter7/Chapter6Imports.lean",
        "blueprint/src/parts/08-conjecture-and-examples.tex",
        "scripts/audit_chapter7.py", "scripts/test_audit_chapter7.py",
        "scripts/update_chapter7_finder.py", "scripts/test_chapter7_publication.py",
        "scripts/check_chapter7_website.py", "scripts/test_chapter7_website.py",
        ".github/workflows/chapter7.yml", "lean-toolchain", "lakefile.toml", "lake-manifest.json"}
    controls |= {module.replace(".", "/") + ".lean" for module in audit["source_modules"]}
    if not hashes or not controls <= hashes.keys():
        raise ValueError("Chapter 7 audit has no bound blueprint/inventory source hashes")
    for relative, expected in hashes.items():
        path = Path(relative)
        if path.is_absolute() or ".." in path.parts:
            raise ValueError(f"Unexpected audited source path: {relative}")
        if (not isinstance(expected, str) or not re.fullmatch(r"[0-9a-f]{64}", expected)
                or hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != expected):
            raise ValueError(f"Source no longer matches retained Chapter 7 kernel audit: {relative}")
    check_scope_coverage((ROOT / "BC4lean.lean").read_bytes(),
                         (ROOT / "docs/audits/chapter7/Chapter6Imports.lean").read_bytes(), audit["modules"])
    origins = audit.get("linked_declarations", {})
    if not isinstance(origins, dict) or set(origins) != set(links):
        raise ValueError("Chapter 7 audit lacks exact linked declaration origins")
    for name, record in origins.items():
        if (record.get("name") != name or not isinstance(record.get("axioms"), list)
                or len(record["axioms"]) != len(set(record["axioms"]))
                or set(record["axioms"]) - ALLOWED_AXIOMS):
            raise ValueError(f"Invalid retained Chapter 7 declaration evidence: {name}")
    verify_process_evidence(audit, inventory, links)
    return audit, hashlib.sha256(audit_bytes).hexdigest()


def verify_process_evidence(audit: dict, inventory: dict, links: list[str]) -> None:
    """Reparse retained raw evidence and reject weakened recorded commands."""
    endpoints = sorted({name for item in [*inventory["targets"].values(), *inventory["milestones"].values()]
                        for name in item["required_declarations"]})
    expected_query = generate_query(inventory["modules"], links, endpoints).encode()
    query_hash = hashlib.sha256(expected_query).hexdigest()
    if (audit.get("query_sha256") != query_hash
            or AUDIT.with_suffix(".lean").read_bytes() != expected_query):
        raise ValueError("Retained Chapter 7 query differs from the uncapped inventory-generated census")
    logs = {}
    keys = {"historical-imports": "historical_imports_run", "build-gate": "cached_strict_build_gate",
            "expected-types": "expected_types_run", "kernel": "kernel_run"}
    lean_prefix = ["lake", "env", "lean", "-j1", "-DwarningAsError=true",
                   "-DautoImplicit=false", "-DrelaxedAutoImplicit=false"]
    for suffix, key in keys.items():
        record = json.loads(AUDIT.with_suffix(f".{suffix}-run.json").read_bytes())
        log = AUDIT.with_suffix(f".{suffix}.log").read_bytes()
        if (record != audit.get(key) or record.get("exit_code") != 0
                or record.get("stdout_stderr_sha256") != hashlib.sha256(log).hexdigest()):
            raise ValueError(f"Chapter 7 {suffix} process record/log differs from retained audit")
        command = record.get("command")
        if not isinstance(command, list) or not all(isinstance(arg, str) for arg in command):
            raise ValueError(f"Invalid recorded Chapter 7 {suffix} command")
        if suffix == "build-gate":
            valid = command == ["lake", "--wfail", "--no-build", "--no-cache", "build", "BC4lean"]
        elif suffix == "historical-imports":
            valid = (len(command) == 3 and command[1:] == ["-B", "scripts/check_project_imports.py"]
                     and re.fullmatch(r"python(?:3(?:\.\d+)?)?(?:\.exe)?", Path(command[0]).name))
        else:
            expected_suffix = "docs/audits/chapter7/ExpectedTypes.lean" if suffix == "expected-types" else AUDIT.with_suffix(".lean").name
            valid = (len(command) == len(lean_prefix) + 1 and command[:-1] == lean_prefix
                     and (command[-1] == expected_suffix or command[-1].endswith("/" + expected_suffix)))
            if suffix == "kernel":
                valid = valid and record.get("query_sha256") == query_hash
        if not valid:
            raise ValueError(f"Recorded Chapter 7 {suffix} command is not the strict audited command")
        logs[suffix] = log
    parsed = parse_kernel_evidence(logs["kernel"].decode(), inventory["modules"], links, endpoints)
    if any(audit.get(key) != value for key, value in parsed.items()):
        raise ValueError("Chapter 7 raw kernel census disagrees with retained declaration/axiom evidence")
    sources = {module: (ROOT / (module.replace(".", "/") + ".lean")).read_text()
               for module in inventory["modules"]}
    if audit.get("private_declaration_counts") != check_private_coverage(sources, parsed["declarations"]):
        raise ValueError("Chapter 7 private declaration coverage differs from source/kernel evidence")
    objects = audit.get("module_olean_sha256")
    required_objects = {".lake/build/lib/lean/" + module.replace(".", "/") + ".olean"
                        for module in audit["source_modules"]}
    if (not isinstance(objects, dict) or not required_objects <= objects.keys()
            or any(path not in required_objects and path.removesuffix(".private") not in required_objects
                   for path in objects)
            or any(not isinstance(sha, str) or not re.fullmatch(r"[0-9a-f]{64}", sha) for sha in objects.values())):
        raise ValueError("Chapter 7 audit lacks exact hash-bound compiled objects")


def load_locations(revision: str) -> tuple[dict[str, tuple[str, int]], str]:
    audit, audit_hash = load_audit(revision)
    origins = audit["linked_declarations"]
    modules = sorted({record["module"] for record in origins.values()})
    commands, paths = {}, {}
    for module in modules:
        if not re.fullmatch(r"BC4lean(?:\.[A-Za-z0-9_]+)+", module):
            raise ValueError(f"Unexpected audited Chapter 7 source module: {module}")
        path = module.replace(".", "/") + ".lean"
        source = (ROOT / path).read_bytes()
        if hashlib.sha256(source).hexdigest() != audit["source_sha256"].get(path):
            raise ValueError(f"Linked source is absent from Chapter 7 audit hashes: {path}")
        # Reuse the Chapter 5 locator, including its nested-comment/string filter.
        # Kernel origins choose the file; exact source commands choose the line.
        commands[module] = declaration_lines(code_only(source.decode("utf-8")))
        paths[module] = path
    committed = set(git("ls-tree", "-r", "--name-only", revision, "--", *paths.values()).splitlines())
    missing = sorted(set(paths.values()) - committed)
    if missing:
        raise ValueError(f"Chapter 7 source absent from pinned GitHub revision: {missing}")
    changed = git("diff", "--name-only", "--no-ext-diff", revision, "--", *paths.values())
    if changed:
        raise ValueError(f"Chapter 7 source differs from pinned GitHub revision:\n{changed}")
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
    return (f'<a class="chapter7-source" data-chapter7-declaration="{html.escape(name)}" '
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
        '<style>#chapter7-source-index table{border-collapse:collapse;width:100%}'
        '#chapter7-source-index td,#chapter7-source-index th{padding:8px;text-align:left;'
        'vertical-align:top;border-bottom:1px solid #dce1e8}'
        '#chapter7-source-index tr:target{background:#ffedab;scroll-margin-top:30px}'
        '#chapter7-source-index td:last-child{overflow-wrap:anywhere}</style>',
        f'<section id="chapter7-source-index" data-chapter7-source-revision="{revision}" '
        f'data-chapter7-audit-sha256="{audit_hash}">',
        '<h2>Chapter 7: Audited declaration source index</h2>',
        f'<p>All {len(locations)} Lean declaration links in the Chapter 7 blueprint. '
        'Declaration modules come from the retained kernel census. Source links '
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
    chapters = list(CHAPTER6_BLOCK.finditer(base))
    if len(chapters) != 1:
        raise ValueError("Expected one existing Chapter 6 source index before Chapter 7")
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
        if attrs.get("id") == "chapter7-source-index":
            self.revisions.append(attrs.get("data-chapter7-source-revision", ""))
            self.audit_hashes.append(attrs.get("data-chapter7-audit-sha256", ""))
        if tag == "a" and (name := attrs.get("data-chapter7-declaration")):
            self.sources.setdefault(name, []).append(attrs.get("href", ""))


def verify_html(text: str, locations: dict[str, tuple[str, int]], revision: str,
                audit_hash: str) -> None:
    parsed = FinderParser()
    parsed.feed(text)
    if parsed.revisions != [revision] or parsed.audit_hashes != [audit_hash]:
        raise ValueError("Chapter 7 finder revision or retained audit hash differs")
    if set(parsed.sources) != set(locations):
        raise ValueError("Chapter 7 finder source-link inventory differs from audited blueprint links")
    for name, (path, line) in locations.items():
        if parsed.ids[f"doc/{name}"] != 1:
            raise ValueError(f"Expected one canonical Chapter 7 declaration fragment: {name}")
        expected = f"{SOURCE_URL}{revision}/{quote(path)}#L{line}"
        if parsed.sources[name] != [expected]:
            raise ValueError(f"Incorrect or duplicate Chapter 7 source file/line link: {name}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Check without changing files.")
    parser.add_argument("--source-revision", help="Immutable source commit recorded by the Chapter 7 audit.")
    args = parser.parse_args()
    current = FINDER.read_text()
    pinned = re.search(r'data-chapter7-source-revision="([0-9a-f]{40})"', current)
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
            raise ValueError("Chapter 7 finder is stale; run scripts/update_chapter7_finder.py")
    else:
        FINDER.write_text(expected)
    print(f'{"Checked" if args.check else "Updated"} {len(locations)} Chapter 7 declaration '
          f'anchors and source file/line links at {revision[:12]}.')


if __name__ == "__main__":
    main()
