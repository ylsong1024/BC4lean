#!/usr/bin/env python3
"""Maintain the static finder's audited Chapter 5 declaration/source links.

Run this script to regenerate, or use --check as a publication preflight. It
uses the retained kernel audit's declaration origins, checks source SHA-256s,
and resolves exact namespace-qualified declaration commands without Lean or
doc-gen. The source revision stays pinned across website-only changes. After
updating audited Lean sources, pass --source-revision <audited source commit>.
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

from audit_chapter5 import audit_blueprint, code_only

ROOT = Path(__file__).resolve().parents[1]
FINDER = ROOT / 'home_page/docs/find/index.html'
AUDIT = ROOT / 'docs/audits/chapter5/core-audit.json'
SOURCE_URL = 'https://github.com/ylsong1024/BC4lean/blob/'
BEGIN = '<!-- BEGIN GENERATED CHAPTER 5 SOURCE INDEX -->'
END = '<!-- END GENERATED CHAPTER 5 SOURCE INDEX -->'
BLOCK = re.compile(re.escape(BEGIN) + r'.*?' + re.escape(END) + r'\n?', re.S)
SUPPLEMENT = re.compile(
    r' <a class="chapter5-source" data-chapter5-declaration="[^"]+" '
    r'href="[^"]+">[^<]*</a>')
SCOPE = re.compile(
    r'^\s*(namespace|(?:noncomputable\s+)?section)(?:\s+([^\s]+))?\s*$')
SCOPE_END = re.compile(r'^\s*end(?:\s+([^\s]+))?\s*$')
DECLARATION = re.compile(
    r'^\s*(?:@\[[^\n]*?\]\s*)*'
    r'(?:(?:private|protected|noncomputable|unsafe|partial|nonrec)\s+)*'
    r'(?:theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque)'
    r'\s+([^\s:({\[]+)')


def declaration_lines(source: str) -> dict[str, int]:
    """Find explicit commands, distinguishing namespaces and dotted names.

    This is deliberately a source locator, not a Lean parser. The kernel audit
    supplies the authoritative origin module. Every linked name must then have
    one exact explicit command there; generated/private implementation names
    are never guessed from a suffix or silently assigned a parent's line.
    """
    namespace = ''
    stack: list[tuple[str, str, str | None]] = []
    found: dict[str, int] = {}
    for number, line in enumerate(code_only(source).splitlines(), 1):
        if match := SCOPE.match(line):
            kind, name = match.groups()
            stack.append((namespace, kind, name))
            if kind == 'namespace':
                if not name:
                    raise ValueError(f'Unnamed namespace on line {number}')
                namespace = f'{namespace}.{name}' if namespace else name
            continue
        if match := SCOPE_END.match(line):
            if not stack:
                raise ValueError(f'Unmatched end on line {number}')
            namespace, _, opened = stack.pop()
            if match[1] and match[1] != opened:
                raise ValueError(f'Mismatched end on line {number}: {match[1]}')
            continue
        if match := DECLARATION.match(line):
            name = match[1]
            full = (name.removeprefix('_root_.') if name.startswith('_root_.')
                    else f'{namespace}.{name}' if namespace else name)
            if full in found:
                raise ValueError(f'Ambiguous declaration command: {full}')
            found[full] = number
    return found


def git(*args: str) -> str:
    return subprocess.run(['git', *args], cwd=ROOT, check=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          text=True).stdout.strip()


def load_locations(revision: str) -> tuple[dict[str, tuple[str, int]], str]:
    audit_bytes = AUDIT.read_bytes()
    audit = json.loads(audit_bytes)
    links = audit['linked_declarations']
    if len(set(links)) != len(links):
        raise ValueError('Duplicate linked declaration in retained audit')
    actual_links, _, _ = audit_blueprint(
        (ROOT / 'blueprint/src/parts/05-equivariant-kk.tex').read_text())
    if sorted(links) != actual_links:
        raise ValueError('Chapter 5 blueprint links differ from the retained kernel audit')
    origins = {}
    for declaration in audit['declarations']:
        name = declaration['name']
        if name in origins:
            raise ValueError(f'Duplicate audited declaration origin: {name}')
        origins[name] = declaration['module']
    modules = sorted({origins[name] for name in links})
    commands, paths = {}, {}
    for module in modules:
        if not re.fullmatch(r'BC4lean\.[A-Za-z0-9_]+', module):
            raise ValueError(f'Unexpected audited source module: {module}')
        path = module.replace('.', '/') + '.lean'
        source = (ROOT / path).read_bytes()
        if hashlib.sha256(source).hexdigest() != audit['source_sha256'].get(path):
            raise ValueError(f'Source no longer matches retained kernel audit: {path}')
        paths[module] = path
        commands[module] = declaration_lines(source.decode('utf-8'))
    committed = set(git('ls-tree', '-r', '--name-only', revision, '--', *paths.values()).splitlines())
    missing = sorted(set(paths.values()) - committed)
    if missing:
        raise ValueError(f'Audited source absent from pinned GitHub revision: {missing}')
    changed = git('diff', '--name-only', '--no-ext-diff', revision, '--', *paths.values())
    if changed:
        raise ValueError(f'Audited source differs from pinned GitHub revision:\n{changed}')
    locations = {}
    for name in sorted(links):
        module = origins[name]
        if name not in commands[module]:
            raise ValueError(f'No exact declaration command for {name} in {paths[module]}')
        locations[name] = (paths[module], commands[module][name])
    return locations, hashlib.sha256(audit_bytes).hexdigest()


def verify_existing_snapshots(base: str, locations: dict[str, tuple[str, int]]) -> None:
    """Retain existing Chapter 5 code context only when it matches audited bytes."""
    snapshots = re.findall(
        r'<h2 id="([^"]+)">[^<]+</h2><p>源码 SHA-256：<code>([^<]+)</code></p>'
        r'<pre>\n(.*?)</pre>', base, re.S)
    chapter_paths = {path for path, _ in locations.values()}
    for module, digest, body in snapshots:
        path = f'BC4lean/{module}.lean'
        if path not in chapter_paths:
            continue
        lines = re.findall(
            r'<span(?: id="[^"]+")?><a class="line" href="[^"]+" id="[^"]+">'
            r'\s*(\d+)</a> (.*?)</span>\n', body)
        if [int(number) for number, _ in lines] != list(range(1, len(lines) + 1)):
            raise ValueError(f'Invalid existing source line anchors: {path}')
        snapshot = ''.join(html.unescape(code) + '\n' for _, code in lines).encode()
        source = (ROOT / path).read_bytes()
        if snapshot != source or hashlib.sha256(source).hexdigest() != digest:
            raise ValueError(f'Existing Chapter 5 source snapshot is stale: {path}')


def source_link(name: str, location: tuple[str, int], revision: str, label: str) -> str:
    path, line = location
    href = f'{SOURCE_URL}{revision}/{quote(path)}#L{line}'
    return (f'<a class="chapter5-source" data-chapter5-declaration="{html.escape(name)}" '
            f'href="{href}">{label}</a>')


def render(base: str, locations: dict[str, tuple[str, int]], revision: str,
           audit_hash: str) -> str:
    existing = set(re.findall(r'\bid="doc/([^"]+)"', base))
    rows = []
    for name, (path, line) in locations.items():
        anchor = '' if name in existing else f' id="doc/{html.escape(name)}"'
        rows.append(
            f'<tr{anchor}><td><a href="#doc/{html.escape(name)}"><code>{html.escape(name)}'
            f'</code></a></td><td>{source_link(name, (path, line), revision, f"{path}:{line}")}'
            '</td></tr>')
        if name in existing:
            pattern = re.compile(r'(<span id="doc/' + re.escape(name) + r'">[^\n]*)(</span>)')
            base, count = pattern.subn(
                lambda match: match[1] + ' ' + source_link(name, (path, line), revision, 'GitHub source')
                + match[2], base)
            if count != 1:
                raise ValueError(f'Expected one existing source declaration anchor: {name}')
    block = '\n'.join([
        BEGIN,
        '<style>#chapter5-source-index table{border-collapse:collapse;width:100%}'
        '#chapter5-source-index td,#chapter5-source-index th{padding:8px;text-align:left;'
        'vertical-align:top;border-bottom:1px solid #dce1e8}'
        '#chapter5-source-index tr:target{background:#ffedab;scroll-margin-top:30px}'
        'pre a.chapter5-source{margin-left:16px;font:12px system-ui}'
        '#chapter5-source-index td:last-child{overflow-wrap:anywhere}</style>',
        f'<section id="chapter5-source-index" data-source-revision="{revision}" '
        f'data-audit-sha256="{audit_hash}">',
        '<h2>Chapter 5: Audited declaration source index</h2>',
        f'<p>All {len(locations)} Lean declaration links in the Chapter 5 blueprint. '
        'Declaration modules come from the retained kernel audit. Source links point '
        'to declaration lines at commit '
        f'<a href="https://github.com/ylsong1024/BC4lean/commit/{revision}">'
        f'<code>{revision[:12]}</code></a>, whose files match the audited SHA-256 hashes. '
        'Existing source snapshots are below.</p>',
        '<table><thead><tr><th scope="col">Lean declaration</th><th scope="col">GitHub source</th>'
        '</tr></thead><tbody>',
        *rows,
        '</tbody></table></section>',
        END,
        '',
    ])
    marker = '</ul></nav>\n'
    if base.count(marker) != 1:
        raise ValueError('Expected one existing source-browser navigation list')
    return base.replace(marker, marker + block, 1)


class FinderParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.ids: Counter[str] = Counter()
        self.sources: dict[str, list[str]] = {}

    def handle_starttag(self, tag: str, attributes: list[tuple[str, str | None]]) -> None:
        attrs = dict(attributes)
        if identifier := attrs.get('id'):
            self.ids[identifier] += 1
        if tag == 'a' and (name := attrs.get('data-chapter5-declaration')):
            self.sources.setdefault(name, []).append(attrs.get('href', ''))


def verify_html(text: str, locations: dict[str, tuple[str, int]], revision: str) -> None:
    parsed = FinderParser()
    parsed.feed(text)
    if set(parsed.sources) != set(locations):
        raise ValueError('Finder source-link inventory differs from audited blueprint links')
    for name, (path, line) in locations.items():
        if parsed.ids[f'doc/{name}'] != 1:
            raise ValueError(f'Expected one canonical declaration fragment: {name}')
        expected = f'{SOURCE_URL}{revision}/{quote(path)}#L{line}'
        if set(parsed.sources[name]) != {expected}:
            raise ValueError(f'Incorrect source file/line link: {name}')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='Check without changing files.')
    parser.add_argument('--source-revision', help='Immutable audited source commit; defaults to the pinned revision.')
    args = parser.parse_args()
    current = FINDER.read_text()
    pinned = re.search(r'data-source-revision="([0-9a-f]{40})"', current)
    revision = git('rev-parse', '--verify',
                   f'{args.source_revision or (pinned[1] if pinned else "HEAD")}^{{commit}}')
    if not re.fullmatch(r'[0-9a-f]{40}', revision):
        raise ValueError('Expected a full immutable source commit hash')
    base = SUPPLEMENT.sub('', BLOCK.sub('', current))
    locations, audit_hash = load_locations(revision)
    verify_existing_snapshots(base, locations)
    expected = render(base, locations, revision, audit_hash)
    verify_html(expected, locations, revision)
    if args.check:
        verify_html(current, locations, revision)
        if current != expected:
            raise ValueError('Chapter 5 finder is stale; run scripts/update_chapter5_finder.py')
    else:
        FINDER.write_text(expected)
    print(f'{"Checked" if args.check else "Updated"} {len(locations)} Chapter 5 declaration '
          f'anchors and source file/line links at {revision[:12]}.')


if __name__ == '__main__':
    main()
