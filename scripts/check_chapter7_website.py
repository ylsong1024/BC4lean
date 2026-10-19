#!/usr/bin/env python3
"""Check actual Chapter 7 pages/graphs/links and extend the version manifest.

Original assembly targets retain their individual audited readiness status.
Verified intermediate lemmas have independent checked nodes and source links.
Existing Chapter 5/6 checks run unchanged before this check is accepted.
"""
import argparse
import hashlib
import json
from html.parser import HTMLParser
from pathlib import Path
import re
import runpy
from urllib.parse import unquote, urlsplit

from audit_chapter7 import (audit_blueprint, load_inventory, pending_blueprint_targets,
                           tex_code_only)
from check_website import Page, check_site
from update_chapter7_finder import load_audit, load_locations, verify_html

ROOT = Path(__file__).resolve().parents[1]


def validate_rendered_chapter7(output, tex, audit):
    def require(condition, message):
        if not condition:
            raise ValueError(f"Chapter 7 rendered status: {message}")

    links, targets, milestones = audit_blueprint(tex, load_inventory(
        ROOT / "docs/audits/chapter7/inventory.json"))
    require(audit["target_inventory"] == targets and audit["milestone_inventory"] == milestones,
            "source inventories differ from the retained kernel audit")
    pending = pending_blueprint_targets(tex)
    complete = all(item["ready"] for item in targets.values()) and not pending
    require(audit.get("blueprint_links") == links and audit.get("notready_targets") == pending
            and audit.get("chapter_complete") is complete,
            "source declaration/pending/completeness inventory differs from the retained audit")
    expected = {**targets, **milestones}
    source = tex_code_only(tex)
    source_proofs, dependencies = {}, {}
    for block in re.finditer(r"\\begin\{(definition|proposition|theorem|lemma)\}(.*?)"
                             r"\\end\{\1\}", source, re.S):
        labels = re.findall(r"\\label\{([^}]+)\}", block[2])
        require(len(labels) == 1 and labels[0] in expected,
                "unregistered or unlabeled source statement")
        item = expected[labels[0]]
        following = source[block.end():].lstrip()
        proof = re.match(r"\\begin\{proof\}(.*?)\\end\{proof\}", following, re.S)
        if item["ready"] and block[1] != "definition":
            require(proof is not None and re.search(r"\\leanok\b", proof[1])
                    and not re.search(r"\\notready\b", proof[1]),
                    f"{labels[0]} lacks an explicit checked proof")
        if proof is not None:
            require(not re.search(r"\\leanok\b", proof[1]) or item["ready"],
                    f"pending original {labels[0]} falsely claims a checked proof")
            if item["ready"]:
                require(re.search(r"\\leanok\b", proof[1])
                        and not re.search(r"\\notready\b", proof[1]),
                        f"{labels[0]} has an unchecked attached proof")
        source_proofs[labels[0]] = int(proof is not None)
        uses = re.findall(r"\\uses\{([^}]*)\}", block[2] + (proof[1] if proof is not None else ""))
        dependencies[labels[0]] = {name.strip() for group in uses for name in group.split(",") if name.strip()}
    proof_count = sum(source_proofs.values())
    require(proof_count == len(re.findall(r"\\begin\{proof\}", source)),
            "unattached proof environment")
    parser = runpy.run_path(str(ROOT / "blueprint/src/build_web.py"))["_Chapter5HTML"]
    class ChapterPage(parser):
        """Keep the existing parser and associate actual theorem/proof wrappers."""
        def __init__(self, labels):
            super().__init__(labels)
            self.wrapper_ids = []
            self.statement_links = {label: set() for label in labels}
            self.statement_proofs = {label: 0 for label in labels}
            self.last_statement = None
            self.statement = None
            self.statement_depth = 0

        def handle_starttag(self, tag, attributes):
            super().handle_starttag(tag, attributes)
            attrs = dict(attributes)
            classes = set(attrs.get("class", "").split())
            identity = attrs.get("id", "")
            if any(name.endswith("_thmwrapper") for name in classes):
                self.wrapper_ids.append(identity)
            if identity in self.labels:
                self.last_statement = identity
            if tag == "div":
                if self.statement is not None:
                    self.statement_depth += 1
                elif identity in self.labels:
                    self.statement, self.statement_depth = identity, 1
                if "proof_content" in classes:
                    require(self.last_statement is not None, "rendered proof precedes every statement")
                    self.statement_proofs[self.last_statement] += 1
            if tag == "a" and self.statement is not None:
                fragment = unquote(urlsplit(attrs.get("href", "")).fragment)
                if fragment.startswith("doc/"):
                    self.statement_links[self.statement].add(fragment[4:])

        def handle_endtag(self, tag):
            super().handle_endtag(tag)
            if tag == "div" and self.statement is not None:
                self.statement_depth -= 1
                if self.statement_depth == 0:
                    self.statement = None

    chapter = ChapterPage(set(expected))
    chapter.feed((Path(output) / "ch-assembly-map.html").read_text())
    require(all(chapter.statement_ids[label] == 1 for label in expected),
            "missing/duplicate statement anchors")
    require(chapter.links == set(links) and chapter.proof_count == proof_count,
            "chapter links or proof count differ from the source")
    require(set(chapter.wrapper_ids) == set(expected) and len(chapter.wrapper_ids) == len(expected),
            "stale, missing, or duplicate rendered statement wrappers")
    require(chapter.statement_proofs == source_proofs,
            "rendered proofs belong to different statements than the source")
    require(all(chapter.statement_links[label] == set(item["linked_declarations"])
                for label, item in expected.items()),
            "rendered statement declaration links differ from their source statements")
    graph_results = {}
    for filename in ("dep_graph_chapter_7.html", "dep_graph_document.html"):
        html = (Path(output) / filename).read_text()
        dots = re.findall(r"\.renderDot\(\s*`(.*?)`\s*\)", html, re.S)
        require(len(dots) == 1, f"{filename}: expected one DOT graph")
        nodes = {}
        for label, attributes in re.findall(r'"([^"\n]+)"\s*\[([^\[\]]*)\];', dots[0], re.S):
            attrs = dict(re.findall(r'(\w+)\s*=\s*("[^"\n]*"|[^,\s;\]]+)', attributes))
            if "label" in attrs:
                require(label not in nodes, f"{filename}: duplicate node {label}")
                nodes[label] = attrs
        require(set(expected) <= set(nodes), f"{filename}: missing Chapter 7 nodes")
        if filename == "dep_graph_chapter_7.html":
            require(set(nodes) == set(expected), "unexpected Chapter 7 graph node")
        edges = set(re.findall(r'"([^"\n]+)"\s*->\s*"([^"\n]+)"', dots[0]))
        require(all(a in nodes and b in nodes for a, b in edges),
                f"{filename}: an edge references an undeclared graph node")
        successors = {label: set() for label in nodes}
        for a, b in edges:
            successors[a].add(b)

        def reaches(start, target):
            # plastexdepgraph uses Graphviz's transitive reduction by default.
            # A redundant direct dependency may disappear, but its path must
            # survive; requiring every literal source edge would reject it.
            pending, seen = [start], set()
            while pending:
                node = pending.pop()
                if node == target:
                    return True
                if node not in seen:
                    seen.add(node)
                    pending.extend(successors[node] - seen)
            return False

        for label, used in dependencies.items():
            if filename == "dep_graph_document.html":
                require(used <= set(nodes), f"{filename}: missing dependency nodes for {label}")
            require(all(reaches(dependency, label) for dependency in used if dependency in nodes),
                    f"{filename}: missing source dependency path for {label}")
        document = parser(set(expected))
        document.feed(html)
        for href in Page(html).links:
            target = urlsplit(href)
            fragment = unquote(target.fragment)
            require(not (Path(unquote(target.path)).name == "ch-assembly-map.html"
                         and fragment in nodes and fragment not in expected),
                    f"{filename}: stale Chapter 7 node/popup {fragment}")
        for label, item in expected.items():
            attrs = nodes[label]
            color = attrs.get("color", "").strip('"')
            fill = attrs.get("fillcolor", "").strip('"')
            checked_fills = {"#B0ECA3", "#1CAC78", "#9CEC8B"}
            if item["ready"]:
                require(color == "green", f"{filename}: false readiness border for {label}")
                fills = {"#B0ECA3"} if item["statement_kind"] == "definition" else {"#1CAC78", "#9CEC8B"}
                require(fill in fills, f"{filename}: missing checked definition/proof fill for {label}")
                styles = {value.strip() for value in attrs.get("style", "").strip('"').split(",")}
                require("filled" in styles, f"{filename}: unchecked fill style for {label}")
            else:
                require(color == "#FFAA33" and fill not in checked_fills,
                        f"{filename}: pending original has false checked/readiness colors for {label}")
            require(attrs.get("shape") == ("box" if item["statement_kind"] == "definition" else "ellipse"),
                    f"{filename}: wrong statement shape for {label}")
            require(document.modal_counts[label] == 1 and
                    document.modal_links[label] == set(item["linked_declarations"]),
                    f"{filename}: source-link popup differs for {label}")
        graph_results[filename] = {"nodes": len(expected), "links": len(links)}
    return {"chapter_complete": audit["chapter_complete"], "original_targets": {
        label: item["ready"] for label, item in targets.items()},
        "verified_milestones": len(milestones), "statements": len(expected),
        "explicit_proofs": proof_count, "declaration_links": len(links), "graphs": graph_results}


def validate_general_conjecture_scope(tex, homepage_html):
    """Bind Chapter 7's construction-only scope to the actual Chapter 8 marker.

    Do not infer theorem status by spotting the word "isomorphism" in prose.
    The actual original conjecture must remain pending. Optional structured
    homepage claim flags must stay false. Exact affirmative sentence checks
    catch a few obvious stale editorial claims without rejecting explanatory
    sentences such as "does not prove that assembly is an isomorphism".
    This is a publication safeguard, not a natural-language proof audit.
    """
    source = tex_code_only(tex)
    label = "conj:baum-connes"
    blocks = re.findall(r"\\begin\{conjecture\}(.*?)\\end\{conjecture\}", source, re.S)
    found = [body for body in blocks if label in re.findall(r"\\label\{([^}]+)\}", body)]
    if (len(re.findall(r"\\label\{" + re.escape(label) + r"\}", source)) != 1
            or len(found) != 1
            or len(re.findall(r"\\notready\b", found[0])) != 1
            or re.search(r"\\leanok\b", found[0])):
        raise ValueError("Chapter 7 construction does not certify the general Baum-Connes conjecture")
    conjecture = next(match for match in re.finditer(
        r"\\begin\{conjecture\}(.*?)\\end\{conjecture\}", source, re.S)
        if label in re.findall(r"\\label\{([^}]+)\}", match[1]))
    proof = re.match(r"\\begin\{proof\}(.*?)\\end\{proof\}", source[conjecture.end():].lstrip(), re.S)
    if proof and re.search(r"\\leanok\b", proof[1]):
        raise ValueError("Chapter 7 cannot publish a checked general Baum-Connes conjecture proof")

    class ScopeClaims(HTMLParser):
        flags = {"data-general-baum-connes-proved", "data-general-assembly-isomorphism-proved"}

        def handle_starttag(self, tag, attributes):
            for name, value in attributes:
                if name in self.flags and value not in {"false", "unproved"}:
                    raise ValueError("Chapter 7 homepage falsely flags a proved general conjecture/isomorphism")

    ScopeClaims().feed(homepage_html)
    explicit_claims = {
        "The general Baum-Connes conjecture is proved.",
        "Chapter 7 proves the general Baum-Connes conjecture.",
        "The assembly map is an isomorphism for every countable discrete group.",
    }
    normalized = Page(homepage_html).text.replace("–", "-").replace("—", "-")
    # Require the whole sentence to be an exact affirmative claim. A negative
    # qualification or explanation in the same sentence must not match.
    sentences = {" ".join(part.split()) + "." for part in re.split(r"[.!?]", normalized) if part.strip()}
    if sentences & explicit_claims:
        raise ValueError("Chapter 7 homepage explicitly claims a proved general conjecture/isomorphism")
    return {"general_baum_connes_conjecture_verified": False,
            "general_assembly_isomorphism_proved": False,
            "general_conjecture_label": label, "general_conjecture_status": "pending"}


def check_chapter7_site(site, revision):
    manifest = check_site(site, revision)
    finder = (site / "docs/find/index.html").read_text()
    pin = re.search(r'data-chapter7-source-revision="([0-9a-f]{40})"', finder)
    if not pin:
        raise ValueError("Chapter 7 finder lacks an immutable source revision")
    locations, audit_hash = load_locations(pin[1])
    verify_html(finder, locations, pin[1], audit_hash)
    audit, _ = load_audit(pin[1])
    tex = (ROOT / "blueprint/src/parts/07-assembly-map.tex").read_text()
    counts = validate_rendered_chapter7(site / "blueprint", tex, audit)
    for relative in ("ch-assembly-map.html", "dep_graph_chapter_7.html", "dep_graph_document.html"):
        page = Page((site / "blueprint" / relative).read_text())
        seen = set()
        for href in page.links:
            target = urlsplit(href)
            fragment = unquote(target.fragment)
            if fragment.startswith("doc/") and fragment[4:] in locations:
                if (target.scheme, target.netloc, target.path) != (
                        "https", "ylsong1024.github.io", "/BC4lean/docs/find/"):
                    raise ValueError(f"Incorrect Chapter 7 source-link destination: {href}")
                seen.add(fragment[4:])
        if seen != set(locations):
            raise ValueError(f"Incomplete Chapter 7 declaration-link inventory in {relative}")
    homepage_html = (site / "index.html").read_text()
    homepage = Page(homepage_html)
    scope = validate_general_conjecture_scope(
        (ROOT / "blueprint/src/parts/08-conjecture-and-examples.tex").read_text(),
        homepage_html)
    incomplete = "Chapter 7 has verified foundations; the assembly map remains incomplete."
    if audit["chapter_complete"]:
        if "Chapter 7 is verified." not in homepage.text or incomplete in homepage.text:
            raise ValueError("Homepage lacks the audited Chapter 7 completion status")
    elif (incomplete not in homepage.text
          or re.search(r"Chapter\s+7\s+is\s+(?:fully\s+)?(?:verified|complete|finished)\b",
                       homepage.text, re.I)):
        raise ValueError("Homepage lacks the precise Chapter 7 milestone/incomplete status or falsely claims completion")
    for relative in ("blueprint/ch-assembly-map.html", "blueprint/dep_graph_chapter_7.html"):
        data = (site / relative).read_bytes()
        manifest["pages"][relative] = {"sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}
    manifest.update({"chapter7_mathematical_source_revision": pin[1],
                     "chapter7_core_audit_sha256": audit_hash, "chapter7": counts,
                     "chapter7_scope": scope})
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("site", type=Path)
    parser.add_argument("--revision", required=True)
    args = parser.parse_args()
    manifest = check_chapter7_site(args.site.resolve(strict=True), args.revision)
    (args.site / "site-version.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Verified actual Chapter 7 publication: {manifest['chapter7']}")


if __name__ == "__main__":
    main()
