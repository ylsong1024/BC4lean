"""Check Chapter 8 publication content and preserve prior verified evidence.

Importing this module performs no native or network operation."""
from collections import Counter
from dataclasses import dataclass
import hashlib
import html
from html.parser import HTMLParser
import json
from pathlib import Path, PurePosixPath
import re
from urllib.parse import quote, unquote, urlsplit

S7 = "4daf13f6be649ef3e7f9fe90122bcbee4707b1b2"
REV = re.compile(r"[0-9a-f]{40}\Z")
SHA = re.compile(r"[0-9a-f]{64}\Z")
MODULE = re.compile(r"BC4lean(?:\.[A-Za-z_][A-Za-z0-9_]*)+\Z")
CONJECTURE = "conj:baum-connes"
PROPERTY = "def:baum-connes-property"
UNIT = "thm:baum-connes-unit"
FINDER = "home_page/docs/find/index.html"
TEX7 = "blueprint/src/parts/07-assembly-map.tex"
TEX8 = "blueprint/src/parts/08-conjecture-and-examples.tex"
AUDIT8 = "docs/audits/chapter8/audit.json"
SOURCE_URL = "https://github.com/ylsong1024/BC4lean/blob/"
FINDER_URL = ("https", "ylsong1024.github.io", "/BC4lean/docs/find/")
BEGIN8 = "<!-- BEGIN GENERATED CHAPTER 8 SOURCE INDEX -->"
END8 = "<!-- END GENERATED CHAPTER 8 SOURCE INDEX -->"
BEGIN7 = "<!-- BEGIN GENERATED CHAPTER 7 SOURCE INDEX -->"
END7 = "<!-- END GENERATED CHAPTER 7 SOURCE INDEX -->"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def safe_relative(value):
    require(isinstance(value, str) and value and "\\" not in value, "Invalid relative path")
    p = PurePosixPath(value)
    require(not p.is_absolute() and ".." not in p.parts and str(p) == value, "Unsafe/noncanonical path")
    return value


def read(root, relative):
    root = Path(root).resolve(strict=True)
    p = root / safe_relative(relative)
    require(p.resolve(strict=True).is_relative_to(root) and p.is_file(), "Source escapes root")
    require(p.stat().st_size <= 32 * 1024 * 1024, "Oversized publication input")
    return p.read_bytes()


def object_json(data):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, "Duplicate JSON object key")
            result[key] = value
        return result
    value = json.loads(data, object_pairs_hook=pairs)
    require(isinstance(value, dict), "Expected JSON object")
    return value


INERT_HTML = {'template','noscript','textarea','plaintext','xmp','iframe','select'}
VOID_HTML = {'area','base','br','col','embed','hr','img','input','link','meta','param','source','track','wbr'}
FOREIGN_EMPTY = {'svg','use','path','circle','rect','line','polygon','polyline','ellipse','g','defs','symbol','stop','lineargradient','radialgradient'}


class Page(HTMLParser):
    def __init__(self, labels=()):
        super().__init__(convert_charrefs=True)
        self.labels = set(labels)
        self.ids = Counter()
        self.sources = {}
        self.revisions, self.audit_hashes, self.links, self.text = [], [], [], []
        self.wrappers, self.statement_links, self.proofs, self.checks = Counter(), {}, Counter(), Counter()
        self.modal_counts, self.modal_links, self.any_checks, self.modal_checks = Counter(), {}, Counter(), Counter()
        self.divs = []
        self.last_statement = None
        self.flags = {}
        self.rows, self.row, self.unattached_proofs = [], None, 0

    def handle_startendtag(self, tag, attributes):
        require(tag in VOID_HTML or tag in FOREIGN_EMPTY, 'Self-closing nonvoid publication tag')
        self.handle_starttag(tag,attributes)
        self.handle_endtag(tag)

    def handle_starttag(self, tag, attributes):
        require(tag not in INERT_HTML, 'Inert/raw-text publication container')
        keys = [k for k, _ in attributes]
        require(len(keys) == len(set(keys)), "Duplicate HTML attribute")
        attrs = dict(attributes)
        identity = attrs.get("id", "")
        classes = set((attrs.get("class") or "").split())
        if tag == 'tr':
            require(self.row is None, 'Nested finder rows')
            self.row = {'anchors':[], 'sources':{}}
        if identity:
            self.ids[identity] += 1
            if self.row is not None and identity.startswith('doc/'):
                self.row['anchors'].append(identity[4:])
        for key, value in attributes:
            if key.startswith("data-general-") or key == "data-chapter8-complete":
                self.flags.setdefault(key, []).append(value)
        if identity == "chapter8-source-index":
            self.revisions.append(attrs.get("data-chapter8-source-revision", ""))
            self.audit_hashes.append(attrs.get("data-chapter8-audit-sha256", ""))
        if tag == "div":
            wrapper = identity if any(c.endswith("_thmwrapper") for c in classes) else None
            if wrapper is not None:
                self.wrappers[wrapper] += 1
                self.last_statement = wrapper
            proof_class = 'proof_content' in classes
            proof = self.last_statement if proof_class else None
            if proof_class and proof is None:
                self.unattached_proofs += 1
            if proof is not None:
                self.proofs[proof] += 1
            modal = identity[:-6] if 'dep-modal-container' in classes and identity.endswith('_modal') else None
            if modal in self.labels:
                self.modal_counts[modal] += 1
            self.divs.append((wrapper, proof, modal, "thm_header_extras" in classes))
        if tag == "a":
            href = attrs.get("href", "")
            self.links.append(href)
            target = urlsplit(href)
            fragment = unquote(target.fragment)
            if fragment.startswith("doc/"):
                name = fragment[4:]
                for wrapper, _, modal, _ in self.divs:
                    if wrapper in self.labels:
                        self.statement_links.setdefault(wrapper, set()).add(name)
                    if modal in self.labels:
                        self.modal_links.setdefault(modal, set()).add(name)
            if name := attrs.get("data-chapter8-declaration"):
                self.sources.setdefault(name, []).append(href)
                if self.row is not None:
                    self.row['sources'].setdefault(name, []).append(href)

    def handle_endtag(self, tag):
        if tag == 'tr':
            require(self.row is not None, 'Unbalanced finder row')
            self.rows.append(self.row); self.row = None
        if tag == "div":
            require(bool(self.divs), "Unbalanced rendered div")
            self.divs.pop()

    def handle_data(self, data):
        self.text.append(data)
        if "✓" in data:
            for wrapper, _, modal, _ in self.divs:
                if modal in self.labels:
                    self.modal_checks[modal] += data.count('✓')
                if wrapper in self.labels:
                    self.any_checks[wrapper] += data.count('✓')
                    if any(header for _, _, _, header in self.divs):
                        self.checks[wrapper] += data.count('✓')

    def finish(self, text):
        self.feed(text)
        self.close()
        require(not self.divs and self.row is None, "Unclosed rendered div/finder row")
        return self


def one_block(text, begin, end):
    require(text.count(begin) == text.count(end) == 1, "Missing/duplicate finder block markers")
    matches = list(re.finditer(re.escape(begin) + r".*?" + re.escape(end) + r"\n?", text, re.S))
    require(len(matches) == 1, "Malformed finder block")
    return matches[0]


def audit8_shape(audit, source):
    require(REV.fullmatch(source or ""), "Expected full S8 revision")
    require(audit.get("schema") == "chapter8.actual.native-milestone-audit.v1"
            and audit.get("schema_version") == 1 and audit.get("status") == "verified_milestone"
            and audit.get("milestone_verified") is True and audit.get("chapter_complete") is False
            and audit.get("general_conjecture_proved") is False and audit.get("source_revision") == source,
            "Chapter 8 lacks an actual correctly scoped native milestone audit")
    modules = audit.get("modules")
    require(isinstance(modules, list) and modules and len(modules) == len(set(modules))
            and all(isinstance(m, str) and MODULE.fullmatch(m) for m in modules), "Invalid new8 modules")
    targets, milestones = audit.get("target_inventory"), audit.get("milestone_inventory")
    require(isinstance(targets, dict) and set(targets) == {PROPERTY, CONJECTURE}
            and isinstance(milestones, dict) and UNIT in milestones
            and not set(targets).intersection(milestones), "Missing original8/Unit inventory")
    items = {**targets, **milestones}
    for label, item in items.items():
        require(isinstance(item, dict) and isinstance(item.get("ready"), bool)
                and item.get("statement_kind") in {"definition", "proposition", "theorem", "lemma", "conjecture"}
                and isinstance(item.get("linked_declarations"), list)
                and len(item["linked_declarations"]) == len(set(item["linked_declarations"])), "Invalid item")
    require(targets[PROPERTY]["ready"] is True and targets[PROPERTY]["statement_kind"] == "definition"
            and targets[CONJECTURE]["ready"] is False and targets[CONJECTURE]["statement_kind"] == "conjecture"
            and targets[CONJECTURE].get("required_declarations") == [] and milestones[UNIT]["ready"] is True,
            "Conjecture/property/Unit readiness is false or overstated")
    require(audit.get("statement_definition_declarations", {}).get(CONJECTURE)
            == ["BC4lean.Assembly.BaumConnesConjecture"], "Missing separate general statement definition")
    return modules, items


@dataclass(frozen=True)
class Context:
    root: Path
    audit: dict
    audit_sha256: str
    source_revision: str
    locations: dict
    retained: object
    provider: object


def context(root, audit_path, source_revision, retained_provider, retained_manifest, new_modules,
            audit_loader, blob_reader):
    """First validate v4 preservation; only then replay audit8 and open helpers."""
    root = Path(root).resolve(strict=True)
    retained = retained_provider.validate(retained_provider.RepositoryReader(root), retained_manifest, new_modules)
    require(retained.audit.get("source_revision") == S7, "Unexpected historical S7 pin")
    require(SHA.fullmatch(retained.audit_sha256 or ""), "Invalid retained7 audit hash")
    audit, audit_hash = audit_loader(root, Path(audit_path), source_revision, retained_provider=retained)
    raw = Path(audit_path).read_bytes()
    require(audit == object_json(raw) and digest(raw) == audit_hash, "audit8 loader/raw mismatch")
    modules, _ = audit8_shape(audit, source_revision)
    require(sorted(modules) == sorted(new_modules), "New modules differ from retained validation")
    links, origins = audit.get("blueprint_links"), audit.get("linked_declarations")
    require(isinstance(links, list) and links and len(links) == len(set(links))
            and isinstance(origins, dict) and set(origins) == set(links), "Invalid exact linked8 origins")
    _, items = audit8_shape(audit, source_revision)
    require(set(links) == {n for item in items.values() for n in item['linked_declarations']},
            'Linked8 census differs from complete statement link inventory')
    locations, commands = {}, {}
    with retained.helpers.open() as helpers:
        locator = helpers["update_chapter5_finder"]
        for name in links:
            record = origins[name]
            require(isinstance(record, dict) and record.get("name") == name and record.get("module") in modules,
                    "Linked8 declaration is not from an audited new8 origin")
            module = record["module"]
            relative = module.replace(".", "/") + ".lean"
            data = read(root, relative)
            require(digest(data) == audit.get("source_sha256", {}).get(relative), "Linked8 source hash mismatch")
            require(blob_reader(source_revision, relative) == data, "Linked8 source differs from immutable S8")
            if module not in commands:
                commands[module] = locator.declaration_lines(locator.code_only(data.decode("utf-8")))
            require(name in commands[module] and isinstance(commands[module][name], int)
                    and commands[module][name] > 0, "No exact source command for linked8 declaration")
            locations[name] = (relative, commands[module][name])
    return Context(root, audit, audit_hash, source_revision, locations, retained, retained_provider)


def verify_finder(text, ctx):
    parser = Page().finish(text)
    require(parser.ids["chapter8-source-index"] == 1 and parser.revisions == [ctx.source_revision]
            and parser.audit_hashes == [ctx.audit_sha256], "Incorrect finder8 pin/audit hash")
    require(set(parser.sources) == set(ctx.locations), "Finder8 declaration inventory differs")
    for name, (relative, line) in ctx.locations.items():
        require(parser.ids["doc/" + name] == 1, "Missing/duplicate canonical declaration anchor")
        expected = SOURCE_URL + ctx.source_revision + "/" + quote(relative) + "#L" + str(line)
        require(parser.sources[name] == [expected], "Incorrect/duplicate immutable S8 source line")
        matching = [row for row in parser.rows if name in row['anchors'] or name in row['sources']]
        require(len(matching) == 1 and matching[0]['anchors'] == [name]
                and matching[0]['sources'] == {name:[expected]},
                'Canonical declaration anchor is not attached to its own exact source row')
    frozen = one_block(text, BEGIN7, END7).group()
    require(frozen.encode() == ctx.retained.frozen_finder_block.encode(), "S7 finder block changed")


def render_finder(current, ctx):
    require(one_block(current, BEGIN7, END7).group().encode() == ctx.retained.frozen_finder_block.encode(),
            "S7 finder bytes changed before rendering")
    if BEGIN8 in current or END8 in current:
        current = current[:one_block(current, BEGIN8, END8).start()] + current[one_block(current, BEGIN8, END8).end():]
    ids = Page().finish(current).ids
    rows = []
    for name, (relative, line) in ctx.locations.items():
        require(ids["doc/" + name] == 0, "New8 declaration anchor already exists outside generated8 block")
        identity = ' id="doc/' + html.escape(name, quote=True) + '"'
        href = SOURCE_URL + ctx.source_revision + "/" + quote(relative) + "#L" + str(line)
        rows.append('<tr' + identity + '><td><code>' + html.escape(name) + '</code></td><td><a '
                    'data-chapter8-declaration="' + html.escape(name, quote=True) + '" href="' + href + '">'
                    + html.escape(relative) + ':' + str(line) + '</a></td></tr>')
    block = '\n'.join([BEGIN8, '<section id="chapter8-source-index" data-chapter8-source-revision="'
        + ctx.source_revision + '" data-chapter8-audit-sha256="' + ctx.audit_sha256 + '">',
        '<h2>Chapter 8: Audited definitions and verified milestones</h2>',
        '<p>The linked general conjecture is a proposition-valued definition and remains unproved.</p>',
        '<table><thead><tr><th>Lean declaration</th><th>Immutable source</th></tr></thead><tbody>',
        *rows, '</tbody></table></section>', END8, ''])
    insertion = one_block(current, BEGIN7, END7).end()
    result = current[:insertion] + block + current[insertion:]
    verify_finder(result, ctx)
    return result


_TOKEN = re.compile(r'\s+|"(?:\\.|[^"\\])*"|->|[A-Za-z_][A-Za-z_0-9]*|-?(?:\d+(?:\.\d*)?|\.\d+)|[{}\[\]=,;]')


def parse_dot(dot):
    """Consume every token; one attribute list, no repeated nodes/defaults/keys."""
    tokens, pos = [], 0
    while pos < len(dot):
        match = _TOKEN.match(dot, pos)
        require(match is not None, "Unsupported/unparsed DOT token")
        token = match[0]
        if not token.isspace():
            tokens.append(token)
        pos = match.end()
    i = 0
    def take(want=None):
        nonlocal i
        require(i < len(tokens), "Truncated DOT")
        token = tokens[i]
        require(want is None or token == want, "Unexpected DOT token")
        i += 1
        return token
    def value():
        token = take()
        require(token not in {'{','}','[',']','=',';',',','->'}, "Invalid DOT value")
        return token[1:-1] if token.startswith('"') else token
    def attributes():
        take('['); result = {}
        while tokens[i] != ']':
            key = value(); take('='); val = value()
            require(key not in result, "Repeated DOT attribute")
            result[key] = val
            if tokens[i] in {',',';'}:
                take()
            else:
                require(tokens[i] == ']', "Missing DOT attribute separator")
        take(']')
        return result
    if tokens and tokens[0] == 'strict':
        take('strict')
    take('digraph')
    if tokens[i] != '{':
        value()
    take('{')
    nodes, edges, defaults = {}, set(), set()
    safe_defaults = {'graph': {'bgcolor'}, 'node': {'label','penwidth'}, 'edge': {'arrowhead'}}
    while tokens[i] != '}':
        head = value()
        if head in safe_defaults and tokens[i] == '[':
            require(head not in defaults, "Repeated DOT defaults")
            attrs = attributes()
            require(set(attrs) <= safe_defaults[head], "Unsafe visual DOT defaults")
            expected_defaults = {'graph': {'bgcolor':'transparent'},
                'node': {'label':'N', 'penwidth':'1.8'}, 'edge': {'arrowhead':'vee'}}
            if head == 'node' and attrs.get('label') == r'\N':
                attrs = {**attrs,'label':'N'}
            require(attrs == expected_defaults[head], 'Noncanonical DOT default values')
            defaults.add(head)
        elif tokens[i] == '->':
            take('->'); target = value()
            require((head, target) not in edges, "Repeated DOT edge")
            edges.add((head, target))
            if tokens[i] == '[':
                require(attributes() in ({}, {'style':'dashed'}), 'Noncanonical/invisible DOT edge attributes')
        else:
            require(tokens[i] == '[' and head not in nodes, "Unstyled/repeated DOT node")
            nodes[head] = attributes()
        take(';')
    take('}')
    require(i == len(tokens) and defaults == {'graph','node','edge'}, "Trailing DOT statements or missing canonical defaults")
    require(all(a in nodes and b in nodes for a,b in edges), "DOT edge references undeclared node")
    return nodes, edges



def decode_static_template(raw):
    """ECMAScript untagged static-template value; reject expressions/invalid escapes.

    Graphviz receives this decoded value, not the HTML's raw source spelling.
    Decoding happens before DOT tokenization, so \x22 cannot hide an attribute.
    """
    out, i = [], 0
    while i < len(raw):
        char = raw[i]; i += 1
        require(not (char == '$' and i < len(raw) and raw[i] == '{'), 'Dynamic DOT template expression')
        if char == '\r':
            if i < len(raw) and raw[i] == '\n': i += 1
            out.append('\n'); continue
        if char != '\\':
            out.append(char); continue
        require(i < len(raw), 'Trailing JavaScript template escape')
        char = raw[i]; i += 1
        if char in '\n\r\u2028\u2029':
            if char == '\r' and i < len(raw) and raw[i] == '\n': i += 1
            continue
        escapes = {'b':'\b','f':'\f','n':'\n','r':'\r','t':'\t','v':'\v'}
        if char in escapes:
            out.append(escapes[char]); continue
        if char == '0':
            require(i == len(raw) or raw[i] not in '0123456789', 'Legacy numeric template escape')
            out.append('\0'); continue
        require(char not in '123456789', 'Legacy numeric template escape')
        if char == 'x':
            digits = raw[i:i+2]
            require(len(digits)==2 and re.fullmatch('[0-9A-Fa-f]{2}',digits), 'Invalid hexadecimal template escape')
            i += 2; out.append(chr(int(digits,16))); continue
        if char == 'u':
            if i < len(raw) and raw[i] == '{':
                end = raw.find('}',i+1)
                require(end >= 0, 'Truncated Unicode template escape')
                digits=raw[i+1:end]
                require(bool(digits) and re.fullmatch('[0-9A-Fa-f]+',digits), 'Invalid Unicode codepoint escape')
                i=end+1
            else:
                digits=raw[i:i+4]
                require(len(digits)==4 and re.fullmatch('[0-9A-Fa-f]{4}',digits), 'Invalid Unicode template escape')
                i+=4
            point=int(digits,16)
            require(point <= 0x10FFFF and not 0xD800 <= point <= 0xDFFF, 'Unsupported Unicode template scalar')
            out.append(chr(point)); continue
        # EscapeSequence's NonEscapeCharacter includes backtick, quotes, $, and N.
        out.append(char)
    return ''.join(out)


class Scripts(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=False)
        self.current, self.scripts = None, []
    def handle_startendtag(self, tag, attributes):
        require(tag in VOID_HTML or tag in FOREIGN_EMPTY, 'Self-closing nonvoid graph tag')
        self.handle_starttag(tag,attributes)
        self.handle_endtag(tag)
    def handle_starttag(self, tag, attributes):
        require(tag not in INERT_HTML, 'Inert/raw-text graph container')
        if tag == 'script':
            require(self.current is None and len(attributes) == len(dict(attributes)),
                    'Nested script or duplicate script attribute')
            self.current = [dict(attributes), '']
    def handle_data(self, data):
        if self.current is not None:
            self.current[1] += data
    def handle_endtag(self, tag):
        if tag == 'script':
            require(self.current is not None, 'Unbalanced graph script')
            self.scripts.append(self.current); self.current = None


GRAPH_SCAFFOLD_SHA256 = '10a2d4332df4aab2a59dbb40bc02be016fc7c45e358d5954beeb4c76c7f952d3'
GRAPH_OTHER_SCRIPTS = [
    ({'type':'text/x-mathjax-config'},'e36df53f33539e76279451036778912ee60700932e28caf9c4d2d11867a6b790'),
    ({'type':'text/javascript','src':'https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js'},
     '6c179f21e6f62b629055d8ab40f454ed02e48b68563913473b857d3638e23b28'),
    ({'src':'js/jquery.min.js','type':'text/javascript'},digest(b'')),
    ({'src':'js/d3.min.js'},digest(b'')), ({'src':'js/hpcc.min.js'},digest(b'')),
    ({'src':'js/d3-graphviz.js'},digest(b''))]


def effective_dot(text):
    parser = Scripts(); parser.feed(text); parser.close()
    require(parser.current is None and len(parser.scripts) == 7, 'Unexpected/unclosed graph script inventory')
    for (attrs, body), (expected_attrs, expected_hash) in zip(parser.scripts[:6],GRAPH_OTHER_SCRIPTS):
        require(attrs == expected_attrs and digest(body.encode()) == expected_hash,
                'Graph supporting-script attributes/body differ from retained renderer')
    attrs, script = parser.scripts[6]
    require(attrs == {'type':'text/javascript'}, 'Unexpected graph renderer script attributes')
    require(len(re.findall(r'\brenderDot\b',script)) == 1, 'Unexpected/multiple renderDot invocations')
    matches=list(re.finditer(r'\.renderDot\(\s*`((?:\\.|[^`\\])*)`\s*\)',script,re.S))
    require(len(matches)==1, 'Graph is not one static JavaScript template')
    match=matches[0]
    scaffold=script[:match.start(1)]+'<DOT>'+script[match.end(1):]
    require(digest(scaffold.encode()) == GRAPH_SCAFFOLD_SHA256,
            'Graph renderer JavaScript outside the static template is not the retained canonical scaffold')
    return decode_static_template(match[1])


def tex_source(tex, items):
    require(not re.search(r'\\(?:input|include|verb)\b', tex), "Indirect/opaque Chapter8 TeX input")
    # Percent comments only; an escaped percent has an odd run of backslashes.
    def uncomment(line):
        for index, char in enumerate(line):
            if char == '%':
                backslashes, previous = 0, index - 1
                while previous >= 0 and line[previous] == '\\':
                    backslashes += 1; previous -= 1
                if backslashes % 2 == 0:
                    return line[:index]
        return line
    source = '\n'.join(uncomment(line) for line in tex.splitlines())
    found, dependencies = {}, {}
    pattern = r'\\begin\{(definition|proposition|theorem|lemma|conjecture)\}(.*?)\\end\{\1\}'
    for match in re.finditer(pattern, source, re.S):
        kind, body = match[1], match[2]
        labels = re.findall(r'\\label\{([^}]+)\}', body)
        require(len(labels) == 1 and labels[0] in items and labels[0] not in found, "Unknown/repeated source statement")
        label = labels[0]; item = items[label]
        require(kind == item['statement_kind'], "Source8 kind differs from audited inventory")
        proof = re.match(r'\\begin\{proof\}(.*?)\\end\{proof\}', source[match.end():].lstrip(), re.S)
        ready = item['ready']
        require(bool(re.search(r'\\leanok\b', body)) == ready, "Source8 readiness differs")
        require(not ready or not re.search(r'\\notready\b', body), "Ready source8 remains pending")
        if ready and kind != 'definition':
            require(proof is not None and re.search(r'\\leanok\b', proof[1])
                    and not re.search(r'\\notready\b', proof[1]), "Verified source8 lacks checked attached proof")
        if label == CONJECTURE:
            require(len(re.findall(r'\\notready\b', body)) == 1 and proof is None,
                    "General conjecture has a proof/readiness claim")
        linked = {n.strip() for group in re.findall(r'\\lean\{([^}]+)\}', body) for n in group.split(',') if n.strip()}
        require(linked == set(item['linked_declarations']), "Source8 declaration links differ")
        dependencies[label] = {n.strip() for group in re.findall(r'\\uses\{([^}]+)\}', body + (proof[1] if proof else ''))
                               for n in group.split(',') if n.strip()}
        found[label] = int(proof is not None)
    require(set(found) == set(items) and sum(found.values()) == len(re.findall(r'\\begin\{proof\}', source)),
            "Missing source8 statement or unattached proof")
    return found, dependencies


def validate_rendered(site, tex, ctx):
    _, items = audit8_shape(ctx.audit, ctx.source_revision)
    expected_proofs, dependencies = tex_source(tex, items)
    chapter = Page(items).finish(read(site, 'blueprint/ch-conjecture-and-examples.html').decode())
    require(chapter.wrappers == Counter({x:1 for x in items}), "Stale/missing/duplicate Chapter8 wrappers")
    require(all(chapter.ids[x] == 1 and chapter.statement_links.get(x, set()) == set(item['linked_declarations'])
                and chapter.proofs[x] == expected_proofs[x] and bool(chapter.checks[x]) == item['ready']
                and (item['ready'] or chapter.any_checks[x] == 0)
                for x,item in items.items()), "Chapter8 links/proofs/checked marks differ")
    require(chapter.unattached_proofs == 0 and set(chapter.proofs) <= set(items),
            "Proof attached outside registered Chapter8 statement")
    for filename in ('dep_graph_chapter_8.html','dep_graph_document.html'):
        text = read(site, 'blueprint/' + filename).decode()
        nodes, edges = parse_dot(effective_dot(text))
        require(set(items) <= set(nodes), "Missing Chapter8 DOT nodes")
        if filename == 'dep_graph_chapter_8.html':
            require(set(nodes) == set(items), "Unexpected Chapter8 DOT nodes")
        parser = Page(items).finish(text)
        require(parser.unattached_proofs == 0 and not parser.proofs, 'Unexpected proof wrapper in graph8 popups')
        def reaches(start, target):
            todo, seen = [start], set()
            while todo:
                item = todo.pop()
                if item == target:
                    return True
                if item not in seen:
                    seen.add(item)
                    todo += [b for a,b in edges if a == item and b not in seen]
            return False
        for label, item in items.items():
            attrs = nodes[label]
            require(attrs.get('shape') == ('box' if item['statement_kind'] == 'definition' else 'ellipse')
                    and attrs.get('label') == label.split(':',1)[-1], 'Wrong graph8 shape/caption')
            expected_attrs = {'color','label','shape','fillcolor','style'} if item['ready'] else {'color','label','shape'}
            require(set(attrs) == expected_attrs, 'Unexpected/missing controlled graph8 node attributes')
            if item['ready']:
                fills = {'#B0ECA3'} if item['statement_kind'] == 'definition' else {'#1CAC78','#9CEC8B'}
                require(attrs.get('color') == 'green' and attrs.get('fillcolor') in fills
                        and attrs.get('style') == 'filled', "Missing actual checked graph8 colors/style")
            else:
                require(attrs.get('color') == '#FFAA33' and 'fillcolor' not in attrs and 'style' not in attrs,
                        "Pending general conjecture has checked/filled graph styling")
            require(parser.modal_counts[label] == 1 and parser.modal_links.get(label, set()) == set(item['linked_declarations']),
                    "Graph8 popup links differ")
            require(item['ready'] or parser.modal_checks[label] == 0, 'Pending conjecture popup has a checked marker')
            require(all(reaches(dep,label) for dep in dependencies[label] if dep in nodes), "Missing graph8 dependency path")
            if filename == 'dep_graph_document.html':
                require(dependencies[label] <= nodes.keys(), "Missing document graph8 prerequisite")
        for href in parser.links:
            target = urlsplit(href); fragment = unquote(target.fragment)
            if fragment.startswith('doc/') and fragment[4:] in ctx.locations:
                require((target.scheme,target.netloc,target.path) == FINDER_URL, "Wrong graph8 source destination")
    for href in chapter.links:
        target = urlsplit(href); fragment = unquote(target.fragment)
        if fragment.startswith('doc/') and fragment[4:] in ctx.locations:
            require((target.scheme,target.netloc,target.path) == FINDER_URL, "Wrong Chapter8 source destination")
    return {'original_targets': {k:v['ready'] for k,v in ctx.audit['target_inventory'].items()},
            'verified_milestones': sum(x['ready'] for x in ctx.audit['milestone_inventory'].values()),
            'statements':len(items), 'explicit_proofs':sum(expected_proofs.values()),
            'declaration_links':len(ctx.locations), 'chapter_complete':False, 'general_conjecture_proved':False}


def check_site(site, publication_revision, ctx):
    require(REV.fullmatch(publication_revision or ''), "Expected full Q8 publication revision")
    require(publication_revision != ctx.source_revision, "Q8 publication and S8 source commits must be separate")
    site = Path(site).resolve(strict=True)
    finder = read(site, 'docs/find/index.html').decode()
    homepage = read(site, 'index.html').decode()
    tex7, tex8 = read(ctx.root,TEX7).decode(), read(ctx.root,TEX8).decode()
    require(digest(tex8.encode()) == ctx.audit.get('source_sha256', {}).get(TEX8),
            'Chapter8 source changed after strict audit8 replay')
    # Fresh verified helper context closes before the provider opens its own.
    with ctx.retained.helpers.open() as helpers:
        manifest = helpers['check_website'].check_site(site, publication_revision)
    retained_publication = ctx.provider.verify_published_chapter7(
        site / 'blueprint', tex7, tex8, homepage, finder, ctx.retained)
    require(isinstance(retained_publication, dict)
            and isinstance(retained_publication.get('chapter7_retained_rendered_checks'), dict)
            and isinstance(retained_publication.get('current_general_conjecture_scope'), dict),
            'Invalid retained7 v4 publication result')
    verify_finder(finder, ctx)
    counts = validate_rendered(site, tex8, ctx)
    hp = Page().finish(homepage)
    normalized = ' '.join(' '.join(hp.text).replace('–','-').replace('—','-').split())
    require('Chapter 7 is verified.' in normalized, "Missing retained Chapter7 completion")
    require('The general Baum-Connes conjecture remains unproved.' in normalized,
            "Missing precise general-conjecture status")
    require('The trivial-group assembly map is verified in both degrees.' in normalized,
            "Missing actual Unit milestone status")
    for key, values in hp.flags.items():
        require(all(v in {'false','unproved'} for v in values), "False chapter/general completion claim")
    pages = dict(manifest['pages'])
    for relative in ('blueprint/ch-assembly-map.html','blueprint/dep_graph_chapter_7.html',
                     'blueprint/ch-conjecture-and-examples.html','blueprint/dep_graph_chapter_8.html',
                     'blueprint/dep_graph_document.html','docs/find/index.html','index.html'):
        data = read(site, relative); pages[relative] = {'sha256':digest(data), 'bytes':len(data)}
    manifest.update(pages=pages, chapter7_mathematical_source_revision=S7,
                    chapter7_core_audit_sha256=ctx.retained.audit_sha256,
                    chapter7=retained_publication['chapter7_retained_rendered_checks'],
                    chapter7_scope=retained_publication['current_general_conjecture_scope'],
                    chapter8_mathematical_source_revision=ctx.source_revision,
                    chapter8_core_audit_sha256=ctx.audit_sha256, chapter8=counts,
                    general_conjecture_proved=False)
    return manifest
