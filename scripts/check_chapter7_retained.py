#!/usr/bin/env python3
"""Preserve the verified Chapter 7 proof/evidence baseline across later chapters.

This read-only verifier performs no Lean/Lake or Git mutation. Its result
certifies retained Chapter 7 source/evidence and registered aggregate extension,
not new Chapter 8 native proofs or publication. Historical and current bytes
have explicit providers; no verifier/ROOT monkeypatch substitutes one for the other.
"""
from __future__ import annotations

import argparse
import builtins
from contextlib import contextmanager
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import selectors
import subprocess
import sys
import time
import types
from types import MappingProxyType
from typing import Mapping

Q7 = "e1afa3d693e0a95cd568f517578d109995d80442"
S7 = "4daf13f6be649ef3e7f9fe90122bcbee4707b1b2"
MANIFEST_SHA = "1518087f749f7a6cf0b61b1cfae442ab34f22e4864371f96a1f8dee0454c3035"
MANIFEST_PATH = Path(__file__).resolve().parents[1] / "docs/audits/chapter8/Chapter7Baseline.json"
AUDIT = "docs/audits/chapter7/audit.json"
BUILD = "docs/audits/chapter7/build.json"
FINDER = "home_page/docs/find/index.html"
TEX7 = "blueprint/src/parts/07-assembly-map.tex"
TEX8 = "blueprint/src/parts/08-conjecture-and-examples.tex"
INVENTORY = "docs/audits/chapter7/inventory.json"
FIXTURE = "docs/audits/chapter7/ExpectedTypes.lean"
AGGREGATE = "BC4lean.lean"
BASE6 = "docs/audits/chapter7/Chapter6Imports.lean"
EXCEPTIONS = frozenset({AGGREGATE, TEX8, ".github/workflows/chapter7.yml"})
ALLOWED = frozenset({"propext", "Classical.choice", "Quot.sound"})
MODULE = re.compile(r"BC4lean(?:\.[A-Za-z_][A-Za-z0-9_]*)+\Z")
SHA = re.compile(r"[0-9a-f]{64}\Z")
REV = re.compile(r"[0-9a-f]{40}\Z")
MAX_FILES = 4096
MAX_FILE = 8 * 1024 * 1024
MAX_TOTAL = 128 * 1024 * 1024
HELPERS = (
    ("audit_chapter5", "scripts/audit_chapter5.py"),
    ("audit_chapter6", "scripts/audit_chapter6.py"),
    ("update_chapter5_finder", "scripts/update_chapter5_finder.py"),
    ("update_chapter6_finder", "scripts/update_chapter6_finder.py"),
    ("audit_chapter7", "scripts/audit_chapter7.py"),
    ("update_chapter7_finder", "scripts/update_chapter7_finder.py"),
    ("check_website", "scripts/check_website.py"),
    ("check_chapter7_website", "scripts/check_chapter7_website.py"),
)


class Rejected(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Rejected(message)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def safe_path(value: str) -> str:
    require(isinstance(value, str) and bool(value) and "\\" not in value
            and "\0" not in value and "\n" not in value and "\r" not in value,
            "Unsafe evidence path")
    p = PurePosixPath(value)
    require(not p.is_absolute() and all(part not in {".", ".."} for part in p.parts)
            and p.as_posix() == value, f"Unsafe/noncanonical evidence path: {value}")
    return value


def json_object(data: bytes, label: str) -> dict:
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, f"Duplicate JSON key in {label}: {key}")
            result[key] = value
        return result
    try:
        result = json.loads(data, object_pairs_hook=unique)
    except (UnicodeError, json.JSONDecodeError) as error:
        raise Rejected(f"Malformed JSON in {label}") from error
    require(isinstance(result, dict), f"Expected JSON object: {label}")
    return result


def hash_map(value: object, count: int, label: str) -> dict[str, str]:
    require(isinstance(value, dict) and len(value) == count, f"Wrong {label} path count")
    for path, sha in value.items():
        safe_path(path)
        require(isinstance(sha, str) and SHA.fullmatch(sha) is not None,
                f"Invalid {label} SHA: {path}")
    return value


def load_manifest(data: bytes) -> dict:
    require(digest(data) == MANIFEST_SHA, "Fixed baseline manifest digest differs")
    m = json_object(data, "baseline manifest")
    require(set(m) == {"schema", "publication_revision", "source_revision", "proof_sources",
                       "original_inputs", "canonical_artifacts", "trusted_pure_helpers",
                       "current_control_exceptions"}, "Baseline manifest schema fields differ")
    require(m["schema"] == "chapter7.retained.baseline-manifest.prototype.v1"
            and m["publication_revision"] == Q7 and m["source_revision"] == S7,
            "Baseline revision/schema differs")
    hash_map(m["proof_sources"], 930, "proof source")
    hash_map(m["original_inputs"], 145, "original input")
    hash_map(m["canonical_artifacts"], 21, "canonical artifact")
    hash_map(m["trusted_pure_helpers"], 9, "pure helper")
    require(set(m["current_control_exceptions"]) == EXCEPTIONS
            and len(m["current_control_exceptions"]) == 3,
            "Continuation control exceptions differ")
    require(set(m["trusted_pure_helpers"]) == {p for _, p in HELPERS}
            | {"blueprint/src/build_web.py"}, "Trusted helper set differs")
    for path in m["proof_sources"]:
        require(path.startswith("BC4lean/") and path.endswith(".lean")
                and MODULE.fullmatch(path.removesuffix(".lean").replace("/", ".")),
                f"Invalid frozen proof source: {path}")
    return m


class RepositoryReader:
    """Bounded, read-only Git/current-file provider; no implicit fallback."""
    def __init__(self, root: Path):
        self.root = root.resolve(strict=True)
        self.git_cache: dict[tuple[str, str], bytes] = {}
        self.current_seen: dict[str, str] = {}
        self.total = 0

    def _command(self, args: list[str], payload: bytes | None = None,
                 max_output: int = MAX_TOTAL) -> bytes:
        # Fixed read-only commands only. Each blob size is checked before the
        # content batch is requested; header/list output is independently capped.
        process = subprocess.Popen(["git", *args], cwd=self.root,
                                   stdin=subprocess.PIPE if payload else subprocess.DEVNULL,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        buffers = {"stdout": bytearray(), "stderr": bytearray()}
        deadline, written = time.monotonic() + 30, 0
        try:
            with selectors.DefaultSelector() as selector:
                for label, stream in (("stdout", process.stdout), ("stderr", process.stderr)):
                    os.set_blocking(stream.fileno(), False)
                    selector.register(stream, selectors.EVENT_READ, label)
                if payload:
                    os.set_blocking(process.stdin.fileno(), False)
                    selector.register(process.stdin, selectors.EVENT_WRITE, "stdin")
                while selector.get_map():
                    remaining = deadline - time.monotonic()
                    require(remaining > 0, "Read-only Git command exceeded30-second budget")
                    for key, _ in selector.select(min(remaining, 0.25)):
                        stream, label = key.fileobj, key.data
                        if label == "stdin":
                            try:
                                written += os.write(stream.fileno(), payload[written:written + 8192])
                            except BlockingIOError:
                                continue
                            if written == len(payload):
                                selector.unregister(stream)
                                stream.close()
                            continue
                        limit = max_output if label == "stdout" else 65536
                        try:
                            chunk = os.read(stream.fileno(), min(65536, limit - len(buffers[label]) + 1))
                        except BlockingIOError:
                            continue
                        if not chunk:
                            selector.unregister(stream)
                            stream.close()
                        else:
                            buffers[label].extend(chunk)
                            require(len(buffers[label]) <= limit,
                                    "Git output exceeds bounded inventory budget")
            require(process.wait(timeout=max(0.01, deadline - time.monotonic())) == 0,
                    f"Read-only Git command failed: {args[0]}")
            return bytes(buffers["stdout"])
        except BaseException:
            if process.poll() is None:
                process.kill()  # Only this reader's own bounded Git child.
            process.wait(timeout=5)
            raise
        finally:
            for stream in (process.stdin, process.stdout, process.stderr):
                if stream is not None:
                    stream.close()

    def head(self) -> str:
        value = self._command(["rev-parse", "--verify", "HEAD^{commit}"], max_output=128).decode().strip()
        require(REV.fullmatch(value) is not None, "Invalid current HEAD")
        return value

    def ancestor(self, earlier: str, later: str) -> bool:
        require(REV.fullmatch(earlier) is not None and REV.fullmatch(later) is not None,
                "Invalid ancestry revision")
        result = subprocess.run(["git", "merge-base", "--is-ancestor", earlier, later],
                                cwd=self.root, capture_output=True, timeout=15)
        require(result.returncode in {0, 1}, "Missing Git object or failed ancestry query")
        return result.returncode == 0

    def prefetch(self, revision: str, paths: list[str]) -> None:
        require(REV.fullmatch(revision) is not None, "Invalid immutable revision")
        pending = sorted({safe_path(p) for p in paths if (revision, p) not in self.git_cache})
        require(len(self.git_cache) + len(pending) <= MAX_FILES, "Too many Git evidence blobs")
        if not pending:
            return
        payload = "".join(f"{revision}:{p}\n" for p in pending).encode()
        headers = self._command(["cat-file", "--batch-check=%(objectname) %(objecttype) %(objectsize)"],
                                payload, max_output=256 * len(pending))
        lines = headers.splitlines()
        require(len(lines) == len(pending), "Incomplete Git object-size census")
        sizes = []
        for line in lines:
            fields = line.split()
            require(len(fields) == 3 and fields[1] == b"blob" and fields[2].isdigit(),
                    "Missing/nonblob historical input")
            size = int(fields[2])
            require(size <= MAX_FILE, "Historical blob exceeds file budget")
            sizes.append(size)
        require(self.total + sum(sizes) <= MAX_TOTAL, "Historical blob total exceeds budget")
        output = self._command(["cat-file", "--batch"], payload,
                               max_output=sum(sizes) + 256 * len(pending))
        pos = 0
        for path, size, expected_header in zip(pending, sizes, lines):
            end = output.find(b"\n", pos)
            require(end >= pos and output[pos:end] == expected_header,
                    "Git content/size headers disagree")
            data = output[end + 1:end + 1 + size]
            require(len(data) == size and output[end + 1 + size:end + 2 + size] == b"\n",
                    "Truncated Git content framing")
            self.git_cache[(revision, path)] = data
            pos = end + 2 + size
        require(pos == len(output), "Extra Git content bytes")
        self.total += sum(sizes)

    def blob(self, revision: str, path: str) -> bytes:
        safe_path(path)
        self.prefetch(revision, [path])
        return self.git_cache[(revision, path)]

    def current(self, path: str) -> bytes:
        safe_path(path)
        local = self.root / path
        require(local.resolve(strict=True).is_relative_to(self.root) and local.is_file()
                and not local.is_symlink(), f"Current evidence is not an internal regular file: {path}")
        size = local.stat().st_size
        require(size <= MAX_FILE, f"Current file exceeds budget: {path}")
        with local.open("rb") as stream:
            data = stream.read(MAX_FILE + 1)
        require(len(data) == size and len(data) <= MAX_FILE, f"Current file changed/oversized: {path}")
        if path not in self.current_seen:
            require(len(self.current_seen) < MAX_FILES and self.total + len(data) <= MAX_TOTAL,
                    "Current evidence exceeds bounded inventory budget")
            self.total += len(data)
            self.current_seen[path] = digest(data)
        else:
            require(self.current_seen[path] == digest(data), f"Current input changed between reads: {path}")
        return data

    def proof_paths(self, revision: str | None = None) -> set[str]:
        if revision is None:
            result = set()
            for path in (self.root / "BC4lean").rglob("*.lean"):
                require(len(result) < MAX_FILES, "Unbounded project proof-file inventory")
                result.add(path.relative_to(self.root).as_posix())
        else:
            raw = self._command(["ls-tree", "-r", "-z", "--name-only", revision, "--", "BC4lean"],
                                max_output=1024 * 1024)
            result = {p.decode() for p in raw.split(b"\0") if p.endswith(b".lean")}
        require(len(result) <= MAX_FILES, "Unbounded project proof-file inventory")
        for path in result:
            safe_path(path)
        return result

    def stable(self) -> None:
        for path in list(self.current_seen):
            self.current(path)


@dataclass
class MemoryReader:
    """Explicit isolated fixtures; mutations affect bytes in this object only."""
    root: Path
    current_files: dict[str, bytes]
    git_files: dict[tuple[str, str], bytes]
    revision: str = Q7
    ancestry_ok: bool = True

    def current(self, path):
        safe_path(path)
        require(path in self.current_files, f"Missing current fixture file: {path}")
        return self.current_files[path]

    def blob(self, revision, path):
        safe_path(path)
        require((revision, path) in self.git_files, f"Missing historical fixture blob: {path}")
        return self.git_files[(revision, path)]

    def prefetch(self, revision, paths):
        for path in paths:
            self.blob(revision, path)

    def head(self):
        return self.revision

    def ancestor(self, earlier, later):
        return self.ancestry_ok

    def proof_paths(self, revision=None):
        paths = self.current_files if revision is None else {
            p for (rev, p) in self.git_files if rev == revision}
        return {p for p in paths if p.startswith("BC4lean/") and p.endswith(".lean")}

    def stable(self):
        pass  # The production reader rechecks actual files; this is not a receipt claim.


def namespace_fingerprint(module):
    """Detect mutation while a fresh verified helper context is in use."""
    def value(item, depth=0):
        require(depth <= 12, "Unexpected helper namespace nesting")
        if isinstance(item, types.FunctionType):
            return ("function", id(item), id(item.__code__), id(item.__globals__),
                    value(item.__defaults__, depth + 1), value(item.__kwdefaults__, depth + 1))
        if isinstance(item, (staticmethod, classmethod)):
            return (type(item).__name__, value(item.__func__, depth + 1))
        if isinstance(item, type) and item.__module__ == module.__name__:
            return ("class", id(item), tuple(sorted((k, value(v, depth + 1))
                    for k, v in vars(item).items() if k not in {"__dict__", "__weakref__"})))
        if isinstance(item, dict):
            require(len(item) <= 4096, "Unexpected helper dictionary size")
            return ("dict", tuple(sorted((repr(k), value(v, depth + 1)) for k, v in item.items())))
        if isinstance(item, (set, frozenset)):
            return (type(item).__name__, tuple(sorted(repr(v) for v in item)))
        if isinstance(item, (tuple, list)):
            require(len(item) <= 4096, "Unexpected helper sequence size")
            return (type(item).__name__, tuple(value(v, depth + 1) for v in item))
        if item is None or isinstance(item, (str, int, float, bool, bytes)):
            return (type(item).__name__, item)
        return (type(item).__name__, id(item))
    return tuple(sorted((key, value(item)) for key, item in vars(module).items()))


@dataclass(frozen=True)
class VerifiedHelperSources:
    """Fresh verified modules per operation; no public marker establishes provenance."""
    root: Path
    sources: Mapping[str, bytes]
    expected_sha256: Mapping[str, str]

    @contextmanager
    def open(self):
        require(dict(self.expected_sha256) == load_manifest(MANIFEST_PATH.read_bytes())["trusted_pure_helpers"],
                "Helper source provenance does not match fixed manifest")
        names = {name for name, _ in HELPERS}
        require(not names.intersection(sys.modules), "Preexisting/unverified helper module in import context")
        result = {}
        try:
            for name, path in HELPERS:
                data = self.sources[path]
                require(digest(data) == self.expected_sha256[path], "Verified helper source bundle changed")
                module = types.ModuleType(name)
                module.__file__ = str(self.root / path)
                module.__dict__["__builtins__"] = dict(vars(builtins))
                sys.modules[name] = module
                result[name] = module
                exec(compile(data, module.__file__, "exec"), module.__dict__)
            fingerprints = {name: namespace_fingerprint(module) for name, module in result.items()}
            yield result
            require(all(sys.modules.get(name) is module for name, module in result.items()),
                    "Temporary verified helper module replaced during use")
            require(all(namespace_fingerprint(module) == fingerprints[name] for name, module in result.items()),
                    "Verified helper namespace/function mutated during use")
        finally:
            for name in result:
                sys.modules.pop(name, None)


def verified_helper_sources(reader, manifest):
    sources = {}
    for _, path in HELPERS:
        data = reader.current(path)
        expected = manifest["trusted_pure_helpers"][path]
        require(digest(data) == expected and digest(reader.blob(Q7, path)) == expected,
                f"Pure helper differs from frozen Q7: {path}")
        sources[path] = data
    return VerifiedHelperSources(reader.root, MappingProxyType(sources),
                                 MappingProxyType(dict(manifest["trusted_pure_helpers"])))


def verify_processes(audit: dict, artifacts: Mapping[str, bytes], helpers: dict,
                     inventory: dict, links: list[str], endpoints: list[str]) -> None:
    a = helpers["audit_chapter7"]
    query = a.generate_query(inventory["modules"], links, endpoints).encode()
    require(artifacts[AUDIT.removesuffix(".json") + ".lean"] == query
            and audit["query_sha256"] == digest(query), "Capped/rewritten historical census query")
    lean = ["lake", "env", "lean", "-j1", "-DwarningAsError=true",
            "-DautoImplicit=false", "-DrelaxedAutoImplicit=false"]
    stages = {"historical-imports": "historical_imports_run", "build-gate": "cached_strict_build_gate",
              "expected-types": "expected_types_run", "kernel": "kernel_run"}
    for suffix, key in stages.items():
        base = AUDIT.removesuffix(".json")
        record = json_object(artifacts[f"{base}.{suffix}-run.json"], suffix)
        raw = artifacts[f"{base}.{suffix}.log"]
        require(record == audit.get(key) and type(record.get("exit_code")) is int
                and record["exit_code"] == 0 and record.get("stdout_stderr_sha256") == digest(raw),
                f"Historical {suffix} raw process evidence differs")
        command = record.get("command")
        require(isinstance(command, list) and all(isinstance(x, str) for x in command),
                f"Invalid {suffix} command")
        if suffix == "build-gate":
            valid = command == ["lake", "--wfail", "--no-build", "--no-cache", "build", "BC4lean"]
        elif suffix == "historical-imports":
            valid = len(command) == 3 and command[1:] == ["-B", "scripts/check_project_imports.py"] \
                and re.fullmatch(r"python(?:3(?:\.\d+)?)?(?:\.exe)?", Path(command[0]).name)
        else:
            expected_path = FIXTURE if suffix == "expected-types" else "audit.lean"
            valid = len(command) == len(lean) + 1 and command[:-1] == lean \
                and (command[-1] == expected_path or command[-1].endswith("/" + expected_path))
            if suffix == "kernel":
                valid = valid and record.get("query_sha256") == digest(query)
        require(bool(valid), f"Historical {suffix} command weakened/rewritten")
    expected = audit["expected_types_run"]
    require(expected.get("fixture") == FIXTURE
            and expected.get("source_sha256") == audit["source_sha256"][FIXTURE],
            "Historical fixture binding differs")
    parsed = a.parse_kernel_evidence(artifacts["docs/audits/chapter7/audit.kernel.log"].decode(),
                                     inventory["modules"], links, endpoints)
    require(all(audit.get(k) == v for k, v in parsed.items()),
            "Historical raw kernel census differs from recorded audit")
    require(parsed["declaration_count"] == 2491 and len(parsed["linked_declarations"]) == 117
            and len(parsed["endpoint_declarations"]) == 117 and set(parsed["axioms"]) == ALLOWED,
            "Historical declaration/link/endpoint/axiom counts differ")


def utc(value: str):
    try:
        parsed = datetime.fromisoformat(value)
    except (ValueError, TypeError) as error:
        raise Rejected("Invalid historical run time") from error
    require(parsed.tzinfo is not None and parsed.utcoffset().total_seconds() == 0,
            "Historical run time lacks UTC offset")
    return parsed


def verify_build(build: dict, raw: bytes, modules: list[str], original_inputs: dict,
                 source_texts: dict[str, str], code_only) -> None:
    require(build.get("status") == "passed" and build.get("sources_unchanged_during_build") is True
            and build.get("sequential_leaf_builds") is True
            and build.get("environment") == {"LEAN_NUM_THREADS": "1"},
            "Historical strict build is not successful/sequential/unchanged")
    require(build.get("combined_log_sha256") == digest(raw), "Historical combined build-log hash differs")
    sources = {m: original_inputs[m.replace(".", "/") + ".lean"] for m in modules}
    require(build.get("source_sha256") == sources, "Historical build source map differs")
    runs = build.get("runs")
    require(isinstance(runs, list) and len(runs) == 106, "Historical build does not have 106 runs")
    markers = list(re.finditer(rb"(?m)^COMMAND ([^\n]+)\n", raw))
    require(len(markers) == 106 and markers[0].start() == 0, "Historical build log framing differs")
    previous = utc(build.get("started_utc"))
    targets = []
    for i, (run, marker) in enumerate(zip(runs, markers)):
        command = run.get("command")
        require(isinstance(command, list) and len(command) == 5
                and command[:4] == ["lake", "--wfail", "--no-cache", "build"],
                "Historical leaf/aggregate build command weakened")
        target = command[-1]
        require(isinstance(target, str) and (MODULE.fullmatch(target) is not None or target == "BC4lean"),
                "Invalid historical build target")
        require(type(run.get("exit_code")) is int and run["exit_code"] == 0,
                "Historical build run did not exit zero")
        require(marker.group(1) == json.dumps(command).encode(), "Historical build commands/frame differ")
        segment = raw[marker.end():markers[i + 1].start() if i + 1 < len(markers) else len(raw)]
        require(run.get("stdout_stderr_sha256") == digest(segment),
                "Historical per-run raw build segment differs")
        start, finish = utc(run.get("started_utc")), utc(run.get("finished_utc"))
        require(previous <= start <= finish, "Historical sequential run times overlap/reverse")
        previous = finish
        targets.append(target)
    require(targets[-1] == "BC4lean" and len(set(targets[:-1])) == 105
            and set(targets[:-1]) == set(modules) and utc(build.get("finished_utc")) >= previous,
            "Historical 105-leaf/final aggregate inventory differs")
    positions = {module: i for i, module in enumerate(targets[:-1])}
    edges = 0
    for module, text in source_texts.items():
        deps = re.findall(r"(?m)^\s*import\s+(BC4lean(?:\.[\w']+)+)\s*$", code_only(text))
        for dep in set(deps) & set(modules):
            require(positions[dep] < positions[module], "Historical build order violates a native source dependency")
            edges += 1
    order = build.get("order_validation", {})
    require(order.get("status") == "verified_actual_source_order_only" and order.get("module_count") == 105
            and order.get("internal_dependency_edges") == edges == 184
            and order.get("inventory_sha256") == original_inputs[INVENTORY]
            and order.get("aggregate_sha256") == original_inputs[AGGREGATE]
            and order.get("frozen_prefix_sha256") == original_inputs[BASE6],
            "Historical source-order validation differs")


def verify_extensions(aggregate: bytes, frozen: bytes, proof_paths: set[str],
                      historical_paths: set[str], new_modules: list[str]) -> None:
    require(aggregate.startswith(frozen), "Current aggregate rewrites the frozen 930-module prefix")
    require(isinstance(new_modules, list) and len(new_modules) <= MAX_FILES - 930
            and all(isinstance(m, str) and MODULE.fullmatch(m) for m in new_modules)
            and len(new_modules) == len(set(new_modules)),
            "Invalid/duplicate explicit Chapter8 module whitelist")
    historical_modules = {p.removesuffix(".lean").replace("/", ".") for p in historical_paths}
    require(not (set(new_modules) & historical_modules), "New inventory repeats a frozen proof module")
    imports = []
    for line in aggregate[len(frozen):].decode().splitlines():
        content = line.split("--", 1)[0].strip()
        if not content:
            continue
        match = re.fullmatch(r"import (BC4lean(?:\.[A-Za-z_][A-Za-z0-9_]*)+)", content)
        require(match is not None, "Future aggregate extension is not a plain project import")
        imports.append(match[1])
    require(len(imports) == len(set(imports)) and set(imports) == set(new_modules),
            "Future aggregate imports differ from the explicit Chapter8 whitelist")
    expected_paths = historical_paths | {m.replace(".", "/") + ".lean" for m in new_modules}
    require(proof_paths == expected_paths, "Current proof files differ from frozen930 plus explicit new inventory")


def parse_canonical_dot(source: str) -> tuple[list[tuple[str, dict]], list[dict]]:
    """Fully consume a strict subset of generated DOT, never partial regex matches.

    Quoted/bare IDs, comments, numeric values, node/default/edge statements,
    graph assignments and subgraphs are parsed. Multiple attribute lists,
    ports, HTML IDs and unsupported syntax are rejected rather than skipped.
    The actual pinned Q7 document graph is accepted by this finite grammar.
    """
    require(len(source.encode()) <= MAX_FILE, "DOT source exceeds file budget")
    tokens, pos = [], 0
    bare = re.compile(r'[A-Za-z_\x80-\uffff][A-Za-z0-9_\x80-\uffff]*|-?(?:\.[0-9]+|[0-9]+(?:\.[0-9]*)?)')
    while pos < len(source):
        if source[pos].isspace(): pos += 1; continue
        if source.startswith('//', pos) or source[pos] == '#':
            end = source.find('\n', pos)
            pos = len(source) if end < 0 else end + 1
            continue
        if source.startswith('/*', pos):
            end = source.find('*/', pos + 2)
            require(end >= 0, "Unterminated DOT comment")
            pos = end + 2
            continue
        if source[pos] == '"':
            pos += 1
            value = []
            while pos < len(source) and source[pos] != '"':
                char = source[pos]
                if char == '\\':
                    require(pos + 1 < len(source), "Unterminated DOT quoted escape")
                    following = source[pos + 1]
                    if following == '\n': pos += 2; continue
                    value.append(following if following in {'"', '\\'} else '\\' + following)
                    pos += 2
                else:
                    require(char not in {'\n', '\r'}, "Unescaped DOT quoted newline")
                    value.append(char); pos += 1
            require(pos < len(source), "Unterminated DOT quoted ID")
            tokens.append(('id', ''.join(value), True)); pos += 1
        elif source.startswith('->', pos):
            tokens.append(('->', '->', False)); pos += 2
        elif source[pos] in '{}[];,=':
            char = source[pos]; tokens.append((char, char, False)); pos += 1
        else:
            match = bare.match(source, pos)
            require(match is not None, "Unsupported/unconsumed DOT token")
            tokens.append(('id', match[0], False)); pos = match.end()
        require(len(tokens) <= 200000, "DOT token count exceeds budget")
    index, nodes, defaults, statements = 0, [], [], 0
    def peek(kind=None):
        return index < len(tokens) and (kind is None or tokens[index][0] == kind)
    def take(kind):
        nonlocal index
        require(peek(kind), f"Expected canonical DOT token {kind}")
        value = tokens[index]; index += 1; return value
    def identifier():
        token = take('id')
        require('\\' not in token[1], "Escaped DOT identifier outside canonical generated subset")
        return token
    def attrs():
        result = {}
        if not peek('['): return result
        take('[')
        while not peek(']'):
            key = take('id')[1]
            require(key == key.lower() and key not in result, "Duplicate/noncanonical graph attribute")
            take('='); value = take('id')[1]
            result[key] = value
            if peek(',') or peek(';'): index_token = tokens[index][0]; take(index_token)
            elif not peek(']'):
                require(peek('id'), "Unparsed DOT attribute syntax")
        take(']')
        require(not peek('['), "Noncanonical multiple DOT attribute lists")
        return result
    def body(depth=0):
        nonlocal statements
        require(depth <= 32, "DOT subgraph nesting exceeds budget")
        take('{')
        while not peek('}'):
            require(peek(), "Unterminated DOT graph")
            if peek(';'): take(';'); continue
            statements += 1
            require(statements <= 8192, "DOT statement count exceeds budget")
            if peek('{'):
                body(depth + 1)
                if peek(';'): take(';')
                continue
            first = identifier()
            if not first[2] and first[1].lower() == 'subgraph':
                if peek('id'): identifier()
                body(depth + 1)
                if peek(';'): take(';')
                continue
            if not first[2] and first[1].lower() in {'node', 'edge', 'graph'} and peek('['):
                attributes = attrs()
                if first[1].lower() == 'node': defaults.append(attributes)
            elif peek('='):
                take('='); take('id')
            elif peek('->'):
                while peek('->'):
                    take('->'); identifier()
                attrs()
            else:
                nodes.append((first[1], attrs()))
            take(';')
        take('}')
    if peek('id') and not tokens[index][2] and tokens[index][1].lower() == 'strict': take('id')
    graph = take('id')
    require(not graph[2] and graph[1].lower() == 'digraph', "Expected a complete directed DOT graph")
    if peek('id'): identifier()
    body()
    require(index == len(tokens), "Unconsumed syntax after DOT graph")
    return nodes, defaults


def verify_pending_graph(html: str) -> None:
    # This is a JavaScript template argument before it is DOT. In the actual
    # pinned generated pages the sole backslash escape is benign identity
    # escape \N in the default label; the browser cooks it to N. Reject all
    # other escapes/interpolation instead of analyzing raw bytes as cooked DOT.
    require(len(re.findall(r"\brenderDot\b", html)) == 1,
            "Expected exactly one literal renderDot call")
    dots = re.findall(r"\.renderDot\s*\(\s*`([^`]*)`\s*\)", html, re.S)
    require(len(dots) == 1, "Expected one complete single-literal JavaScript DOT argument")
    raw = dots[0]
    require('${' not in raw, "JavaScript template interpolation is outside the canonical generated subset")
    cooked, index = [], 0
    while index < len(raw):
        if raw[index] == '\\':
            require(raw[index:index + 2] == r'\N',
                    "JavaScript template-active escape is outside the canonical generated subset")
            cooked.append('N'); index += 2
        else:
            cooked.append(raw[index]); index += 1
    all_nodes, defaults = parse_canonical_dot(''.join(cooked))
    for attrs in defaults:
        require(set(attrs) <= {"label", "penwidth"}
                and ("label" not in attrs or attrs["label"] == "N")
                and ("penwidth" not in attrs or re.fullmatch(r"[0-9]+(?:\.[0-9]+)?", attrs["penwidth"])),
                "Unsafe inherited node defaults for pending conjecture")
    nodes = [attrs for name, attrs in all_nodes if name == 'conj:baum-connes']
    require(len(nodes) == 1, "Missing/duplicate actual general-conjecture graph node")
    attrs = nodes[0]
    require(set(attrs) == {"color", "label", "shape"} and bool(attrs["label"])
            and attrs["color"].casefold() == "#ffaa33" and attrs["shape"] == "ellipse",
            "General conjecture falsely rendered as checked or outside positive pending profile")


@dataclass(frozen=True)
class ValidatedChapter7:
    """Explicit retained data provider for a NEW Chapter8 publication route."""
    audit: dict
    locations: dict[str, tuple[str, int]]
    audit_sha256: str
    receipt: dict
    helpers: VerifiedHelperSources
    frozen_finder_block: str


def validate(reader, manifest: dict, new_modules: list[str] | None = None) -> ValidatedChapter7:
    load_manifest((json.dumps(manifest, indent=2) + "\n").encode())
    prototype_source_sha256 = digest(Path(__file__).read_bytes())
    new_modules = [] if new_modules is None else new_modules
    head = reader.head()
    require(REV.fullmatch(head) is not None and reader.ancestor(S7, Q7) and reader.ancestor(Q7, head),
            "Current source revision does not descend from the exact verified Q7/S7")
    proof_map = manifest["proof_sources"]
    original_inputs = manifest["original_inputs"]
    artifacts_map = manifest["canonical_artifacts"]
    reader.prefetch(Q7, [*proof_map, *artifacts_map, *manifest["trusted_pure_helpers"], FINDER, AGGREGATE])
    reader.prefetch(S7, list(original_inputs))
    require(reader.proof_paths(Q7) == set(proof_map), "Frozen Q7 proof-file inventory differs")
    for path, sha in proof_map.items():
        require(digest(reader.blob(Q7, path)) == sha and digest(reader.current(path)) == sha,
                f"Frozen930 current/Git proof source differs: {path}")
    artifacts = {}
    for path, sha in artifacts_map.items():
        current, original = reader.current(path), reader.blob(Q7, path)
        require(digest(current) == sha and current == original,
                f"Canonical Q7 audit/completion artifact differs: {path}")
        artifacts[path] = current
    for path, sha in original_inputs.items():
        require(digest(reader.blob(S7, path)) == sha, f"Original S7 source binding differs: {path}")
        if path not in EXCEPTIONS:
            require(digest(reader.current(path)) == sha, f"Unapproved current historical input changed: {path}")
    current_exception_hashes = {path: digest(reader.current(path)) for path in sorted(EXCEPTIONS)}
    # All trusted Python source is checked before any of it is executed.
    for path, sha in manifest["trusted_pure_helpers"].items():
        require(digest(reader.current(path)) == sha and digest(reader.blob(Q7, path)) == sha,
                f"Changed trusted helper source: {path}")
    helper_sources = verified_helper_sources(reader, manifest)
    with helper_sources.open() as helpers:
        a = helpers["audit_chapter7"]
        f = helpers["update_chapter7_finder"]
        inventory = a.load_inventory(Path(INVENTORY), reader.current(INVENTORY))
        audit = json_object(artifacts[AUDIT], AUDIT)
        require(audit.get("schema_version") == 1 and audit.get("status") == "verified_complete"
                and audit.get("chapter_complete") is True and audit.get("milestone_verified") is True
                and audit.get("source_revision") == S7 and audit.get("module_sources_match_revision") is True
                and audit.get("inputs_unchanged_during_audit") is True,
                "Canonical audit is not unchanged-input verified-complete evidence at S7")
        require(audit.get("source_sha256") == original_inputs and len(audit["source_sha256"]) == 145,
                "Original 145-input bindings differ from canonical manifest")
        modules = inventory["modules"]
        require(len(modules) == 105 and audit.get("modules") == modules
                and audit.get("source_modules") == sorted(modules + inventory["additional_source_modules"]),
                "Retained105 module/source census differs")
        links, targets, milestones = a.audit_blueprint(reader.current(TEX7).decode(), inventory)
        require(len(links) == 117 and audit.get("blueprint_links") == links
                and audit.get("target_inventory") == targets and len(targets) == 5
                and audit.get("milestone_inventory") == milestones
                and all(item["ready"] for item in [*targets.values(), *milestones.values()])
                and audit.get("notready_targets") == []
                and a.pending_blueprint_targets(reader.current(TEX7).decode()) == [],
                "Original Chapter7 endpoints/readiness/links differ")
        endpoints = sorted({name for item in [*inventory["targets"].values(), *inventory["milestones"].values()]
                            for name in item["required_declarations"]})
        verify_processes(audit, artifacts, helpers, inventory, links, endpoints)
        texts = {module: reader.current(module.replace(".", "/") + ".lean").decode() for module in modules}
        require(audit.get("private_declaration_counts") == a.check_private_coverage(texts, audit["declarations"]),
                "Retained private declaration coverage differs")
        fixture = reader.current(FIXTURE)
        require(len(re.findall(r"(?m)^example\b", a.code_only(fixture.decode()))) == 55,
                "Retained independent fixture no longer has its 55 signatures")
        objects = audit.get("module_olean_sha256")
        expected_objects = {".lake/build/lib/lean/" + m.replace(".", "/") + ".olean" for m in audit["source_modules"]}
        require(isinstance(objects, dict) and expected_objects <= set(objects)
                and all((p in expected_objects or p.removesuffix(".private") in expected_objects)
                        and isinstance(sha, str) and SHA.fullmatch(sha) for p, sha in objects.items()),
                "Historical compiled-object provenance is incomplete/invalid")
        frozen = reader.blob(Q7, AGGREGATE)
        require(digest(frozen) == original_inputs[AGGREGATE], "Frozen930 aggregate binding differs")
        a.check_scope_coverage(frozen, reader.current(BASE6), modules)
        require(len(re.findall(rb"(?m)^import BC4lean\.", frozen)) == 930,
                "Frozen aggregate does not contain930 library imports")
        verify_build(json_object(artifacts[BUILD], BUILD), artifacts["docs/audits/chapter7/build.log"],
                     modules, original_inputs, texts, a.code_only)
        verify_extensions(reader.current(AGGREGATE), frozen, reader.proof_paths(), set(proof_map), new_modules)
        for module in new_modules:
            text = reader.current(module.replace(".", "/") + ".lean").decode()
            a.check_proof_tokens(text, module)
            a.check_strict_options(text, module)
            a.check_no_environment_patches(text, module)
        locations = {}
        source_commands = {}
        for name in links:
            module = audit["linked_declarations"][name]["module"]
            require(MODULE.fullmatch(module) is not None, "Invalid retained declaration origin")
            path = module.replace(".", "/") + ".lean"
            source = reader.current(path)
            require(digest(source) == original_inputs.get(path) and source == reader.blob(S7, path),
                    f"Linked declaration differs from audited S7: {name}")
            if module not in source_commands:
                source_commands[module] = f.declaration_lines(f.code_only(source.decode()))
            require(name in source_commands[module], f"Missing exact explicit declaration command: {name}")
            locations[name] = (path, source_commands[module][name])
        current_finder = reader.current(FINDER).decode()
        original_finder = reader.blob(Q7, FINDER).decode()
        current_blocks, original_blocks = f.BLOCK.findall(current_finder), f.BLOCK.findall(original_finder)
        require(len(current_blocks) == len(original_blocks) == 1 and current_blocks == original_blocks,
                "Frozen S7 finder block changed/duplicated")
        f.verify_html(current_finder, locations, S7, digest(artifacts[AUDIT]))
        scope_tex = reader.current(TEX8)
        homepage_source = reader.current("home_page/index.md")
        scope = helpers["check_chapter7_website"].validate_general_conjecture_scope(
            scope_tex.decode(), homepage_source.decode())
        reader.stable()
        require(reader.head() == head, "Source HEAD changed during preservation check")
        require(digest(Path(__file__).read_bytes()) == prototype_source_sha256,
                "Prototype code changed during check")
        receipt = {"schema": "chapter7.retained.preservation.prototype.v1",
                   "status": "verified_q7_baseline_preservation_only" if not new_modules else "verified_q7_preservation_and_registered_import_extension_only",
                   "chapter8_native_verification_performed": False, "chapter8_complete": False,
                   "new_native_chapter7_census_performed": False,
                   "publication_verified": False, "source_revision_s7": S7,
                   "checked_utc": datetime.now(timezone.utc).isoformat(),
                   "prototype_source_sha256": prototype_source_sha256,
                   "publication_revision_q7": Q7, "current_head": head,
                   "baseline_manifest_sha256": MANIFEST_SHA, "proof_sources_preserved": 930,
                   "original_input_bindings": 145, "canonical_artifacts_preserved": 21,
                   "historical_declarations": 2491, "historical_exact_links": 117,
                   "historical_independent_signatures": 55, "historical_strict_build_runs": 106,
                   "historical_axioms": sorted(ALLOWED), "source_finder_revision": S7,
                   "audit_sha256": digest(artifacts[AUDIT]), "build_sha256": digest(artifacts[BUILD]),
                   "explicit_current_control_exceptions": sorted(EXCEPTIONS),
                   "current_control_exception_sha256": current_exception_hashes,
                   "current_aggregate_sha256": digest(reader.current(AGGREGATE)),
                   "current_chapter8_scope_source_sha256": digest(scope_tex),
                   "current_homepage_source_sha256": digest(homepage_source),
                   "registered_future_modules": sorted(new_modules), "current_general_conjecture_scope": scope}
        return ValidatedChapter7(audit, locations, digest(artifacts[AUDIT]), receipt, helper_sources, original_blocks[0])


def _verify_published_finder(html: str, validated: ValidatedChapter7, helpers: dict) -> None:
    """New explicit provider API; old load_audit/load_locations are not called."""
    f = helpers["update_chapter7_finder"]
    require(f.BLOCK.findall(html) == [validated.frozen_finder_block],
            "Published frozen S7 finder block changed/duplicated")
    f.verify_html(
        html, validated.locations, S7, validated.audit_sha256)


def verify_published_finder(html: str, validated: ValidatedChapter7) -> None:
    with validated.helpers.open() as helpers:
        _verify_published_finder(html, validated, helpers)


def verify_published_chapter7(output: Path, tex7: str, current_tex8: str,
                              homepage_html: str, finder_html: str,
                              validated: ValidatedChapter7) -> dict:
    """Publication integration prototype, not invoked by baseline CLI.

    Chapter8's new site entrypoint must first run unchanged check_website.check_site
    for Chapters5/6 and clean deployment HEAD, then call this explicit retained
    provider, then validate Chapter8's own native endpoints/source/rendered nodes.
    No old current-snapshot Chapter7 site entrypoint is invoked or suppressed.
    """
    with validated.helpers.open() as helpers:
        require(digest(tex7.encode()) == validated.audit["source_sha256"][TEX7],
                "Published Chapter7 source differs from frozen audited source")
        require(digest(current_tex8.encode()) == validated.receipt["current_chapter8_scope_source_sha256"],
                "Current Chapter8 scope source changed since preservation check")
        _verify_published_finder(finder_html, validated, helpers)
        c = helpers["check_chapter7_website"]
        result = c.validate_rendered_chapter7(output, tex7, validated.audit)
        scope = c.validate_general_conjecture_scope(current_tex8, homepage_html)
        homepage = c.Page(homepage_html)
        require("Chapter 7 is verified." in homepage.text
                and "Chapter 7 has verified foundations; the assembly map remains incomplete." not in homepage.text,
                "Homepage lacks precise preserved Chapter7 completion status")
        from urllib.parse import unquote, urlsplit
        pages = {}
        for filename in ("ch-assembly-map.html", "dep_graph_chapter_7.html", "dep_graph_document.html"):
            path = output / filename
            require(path.resolve(strict=True).is_relative_to(output.resolve(strict=True))
                    and path.is_file() and path.stat().st_size <= MAX_FILE,
                    f"Missing/unsafe/oversized Chapter7 rendered page: {filename}")
            raw = path.read_bytes()
            seen = set()
            for href in c.Page(raw.decode()).links:
                target = urlsplit(href)
                fragment = unquote(target.fragment)
                if fragment.startswith("doc/") and fragment[4:] in validated.locations:
                    require((target.scheme, target.netloc, target.path) == (
                        "https", "ylsong1024.github.io", "/BC4lean/docs/find/"),
                        "Incorrect preserved Chapter7 source-link destination")
                    seen.add(fragment[4:])
            require(seen == set(validated.locations), "Rendered Chapter7 page has incomplete declaration links")
            pages[filename] = {"sha256": digest(raw), "bytes": len(raw)}
        for filename in ("dep_graph_chapter_8.html", "dep_graph_document.html"):
            path = output / filename
            require(path.resolve(strict=True).is_relative_to(output.resolve(strict=True))
                    and path.is_file() and path.stat().st_size <= MAX_FILE,
                    f"Missing/oversized actual graph: {filename}")
            verify_pending_graph(path.read_text())
        return {"chapter7_retained_rendered_checks": result, "current_general_conjecture_scope": scope,
                "chapter7_rendered_pages": pages,
                "chapter8_native_verification_performed_by_this_function": False}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--new-inventory", help="Explicit current project-relative Chapter8 inventory; none means Q7 baseline only")
    parser.add_argument("--output", type=Path, required=True, help="Outside-repository prototype receipt")
    args = parser.parse_args()
    root = args.root.resolve(strict=True)
    output = args.output.resolve()
    require(not output.is_relative_to(root), "Prototype may not write repository evidence")
    require(not output.exists(), "Prototype receipt path already exists; use a fresh outside path")
    manifest = load_manifest(MANIFEST_PATH.read_bytes())
    reader = RepositoryReader(root)
    modules = []
    if args.new_inventory:
        inventory = json_object(reader.current(safe_path(args.new_inventory)), "new Chapter8 inventory")
        require(inventory.get("schema_version") == 1 and isinstance(inventory.get("modules"), list)
                and bool(inventory["modules"]), "New inventory needs a finite nonempty module list")
        modules = inventory["modules"]
    value = validate(reader, manifest, modules)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(value.receipt, indent=2) + "\n")
    print(json.dumps({"status": value.receipt["status"], "receipt": str(output),
                      "sha256": digest(output.read_bytes())}))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (Rejected, OSError, UnicodeError, KeyError, TypeError, RuntimeError,
            subprocess.TimeoutExpired) as error:
        print(f"Rejected retained Chapter7 prototype check: {error}", file=sys.stderr)
        raise SystemExit(1)
