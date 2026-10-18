#!/usr/bin/env python3
"""Verify Chapter 7 milestones without treating them as the assembly map.

Run a strict aggregate build first. This audit then checks its current build
trace, strictly checks the independent ExpectedTypes.lean fixture, and asks Lean
for every declaration whose module origin is in the finite inventory. There is
no name-prefix filter, declaration cap, or assumed endpoint. Pending original
targets have no invented endpoint declarations and cannot carry a leanok marker.
--require-complete returns 2 when verified milestones leave the chapter pending.
--generate-only writes inputs/query evidence and makes no verification claim.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from audit_chapter6 import (ALLOWED_AXIOMS, check_legacy_module, check_private_coverage,
                           check_proof_tokens, code_only, digest, names,
                           pending_blueprint_targets, tex_code_only)

ROOT = Path(__file__).resolve().parents[1]
TARGET_KINDS = {
    "def:reduced-descent": "definition",
    "def:cutoff-projection": "definition",
    "def:assembly-piece": "definition",
    "prop:assembly-compatibility": "proposition",
    "def:assembly-map": "definition",
}
TARGETS = tuple(TARGET_KINDS)
LABEL = re.compile(r"[A-Za-z][A-Za-z0-9:_-]*\Z")
CHAPTER6_IMPORTS_SHA256 = "74885bdc52882341eafdcfb324a0748fad2cf47fe2002929e80b44743fb733a2"
CHAPTER6_AUDIT_SHA256 = "8472047b2978a1c749f05ea57d7785529acad0c7522fcf992202b6d6ac104969"


def nonempty_text(value: object, what: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{what} must be nonempty text")
    return value


def load_inventory(path: Path, captured: bytes | None = None) -> dict:
    inventory = json.loads(path.read_bytes() if captured is None else captured)
    if not isinstance(inventory, dict) or inventory.get("schema_version") != 1:
        raise ValueError("Unsupported Chapter 7 inventory schema")
    inventory["modules"] = names(inventory.get("modules", []), "Module inventory")
    additional = inventory.get("additional_source_modules", [])
    if not isinstance(additional, list):
        raise ValueError("Additional source modules must be a list")
    inventory["additional_source_modules"] = names(additional, "Additional source modules") if additional else []
    if set(inventory["modules"]) & set(inventory["additional_source_modules"]):
        raise ValueError("Additional source modules must not repeat census modules")
    targets = inventory.get("targets")
    if not isinstance(targets, dict) or set(targets) != set(TARGETS):
        raise ValueError("Endpoint inventory must contain exactly the five original Chapter 7 targets")
    for label, target in targets.items():
        if not isinstance(target, dict):
            raise ValueError(f"Target {label} must be an object")
        nonempty_text(target.get("description"), f"Description for {label}")
        status = target.get("status")
        if status == "pending":
            if target.get("required_declarations") != []:
                raise ValueError(f"Pending target {label} must not invent required declarations")
            nonempty_text(target.get("blocked_reason"), f"Blocked reason for {label}")
        elif status == "implemented":
            target["required_declarations"] = names(target.get("required_declarations", []),
                                                     f"Endpoints for {label}")
        else:
            raise ValueError(f"Target {label} needs an explicit pending/implemented status")
    milestones = inventory.get("milestones")
    if not isinstance(milestones, dict) or not milestones:
        raise ValueError("Milestone inventory must be a nonempty object")
    for label, milestone in milestones.items():
        if not isinstance(label, str) or not LABEL.fullmatch(label) or label in TARGETS:
            raise ValueError("Milestones need separate exact blueprint labels")
        if not isinstance(milestone, dict):
            raise ValueError(f"Milestone {label} must be an object")
        nonempty_text(milestone.get("description"), f"Description for {label}")
        milestone["required_declarations"] = names(milestone.get("required_declarations", []),
                                                    f"Milestone declarations for {label}")
    return inventory


def audit_blueprint(text: str, inventory: dict) -> tuple[list[str], dict, dict]:
    text = tex_code_only(text)

    def links_in(body: str) -> list[str]:
        groups = re.findall(r"\\lean\{([^}]*)\}", body)
        if any(not n.strip() for group in groups for n in group.split(",")):
            raise ValueError("Empty exact blueprint declaration link")
        found = sorted({n.strip() for group in groups for n in group.split(",")})
        if found:
            names(found, "Blueprint links")
        return found

    expected = {**inventory["targets"], **inventory["milestones"]}
    matches: dict[str, list[tuple[str, str]]] = {label: [] for label in expected}
    blocks = re.findall(r"\\begin\{(definition|proposition|theorem|lemma)\}(.*?)"
                        r"\\end\{\1\}", text, re.S)
    for kind, body in blocks:
        for label in re.findall(r"\\label\{([^}]+)\}", body):
            if label in matches:
                matches[label].append((kind, body))
    results = {}
    labels = re.findall(r"\\label\{([^}]+)\}", text)
    for label, item in expected.items():
        occurrences = labels.count(label)
        if occurrences != 1 or len(matches[label]) != 1:
            raise ValueError(f"Required Chapter 7 label {label!r} occurs {occurrences} times and needs one statement")
        kind, body = matches[label][0]
        if label in TARGET_KINDS and kind != TARGET_KINDS[label]:
            raise ValueError(f"Original target {label} changed its statement kind")
        pending_markers = len(re.findall(r"\\notready\b", body))
        ready_markers = len(re.findall(r"\\leanok\b", body))
        if pending_markers > 1 or ready_markers > 1 or (pending_markers and ready_markers):
            raise ValueError(f"Target {label} has contradictory or repeated readiness markers")
        required = item["required_declarations"]
        actual = links_in(body)
        missing = sorted(set(required) - set(actual))
        is_pending = label in TARGETS and item["status"] == "pending"
        if is_pending:
            if pending_markers != 1 or ready_markers:
                raise ValueError(f"Pending original target {label} must retain \\notready and cannot claim \\leanok")
        elif pending_markers or ready_markers != 1 or missing:
            raise ValueError(f"Implemented target/milestone {label} needs \\leanok and mathematical endpoint links: {missing}")
        results[label] = {"statement_kind": kind, "notready": bool(pending_markers),
                          "leanok": bool(ready_markers), "required_declarations": required,
                          "linked_declarations": actual, "missing_required_declarations": missing,
                          "ready": not is_pending and not pending_markers and ready_markers == 1 and not missing}
        if is_pending:
            results[label]["blocked_reason"] = item["blocked_reason"]
    return (links_in(text), {label: results[label] for label in inventory["targets"]},
            {label: results[label] for label in inventory["milestones"]})


def check_scope_coverage(aggregate: bytes, baseline: bytes, modules: list[str],
                         baseline_sha256: str = CHAPTER6_IMPORTS_SHA256) -> None:
    if hashlib.sha256(baseline).hexdigest() != baseline_sha256:
        raise RuntimeError("Frozen Chapter6Imports.lean has the wrong hash")
    if not aggregate.startswith(baseline):
        raise RuntimeError("Aggregate must preserve the frozen Chapter 6 imports as an unchanged prefix")
    suffix = code_only(aggregate[len(baseline):].decode())
    imports = re.findall(r"(?m)^\s*import\s+(BC4lean(?:\.[\w']+)+)\s*$", suffix)
    residue = re.sub(r"(?m)^\s*import\s+BC4lean(?:\.[\w']+)+\s*$", "", suffix)
    if residue.strip() or len(imports) != len(set(imports)) or set(imports) != set(modules):
        raise RuntimeError("New aggregate imports must exactly cover the Chapter 7 module census, once each")
    historical = set(re.findall(r"(?m)^import\s+(\S+)\s*$", code_only(baseline.decode())))
    if historical & set(modules):
        raise RuntimeError("Chapter 7 census repeats a frozen historical module")


def historical_inputs() -> dict[Path, bytes]:
    """Bind the existing Chapter 6 source snapshot without rewriting its report."""
    report = ROOT / "docs/audits/chapter6/audit.json"
    data = report.read_bytes()
    if hashlib.sha256(data).hexdigest() != CHAPTER6_AUDIT_SHA256:
        raise RuntimeError("Frozen Chapter 6 audit has the wrong hash")
    evidence = json.loads(data)
    if evidence.get("status") != "verified" or evidence.get("chapter_complete") is not True:
        raise RuntimeError("Frozen Chapter 6 evidence is not a completed verified audit")
    captured = {report: data}
    for relative, expected in evidence["source_sha256"].items():
        path = (ROOT / relative).resolve()
        if not path.is_relative_to(ROOT.resolve()):
            raise RuntimeError("Historical source path escapes the project")
        content = path.read_bytes()
        if hashlib.sha256(content).hexdigest() != expected:
            raise RuntimeError(f"Frozen Chapter 6 input changed: {relative}")
        captured[path] = content
    return captured


def check_strict_options(text: str, label: str) -> None:
    if re.search(r"\bset_option\s+(?:(?:autoImplicit|relaxedAutoImplicit|debug\.skipKernelTC)\s+true|warningAsError\s+false)\b",
                 code_only(text)):
        raise RuntimeError(f"Strict verification options weakened in {label}")


def check_no_environment_patches(text: str, label: str) -> None:
    """Keep this mathematical milestone scope free of command/compiler patches.

The census intentionally executes trusted Lean metaprogramming from the frozen
audit helper. Newly audited mathematical modules and the independent fixture
must not export elaborators, initializers, native replacements, or arbitrary
commands that can replace that census or bypass declaration type checking.
"""
    forbidden = re.findall(
        r"\b(?:Lean|unsafe|implemented_by|extern|run_cmd|run_elab|run_meta|run_tac|"
        r"elab|elab_rules|macro|macro_rules|syntax|notation|infix|infixl|infixr|prefix|postfix|"
        r"initialize|builtin_initialize|"
        r"command_elab|builtin_command_elab|term_elab|builtin_term_elab|"
        r"tactic|builtin_tactic|builtin_macro)\b|#(?:eval|run)\b|\b(?:s|m|f)!", code_only(text))
    if forbidden:
        raise RuntimeError(f"Executable environment patches in {label}: {sorted(set(forbidden))}")
    # All project imports are either in the frozen prefix or the exact new
    # module census; Mathlib's source is pinned in the Lake manifest. Do not let
    # an unaudited local import introduce command patches behind this guard.
    for line in code_only(text).splitlines():
        if re.search(r"\bimport\b", line) and not re.fullmatch(
                r"\s*import\s+(?:BC4lean|Mathlib)(?:\.[\w']+)+\s*", line):
            raise RuntimeError(f"Import outside the frozen/project/Mathlib scope in {label}: {line.strip()}")


def generate_query(modules: list[str], links: list[str], endpoints: list[str]) -> str:
    # The original helper already performs the uncapped, private-aware census.
    # Add a separate endpoint record/count so expected declarations have evidence
    # even when linked nowhere outside their milestone statement.
    from audit_chapter6 import generate_query as chapter6_query
    query = chapter6_query(modules, links, endpoints).replace("CH6_", "CH7_").replace("Chapter 6", "Chapter 7")
    old = '  liftIO <| IO.println s!"CH7_END|{declarations.size}|{links.size}"'
    new = '''  for text in endpoints do
    let name := text.toName
    let some idx := env.getModuleIdxFor? name
      | throwError "Missing imported endpoint origin {text}"
    let origin := env.header.moduleNames[idx]!.toString
    let axioms ← collectAxioms name
    let axiomText := String.intercalate "," (axioms.toList.map Name.toString)
    liftIO <| IO.println s!"CH7_ENDPOINT|{text}|{origin}|{axiomText}"
  liftIO <| IO.println s!"CH7_END|{declarations.size}|{links.size}|{endpoints.size}"'''
    if query.count(old) != 1:
        raise RuntimeError("Chapter 6 query helper changed; review Chapter 7 query adaptation")
    query = query.replace(old, new)
    # Imported root-level names must not shadow the trusted census operations.
    return (query.replace("(← getEnv)", "(← Lean.getEnv)")
            .replace("collectAxioms name", "Lean.collectAxioms name")
            .replace("liftIO <|", "Lean.Elab.Command.liftIO <|")
            .replace("(String × Name)", "(String × Lean.Name)")
            .replace("Name.toString", "Lean.Name.toString"))


def parse_kernel_evidence(output: str, modules: list[str], links: list[str], endpoints: list[str]) -> dict:
    declarations: dict[str, dict] = {}
    found_links: dict[str, dict] = {}
    found_endpoints: dict[str, dict] = {}
    counts: dict[str, int] = {}
    start, end = False, None
    for line in output.splitlines():
        if not line.startswith("CH7_"):
            continue
        fields = line.split("|")
        kind = fields[0]
        if fields == ["CH7_START", "1"] and not start and end is None:
            start = True
            continue
        if not start or end is not None:
            raise RuntimeError("Kernel evidence outside its unique start/end frame")
        if kind in {"CH7_DECL", "CH7_LINK", "CH7_ENDPOINT"} and len(fields) == 4:
            if kind == "CH7_DECL":
                _, module, name, axiom_text = fields
                rows = declarations
            else:
                _, name, module, axiom_text = fields
                rows = found_links if kind == "CH7_LINK" else found_endpoints
            if not name or not module or name in rows:
                raise RuntimeError(f"Empty or duplicate kernel evidence: {line}")
            if kind in {"CH7_DECL", "CH7_ENDPOINT"} and module not in modules:
                raise RuntimeError(f"Unexpected declaration/endpoint origin: {module}")
            axioms = axiom_text.split(",") if axiom_text else []
            if len(axioms) != len(set(axioms)) or set(axioms) - ALLOWED_AXIOMS:
                raise RuntimeError(f"Unexpected reported axioms in {name}: {axioms}")
            rows[name] = {"name": name, "module": module, "axioms": sorted(axioms)}
        elif kind == "CH7_MODULE" and len(fields) == 3:
            _, module, count = fields
            if module not in modules or module in counts or not count.isdecimal():
                raise RuntimeError(f"Invalid or duplicate module count: {line}")
            counts[module] = int(count)
        elif kind == "CH7_END" and len(fields) == 4 and all(n.isdecimal() for n in fields[1:]):
            end = tuple(map(int, fields[1:]))
        else:
            raise RuntimeError(f"Malformed or duplicate kernel evidence: {line}")
    if end != (len(declarations), len(links), len(endpoints)) or not declarations:
        raise RuntimeError("Missing or inconsistent unique terminal kernel count")
    if set(found_links) != set(links) or set(found_endpoints) != set(endpoints):
        raise RuntimeError("Kernel links/endpoints differ from their exact inventories")
    actual_counts = {m: sum(d["module"] == m for d in declarations.values()) for m in modules}
    if counts != actual_counts or any(n == 0 for n in actual_counts.values()):
        raise RuntimeError("Missing module coverage or inconsistent module declaration counts")
    for name, row in {**found_links, **found_endpoints}.items():
        if (name in found_endpoints or row["module"] in modules) and declarations.get(name) != row:
            raise RuntimeError(f"Inconsistent or uncensused exact declaration evidence for {name}")
    for name in set(found_links) & set(found_endpoints):
        if found_links[name] != found_endpoints[name]:
            raise RuntimeError(f"Inconsistent link/endpoint evidence for {name}")
    return {"declarations": sorted(declarations.values(), key=lambda d: d["name"]),
            "declaration_count": len(declarations), "linked_declarations": found_links,
            "endpoint_declarations": found_endpoints, "module_declaration_counts": counts,
            "axioms": sorted({a for rows in (declarations, found_links, found_endpoints)
                              for row in rows.values() for a in row["axioms"]})}


def run_process(command: list[str], output: Path, suffix: str, **metadata: object) -> tuple[dict, bytes]:
    result = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            env=os.environ)
    log = output.with_suffix(f".{suffix}.log")
    log.write_bytes(result.stdout)
    record = {"command": command, "exit_code": result.returncode,
              "stdout_stderr_sha256": digest(log), **metadata}
    output.with_suffix(f".{suffix}-run.json").write_text(json.dumps(record, indent=2) + "\n")
    if result.returncode:
        raise RuntimeError(f"{suffix} failed with exit code {result.returncode}; see {log}")
    return record, result.stdout


def run_expected_types(fixture: Path, output: Path, source_sha256: str) -> dict:
    if digest(fixture) != source_sha256:
        raise RuntimeError("Expected-type fixture changed before verification")
    command = ["lake", "env", "lean", "-j1", "-DwarningAsError=true",
               "-DautoImplicit=false", "-DrelaxedAutoImplicit=false", str(fixture)]
    location = str(fixture.relative_to(ROOT)) if fixture.is_relative_to(ROOT) else str(fixture)
    record, _ = run_process(command, output, "expected-types", fixture=location,
                            source_sha256=source_sha256)
    return record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", type=Path, default=ROOT / "docs/audits/chapter7/inventory.json")
    parser.add_argument("--output", type=Path, default=ROOT / "docs/audits/chapter7/audit.json")
    parser.add_argument("--generate-only", action="store_true", help="Do not invoke Lean or Lake")
    parser.add_argument("--require-complete", action="store_true")
    args = parser.parse_args()
    args.inventory, args.output = args.inventory.resolve(), args.output.resolve()
    inventory_bytes = args.inventory.read_bytes()
    inventory = load_inventory(args.inventory, inventory_bytes)
    chapter = ROOT / "blueprint/src/parts/07-assembly-map.tex"
    chapter_bytes = chapter.read_bytes()
    links, targets, milestones = audit_blueprint(chapter_bytes.decode(), inventory)
    pending = pending_blueprint_targets(chapter_bytes.decode())
    modules = inventory["modules"]
    source_modules = sorted(modules + inventory["additional_source_modules"])
    sources = {m: ROOT / (m.replace(".", "/") + ".lean") for m in source_modules}
    fixture = ROOT / "docs/audits/chapter7/ExpectedTypes.lean"
    baseline = ROOT / "docs/audits/chapter7/Chapter6Imports.lean"
    controls = [chapter, args.inventory, fixture, baseline, ROOT / "BC4lean.lean",
                ROOT / "scripts/audit_chapter7.py", ROOT / "scripts/test_audit_chapter7.py",
                ROOT / "scripts/update_chapter7_finder.py", ROOT / "scripts/test_chapter7_publication.py",
                ROOT / "scripts/check_chapter7_website.py", ROOT / "scripts/test_chapter7_website.py",
                ROOT / ".github/workflows/chapter7.yml", ROOT / "lean-toolchain",
                ROOT / "lakefile.toml", ROOT / "lake-manifest.json"]
    captured = historical_inputs()
    captured.update({p: p.read_bytes() for p in [*sources.values(), *controls]})
    if captured[chapter] != chapter_bytes or captured[args.inventory] != inventory_bytes:
        raise RuntimeError("Blueprint or endpoint inventory changed during input capture")
    check_scope_coverage(captured[ROOT / "BC4lean.lean"], captured[baseline], modules)
    for module in modules:
        text = captured[sources[module]].decode()
        check_proof_tokens(text, module)
        check_strict_options(text, module)
        check_no_environment_patches(text, module)
        check_legacy_module(text, module)
    check_proof_tokens(captured[fixture].decode(), "Expected-type fixture")
    check_strict_options(captured[fixture].decode(), "Expected-type fixture")
    check_no_environment_patches(captured[fixture].decode(), "Expected-type fixture")
    hashes = {str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p):
              hashlib.sha256(data).hexdigest() for p, data in captured.items()}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    query = args.output.with_suffix(".lean")
    endpoints = sorted({n for item in [*inventory["targets"].values(), *inventory["milestones"].values()]
                        for n in item["required_declarations"]})
    query.write_text(generate_query(modules, links, endpoints))
    revision = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if revision.returncode:
        raise RuntimeError("Cannot identify the source revision for audit provenance")
    paths = [str(source.relative_to(ROOT)) for source in sources.values()]
    tracked = subprocess.run(["git", "ls-files", "--error-unmatch", "--", *paths], cwd=ROOT,
                             stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    unchanged = subprocess.run(["git", "diff", "--quiet", "HEAD", "--", *paths], cwd=ROOT)
    evidence = {"schema_version": 1, "status": "generated_only", "chapter_complete": False,
                "milestone_verified": False,
                "scope": "Uncapped census of every declaration by listed module origin, including private/generated declarations; all exact Chapter 7 links and real milestone/implemented endpoints; independent ExpectedTypes.lean fixture",
                "modules": modules, "source_modules": source_modules, "source_sha256": hashes,
                "query_sha256": digest(query), "source_revision": revision.stdout.strip(),
                "module_sources_match_revision": tracked.returncode == unchanged.returncode == 0,
                "target_inventory": targets, "milestone_inventory": milestones,
                "blueprint_links": links, "notready_targets": pending}
    args.output.with_suffix(".inputs.json").write_text(json.dumps(evidence, indent=2) + "\n")
    args.output.write_text(json.dumps(evidence, indent=2) + "\n")
    if args.generate_only:
        print(f"Generated {query}; no Lean checks or verification/completeness claim were made.")
        return 0
    try:
        objects = [ROOT / ".lake/build/lib/lean" / (m.replace(".", "/") + ".olean") for m in source_modules]
        objects += [private for path in objects if (private := Path(str(path) + ".private")).is_file()]
        object_hashes = {str(path.relative_to(ROOT)): digest(path) for path in objects}
        historical_gate, _ = run_process([sys.executable, "-B", "scripts/check_project_imports.py"],
                                          args.output, "historical-imports")
        gate_command = ["lake", "--wfail", "--no-build", "--no-cache", "build", "BC4lean"]
        gate, _ = run_process(gate_command, args.output, "build-gate")
        expected_run = run_expected_types(fixture, args.output, hashes[str(fixture.relative_to(ROOT))])
        if digest(query) != evidence["query_sha256"]:
            raise RuntimeError("Generated kernel query changed before verification")
        command = ["lake", "env", "lean", "-j1", "-DwarningAsError=true",
                   "-DautoImplicit=false", "-DrelaxedAutoImplicit=false", str(query)]
        kernel_run, stdout = run_process(command, args.output, "kernel", query_sha256=evidence["query_sha256"])
        evidence.update(parse_kernel_evidence(stdout.decode(), modules, links, endpoints))
        evidence["private_declaration_counts"] = check_private_coverage(
            {m: captured[sources[m]].decode() for m in modules}, evidence["declarations"])
        missing = sorted({row["module"] for row in evidence["linked_declarations"].values()
                          if row["module"].replace(".", "/") + ".lean" not in hashes})
        if missing:
            raise RuntimeError("Exact blueprint origins need additional_source_modules entries: " + ", ".join(missing))
        for relative, expected in {**hashes, **object_hashes}.items():
            if digest(ROOT / relative) != expected:
                raise RuntimeError(f"Audit input changed during verification: {relative}")
        if digest(query) != evidence["query_sha256"]:
            raise RuntimeError("Generated kernel query changed during verification")
        complete = all(item["ready"] for item in targets.values()) and not pending
        evidence.update({"status": "verified_complete" if complete else "verified_milestone",
                         "chapter_complete": complete, "milestone_verified": True,
                         "module_olean_sha256": object_hashes, "inputs_unchanged_during_audit": True,
                         "historical_imports_run": historical_gate, "cached_strict_build_gate": gate,
                         "expected_types_run": expected_run, "kernel_run": kernel_run})
    except (OSError, RuntimeError, ValueError) as error:
        evidence.update({"status": "verification_failed", "milestone_verified": False,
                         "chapter_complete": False, "failure": str(error)})
        args.output.write_text(json.dumps(evidence, indent=2) + "\n")
        raise
    args.output.write_text(json.dumps(evidence, indent=2) + "\n")
    print(f"Audited {evidence['declaration_count']} declarations in {len(modules)} modules, {len(links)} exact links, and {len(endpoints)} real endpoints.")
    print("Chapter 7: " + ("complete" if complete else "verified milestones; original targets remain pending"))
    return 2 if args.require_complete and not complete else 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, RuntimeError, OSError) as error:
        print(f"Chapter 7 audit failed: {error}", file=sys.stderr)
        raise SystemExit(1)
