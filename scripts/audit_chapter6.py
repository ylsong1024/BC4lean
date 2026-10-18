#!/usr/bin/env python3
"""Audit the finite Chapter 6 module inventory after its strict Lean build.

The inventory fixes mathematical endpoints before readiness is checked. The Lean
query imports only the listed modules and checks every declaration by module
origin, including private/generated declarations, plus every exact blueprint link.
The independent expected-type fixture is also captured and strictly typechecked.
Use --generate-only to prepare the query without invoking Lean or Lake.
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

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
TARGETS = ("def:piece-k-homology", "prop:topological-transition", "def:topological-side")
NAME = re.compile(r"(?:[^\W\d]|_)[\w']*(?:\.(?:[^\W\d]|_)[\w']*)*\Z")


def code_only(text: str) -> str:
    """Blank Lean strings and nested/line comments, keeping token boundaries."""
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth, i = depth + 1, i + 2
                out.append("  ")
            elif text.startswith("-/", i):
                depth, i = depth - 1, i + 2
                out.append("  ")
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif string:
            if text[i] == "\\":
                out.append("  ")
                i += 2
            elif text[i] == '"':
                string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth, i = 1, i + 2
            out.append("  ")
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out.append(" " * (end - i))
            i = end
        elif text[i] == '"':
            string = True
            out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    if depth or string:
        raise ValueError("Unterminated Lean comment or string in audited source")
    return "".join(out)


def tex_code_only(text: str) -> str:
    lines = []
    for line in text.splitlines():
        for i, char in enumerate(line):
            if char == "%" and (len(line[:i]) - len(line[:i].rstrip("\\"))) % 2 == 0:
                line = line[:i]
                break
        lines.append(line)
    return "\n".join(lines)


def names(values: list[str], what: str) -> list[str]:
    if not isinstance(values, list) or not values or any(not isinstance(n, str) for n in values):
        raise ValueError(f"{what} must be a nonempty string list")
    if len(values) != len(set(values)):
        raise ValueError(f"{what} must be nonempty and contain no duplicates")
    if any(not isinstance(n, str) or not NAME.fullmatch(n) or not n.startswith("BC4lean.")
           for n in values):
        raise ValueError(f"{what} needs exact, fully qualified BC4lean names")
    return sorted(values)


def load_inventory(path: Path, captured: bytes | None = None) -> dict:
    inventory = json.loads(path.read_bytes() if captured is None else captured)
    if inventory.get("schema_version") != 1:
        raise ValueError("Unsupported Chapter 6 inventory schema")
    inventory["modules"] = names(inventory.get("modules", []), "Module inventory")
    extra_sources = inventory.get("additional_source_modules", [])
    if not isinstance(extra_sources, list):
        raise ValueError("Additional source modules must be a list")
    inventory["additional_source_modules"] = names(extra_sources, "Additional source modules") if extra_sources else []
    if set(inventory["modules"]) & set(inventory["additional_source_modules"]):
        raise ValueError("Additional source modules must not repeat declaration-scope modules")
    if set(inventory.get("targets", {})) != set(TARGETS):
        raise ValueError("Endpoint inventory must contain exactly the three Chapter 6 targets")
    for label, target in inventory["targets"].items():
        target["required_declarations"] = names(target.get("required_declarations", []),
                                                 f"Endpoints for {label}")
    return inventory


def audit_blueprint(text: str, inventory: dict) -> tuple[list[str], dict]:
    text = tex_code_only(text)

    def links_in(body: str) -> list[str]:
        groups = re.findall(r"\\lean\{([^}]*)\}", body)
        if any(not n.strip() for group in groups for n in group.split(",")):
            raise ValueError("Empty exact blueprint declaration link")
        found = sorted({n.strip() for group in groups for n in group.split(",")})
        if found:
            names(found, "Blueprint links")
        return found

    links, matches = links_in(text), {label: [] for label in TARGETS}
    blocks = re.findall(r"\\begin\{(definition|proposition|theorem|lemma)\}(.*?)"
                        r"\\end\{\1\}", text, re.S)
    for kind, body in blocks:
        for label in re.findall(r"\\label\{([^}]+)\}", body):
            if label in matches:
                matches[label].append((kind, body))
    targets = {}
    for label in TARGETS:
        occurrences = re.findall(r"\\label\{([^}]+)\}", text).count(label)
        if occurrences != 1 or len(matches[label]) != 1:
            raise ValueError(f"Required Chapter 6 target {label!r} occurs {occurrences} times and needs one statement")
        kind, body = matches[label][0]
        pending = bool(re.search(r"\\notready\b", body))
        leanok = bool(re.search(r"\\leanok\b", body))
        actual = links_in(body)
        required = inventory["targets"][label]["required_declarations"]
        missing = sorted(set(required) - set(actual))
        if pending and leanok:
            raise ValueError(f"Target {label} has contradictory readiness markers")
        if not pending and (not leanok or missing):
            raise ValueError(f"Ready target {label} needs \\leanok and its mathematical endpoint links: {missing}")
        targets[label] = {"statement_kind": kind, "notready": pending, "leanok": leanok,
                          "required_declarations": required, "linked_declarations": actual,
                          "missing_required_declarations": missing,
                          "ready": not pending and leanok and not missing}
    return links, targets


def pending_blueprint_targets(text: str) -> list[str]:
    blocks = re.findall(r"\\begin\{(definition|proposition|theorem|lemma)\}(.*?)"
                        r"\\end\{\1\}", tex_code_only(text), re.S)
    return sorted({label for _, body in blocks if re.search(r"\\notready\b", body)
                   for label in (re.findall(r"\\label\{([^}]+)\}", body) or ["<unlabelled>"])})


def generate_query(modules: list[str], links: list[str], endpoints: list[str]) -> str:
    """No namespace/name prefix filter may replace the module-provenance filter."""
    imports = "\n".join(f"import all {module}" for module in modules)
    array = lambda values: "#[" + ", ".join(json.dumps(n) for n in values) + "]"
    return f'''{imports}
import Lean
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env := (← getEnv).setExporting false
  let modules : Array String := {array(modules)}
  let links : Array String := {array(links)}
  let endpoints : Array String := {array(endpoints)}
  let mut declarations : Array (String × Name) := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let origin := env.header.moduleNames[idx]!.toString
      if modules.contains origin then
        if info matches .axiomInfo _ then
          throwError "New axiom declaration {{name}} in {{origin}}"
        declarations := declarations.push (origin, name)
  liftIO <| IO.println "CH6_START|1"
  for (origin, name) in declarations do
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom {{axiomName}} in {{name}}"
    let axiomText := String.intercalate "," (axioms.toList.map Name.toString)
    liftIO <| IO.println s!"CH6_DECL|{{origin}}|{{name.toString}}|{{axiomText}}"
  for text in (links ++ endpoints).toList.eraseDups do
    let name := text.toName
    unless (env.find? name).isSome do
      throwError "Unknown exact blueprint/endpoint declaration {{text}}"
    if endpoints.contains text then
      let some idx := env.getModuleIdxFor? name
        | throwError "Missing imported endpoint origin {{text}}"
      unless modules.contains env.header.moduleNames[idx]!.toString do
        throwError "Required endpoint outside the Chapter 6 declaration scope: {{text}}"
  for text in links do
    let name := text.toName
    let some idx := env.getModuleIdxFor? name
      | throwError "Missing imported origin for blueprint link {{text}}"
    let origin := env.header.moduleNames[idx]!.toString
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom {{axiomName}} in blueprint link {{text}}"
    let axiomText := String.intercalate "," (axioms.toList.map Name.toString)
    liftIO <| IO.println s!"CH6_LINK|{{text}}|{{origin}}|{{axiomText}}"
  for origin in modules do
    let count := (declarations.filter (·.1 == origin)).size
    liftIO <| IO.println s!"CH6_MODULE|{{origin}}|{{count}}"
  liftIO <| IO.println s!"CH6_END|{{declarations.size}}|{{links.size}}"
'''


def parse_kernel_evidence(output: str, modules: list[str], links: list[str]) -> dict:
    declarations, found_links, counts, start, end = {}, {}, {}, 0, None
    for line in output.splitlines():
        if not line.startswith("CH6_"):
            continue
        fields = line.split("|")
        kind = fields[0]
        if kind == "CH6_START" and fields == [kind, "1"] and start == 0 and end is None:
            start = 1
            continue
        if not start or end is not None:
            raise RuntimeError("Kernel evidence outside its unique start/end frame")
        if kind in {"CH6_DECL", "CH6_LINK"} and len(fields) == 4:
            if kind == "CH6_DECL":
                _, module, name, axiom_text = fields
                rows = declarations
                if module not in modules:
                    raise RuntimeError(f"Unexpected declaration origin: {module}")
            else:
                _, name, module, axiom_text = fields
                rows = found_links
            if name in rows:
                raise RuntimeError(f"Duplicate kernel evidence for {name}")
            axioms = axiom_text.split(",") if axiom_text else []
            if len(axioms) != len(set(axioms)) or set(axioms) - ALLOWED_AXIOMS:
                raise RuntimeError(f"Unexpected reported axioms in {name}: {axioms}")
            rows[name] = {"name": name, "module": module, "axioms": sorted(axioms)}
        elif kind == "CH6_MODULE" and len(fields) == 3:
            _, module, count = fields
            if module not in modules or module in counts or not count.isdecimal():
                raise RuntimeError(f"Invalid or duplicate module count: {line}")
            counts[module] = int(count)
        elif kind == "CH6_END" and len(fields) == 3 and all(n.isdecimal() for n in fields[1:]):
            end = tuple(map(int, fields[1:]))
        else:
            raise RuntimeError(f"Malformed or duplicate kernel evidence: {line}")
    if end != (len(declarations), len(links)) or not declarations:
        raise RuntimeError("Missing or inconsistent unique terminal kernel count")
    if set(found_links) != set(links):
        raise RuntimeError("Kernel links differ from the exact blueprint link inventory")
    actual_counts = {m: sum(d["module"] == m for d in declarations.values()) for m in modules}
    if counts != actual_counts or any(n == 0 for n in actual_counts.values()):
        raise RuntimeError("Missing module coverage or inconsistent module declaration counts")
    for name, link in found_links.items():
        if name in declarations and declarations[name] != link:
            raise RuntimeError(f"Inconsistent declaration and link evidence for {name}")
    return {"declarations": sorted(declarations.values(), key=lambda d: d["name"]),
            "declaration_count": len(declarations), "linked_declarations": found_links,
            "module_declaration_counts": counts,
            "axioms": sorted({a for d in [*declarations.values(), *found_links.values()]
                              for a in d["axioms"]})}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_proof_tokens(text: str, label: str) -> None:
    forbidden = re.findall(r"\b(?:sorry|admit|axiom|sorryAx)\b", code_only(text))
    if forbidden:
        raise RuntimeError(f"Forbidden proof tokens in {label}: {forbidden}")


def run_expected_types(fixture: Path, output: Path, source_sha256: str) -> dict:
    """Retain the independent fixture's actual strict process result."""
    if digest(fixture) != source_sha256:
        raise RuntimeError("Expected-type fixture changed before verification")
    command = ["lake", "env", "lean", "-j1", "-DwarningAsError=true",
               "-DautoImplicit=false", "-DrelaxedAutoImplicit=false", str(fixture)]
    result = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            env=os.environ)
    log = output.with_suffix(".expected-types.log")
    log.write_bytes(result.stdout)
    run = {"command": command, "exit_code": result.returncode,
           "fixture": str(fixture.relative_to(ROOT)) if fixture.is_relative_to(ROOT) else str(fixture),
           "source_sha256": source_sha256, "stdout_stderr_sha256": digest(log)}
    output.with_suffix(".expected-types-run.json").write_text(json.dumps(run, indent=2) + "\n")
    if result.returncode:
        raise RuntimeError(f"Expected-type check failed with exit code {result.returncode}; see {log}")
    return run


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", type=Path, default=ROOT / "docs/audits/chapter6/inventory.json")
    parser.add_argument("--output", type=Path,
                        default=ROOT.parent / "chapter6-evidence/chapter6-audit/audit.json")
    parser.add_argument("--generate-only", action="store_true", help="Do not invoke Lean or Lake")
    parser.add_argument("--require-complete", action="store_true")
    args = parser.parse_args()
    inventory_bytes = args.inventory.read_bytes()
    inventory = load_inventory(args.inventory, inventory_bytes)
    chapter = ROOT / "blueprint/src/parts/06-topological-k-homology.tex"
    expected_types = ROOT / "docs/audits/chapter6/ExpectedTypes.lean"
    chapter_bytes = chapter.read_bytes()
    links, targets = audit_blueprint(chapter_bytes.decode(), inventory)
    pending = pending_blueprint_targets(chapter_bytes.decode())
    modules = inventory["modules"]
    sources = {m: ROOT / (m.replace(".", "/") + ".lean") for m in modules}
    missing_sources = [m for m, source in sources.items() if not source.is_file()]
    if missing_sources:
        raise RuntimeError(f"Scoped module sources are missing: {missing_sources}")
    controls = [chapter, args.inventory.resolve(), Path(__file__).resolve(),
                ROOT / "scripts/test_audit_chapter6.py", ROOT / "scripts/check_project_imports.py",
                ROOT / "docs/audits/chapter6/Chapter5Imports.lean", expected_types, ROOT / "lean-toolchain",
                ROOT / "lakefile.toml", ROOT / "lake-manifest.json"]
    # Additional source modules cover exact blueprint origins in older chapters.
    # Lean checks every origin against this finite snapshot after resolving links.
    # It does not reread all historical project sources or repeat their census.
    source_modules = sorted(modules + inventory["additional_source_modules"])
    captured_sources = [ROOT / (m.replace(".", "/") + ".lean") for m in source_modules]
    paths = [*captured_sources, *controls]
    captured = {p: p.read_bytes() for p in paths}
    if captured[chapter] != chapter_bytes or captured[args.inventory.resolve()] != inventory_bytes:
        raise RuntimeError("Blueprint or endpoint inventory changed during input capture")
    for module, source in sources.items():
        check_proof_tokens(captured[source].decode(), module)
    check_proof_tokens(captured[expected_types].decode(), "Expected-type fixture")
    hashes = {str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p):
              hashlib.sha256(data).hexdigest() for p, data in captured.items()}
    args.output = args.output.resolve()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    source = args.output.with_suffix(".lean")
    endpoints = sorted({n for target in inventory["targets"].values()
                        for n in target["required_declarations"]})
    source.write_text(generate_query(modules, links, endpoints))
    evidence = {"scope": "Every declaration with a listed module origin, including private/generated declarations; all exact Chapter 6 blueprint links; independent ExpectedTypes.lean signature checks",
                "modules": modules, "source_modules": source_modules,
                "source_sha256": hashes, "query_sha256": digest(source),
                "target_inventory": targets, "blueprint_links": links,
                "notready_targets": pending, "chapter_complete": False, "status": "generated_only"}
    revision = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if revision.returncode:
        raise RuntimeError("Cannot identify the source revision for audit provenance")
    module_paths = [str(p.relative_to(ROOT)) for p in captured_sources]
    tracked = subprocess.run(["git", "ls-files", "--error-unmatch", "--", *module_paths],
                             cwd=ROOT, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    unchanged = subprocess.run(["git", "diff", "--quiet", "HEAD", "--", *module_paths], cwd=ROOT)
    evidence.update({"source_revision": revision.stdout.strip(),
                     "module_sources_match_revision": tracked.returncode == unchanged.returncode == 0})
    args.output.with_suffix(".inputs.json").write_text(json.dumps(evidence, indent=2) + "\n")
    args.output.write_text(json.dumps(evidence, indent=2) + "\n")
    if args.generate_only:
        print(f"Generated {source}; no Lean checks or completeness claim were made.")
        return 0
    objects = [ROOT / ".lake/build/lib/lean" / (m.replace(".", "/") + ".olean") for m in modules]
    objects += [private for p in objects if (private := Path(str(p) + ".private")).is_file()]
    object_hashes = {str(p.relative_to(ROOT)): digest(p) for p in objects}
    gate_command = ["lake", "--wfail", "--no-build", "--no-cache", "build", *modules]
    gate = subprocess.run(gate_command, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    args.output.with_suffix(".build-gate.log").write_bytes(gate.stdout)
    if gate.returncode:
        raise RuntimeError("Scoped sources need a current strict build; see the retained build-gate log")
    expected_types_run = run_expected_types(expected_types, args.output,
                                            hashes[str(expected_types.relative_to(ROOT))])
    command = ["lake", "env", "lean", "-j1", "-DwarningAsError=true",
               "-DautoImplicit=false", "-DrelaxedAutoImplicit=false", str(source)]
    result = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            env=os.environ)
    log = args.output.with_suffix(".lean.log")
    log.write_bytes(result.stdout)
    run = {"command": command, "exit_code": result.returncode, "query_sha256": digest(source),
           "stdout_stderr_sha256": digest(log)}
    args.output.with_suffix(".kernel-run.json").write_text(json.dumps(run, indent=2) + "\n")
    if result.returncode:
        raise RuntimeError(f"Lean audit failed with exit code {result.returncode}; see {log}")
    evidence.update(parse_kernel_evidence(result.stdout.decode(), modules, links))
    missing_origins = sorted({row["module"] for row in evidence["linked_declarations"].values()
                              if row["module"].replace(".", "/") + ".lean" not in hashes})
    if missing_origins:
        raise RuntimeError("Exact blueprint origins need additional_source_modules entries: " +
                           ", ".join(missing_origins))
    for relative, expected in {**hashes, **object_hashes}.items():
        if digest(ROOT / relative) != expected:
            raise RuntimeError(f"Audit input changed during verification: {relative}")
    complete = all(t["ready"] for t in targets.values()) and not pending
    evidence.update({"status": "verified", "chapter_complete": complete,
                     "module_olean_sha256": object_hashes, "inputs_unchanged_during_audit": True,
                     "cached_strict_build_gate": {"command": gate_command, "exit_code": 0},
                     "expected_types_run": expected_types_run,
                     "kernel_run": run})
    args.output.write_text(json.dumps(evidence, indent=2) + "\n")
    print(f"Audited {evidence['declaration_count']} declarations in {len(modules)} modules and {len(links)} exact links.")
    print("Chapter 6 targets: " + ("complete" if complete else "pending"))
    return 2 if args.require_complete and not complete else 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, RuntimeError, OSError) as error:
        print(f"Chapter 6 audit failed: {error}", file=sys.stderr)
        raise SystemExit(1)
