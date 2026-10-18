#!/usr/bin/env python3
"""Check the project's explicit import list without changing its order.

BC4lean.lean is an aggregator: one `import BC4lean.Module` per line,
with optional blank lines or line comments. Every .lean file under BC4lean/
must appear exactly once. This is a coverage check, not a Lean parser or proof audit.
"""
from collections import Counter
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import runpy
import sys


def check(root: Path) -> list[str]:
    expected = {
        ".".join(path.relative_to(root).with_suffix("").parts)
        for path in (root / "BC4lean").rglob("*.lean")
    }
    errors = []
    if not expected:
        errors.append("No Lean modules found under BC4lean/.")
    imports = []
    for number, line in enumerate((root / "BC4lean.lean").read_text(encoding="utf-8").splitlines(), 1):
        line = line.split("--", 1)[0].strip()
        if not line:
            continue
        match = re.fullmatch(r"import (BC4lean(?:\.[A-Za-z_][A-Za-z0-9_]*)+)", line)
        if not match:
            errors.append(f"BC4lean.lean:{number}: expected one plain project import.")
        else:
            imports.append(match.group(1))
    counts = Counter(imports)
    errors.extend(f"Missing import: {name}" for name in sorted(expected - counts.keys()))
    errors.extend(f"Import has no source file: {name}" for name in sorted(counts.keys() - expected))
    errors.extend(f"Duplicate import: {name}" for name, n in sorted(counts.items()) if n > 1)
    return errors


def check_chapter5_core_evidence(root: Path) -> list[str]:
    """Check the retained core snapshot, without rerunning Lean or claiming supplemental acceptance.

    Only the 817-entry core Source map is a current-file snapshot. Historical
    object, import-check and blueprint-render records remain historical; in
    particular, the verification document and these two CI entrypoints are not
    in that map. Absolute paths in the original run record are provenance only.
    """
    root = root.resolve()

    def require(condition: bool, message: str) -> None:
        if not condition:
            raise ValueError(message)

    def read(relative: str) -> bytes:
        path = PurePosixPath(relative)
        require(not path.is_absolute() and path.parts and ".." not in path.parts,
                f"Unsafe retained artifact path: {relative}")
        local = root / relative
        require(local.resolve().is_relative_to(root), f"Artifact leaves the checkout: {relative}")
        return local.read_bytes()

    def digest(data: bytes) -> str:
        return hashlib.sha256(data).hexdigest()

    try:
        evidence_bytes = read("docs/audits/chapter5/core-evidence.json")
        require(digest(evidence_bytes) == "c50c13c2df9747c6e6eb9ed08c2a5856aa9c467e1ecb658880bded5c51d46b09",
                "Retained core-evidence.json changed; qualify and bind a new core snapshot first.")
        evidence = json.loads(evidence_bytes)
        require(evidence["schema"] == "chapter5.core.complete-ready.actual-evidence.v1",
                "Unknown retained core-evidence schema.")
        paths = {
            "core_audit": "docs/audits/chapter5/core-audit.json",
            "kernel_source": "docs/audits/chapter5/Chapter5Audit.lean",
            "kernel_log": "docs/audits/chapter5/kernel-stdout-stderr.log",
            "kernel_run": "docs/audits/chapter5/kernel-run.json",
        }
        require(set(evidence["artifacts"]) == set(paths), "Retained core artifact inventory differs.")
        contents = {}
        for kind, relative in paths.items():
            require(evidence["artifacts"][kind]["path"] == relative,
                    f"Unexpected committed artifact path for {kind}.")
            contents[kind] = read(relative)
        audit = json.loads(contents["core_audit"])
        run = json.loads(contents["kernel_run"])
        require(type(run["exit_code"]) is int and run["exit_code"] == 0,
                "Retained raw kernel run did not exit 0.")
        require(audit["chapter_complete"] is True and audit["notready_targets"] == []
                and audit["forbidden_source_tokens"] == []
                and audit["source_control_and_object_hashes_unchanged_during_kernel_audit"] is True,
                "Retained core audit is incomplete or its original snapshot changed.")
        allowed = {"Classical.choice", "Quot.sound", "propext"}
        require(set(audit["axioms"]) == allowed, "Retained core audit axiom set differs.")
        require(audit["source_sha256"] == evidence["source_sha256"]
                and len(audit["source_sha256"]) == 817,
                "Retained 817-entry core Source maps disagree.")
        for relative, expected in audit["source_sha256"].items():
            current = read(relative)
            if relative == "BC4lean.lean" and digest(current) != expected:
                # Later chapters append imports. Preserve the exact historical
                # aggregate as a hash-bound prefix, while checking all present
                # modules separately with check(). No Chapter 5 Lean source or
                # historical proof certificate is changed by this extension.
                original = read("docs/audits/chapter6/Chapter5Imports.lean")
                require(digest(original) == expected,
                        "Historical Chapter 5 aggregate prefix has the wrong hash.")
                require(current.startswith(original),
                        "The historical Chapter 5 aggregate is not an unchanged prefix.")
                extra = current[len(original):].decode("utf-8")
                for line in extra.splitlines():
                    line = line.split("--", 1)[0].strip()
                    if not line:
                        continue
                    match = re.fullmatch(r"import (BC4lean(?:\.[A-Za-z_][A-Za-z0-9_]*)+)", line)
                    require(match is not None, "Later aggregate extension is not a plain import.")
                    source = match[1].replace(".", "/") + ".lean"
                    require(source not in audit["source_sha256"],
                            f"Later aggregate extension repeats an audited module: {source}")
                require(not check(root), "Extended aggregate fails complete module coverage.")
            else:
                require(digest(current) == expected, f"Stale core Source hash: {relative}")

        # This already byte-bound audit module is loaded only for its pure parser.
        parser = runpy.run_path(str(root / "scripts/audit_chapter5.py"))
        declarations, links, axioms, counts = parser["parse_kernel_evidence"](
            contents["kernel_log"].decode("utf-8"), audit["linked_declarations"], audit["modules"])
        require(sorted(declarations, key=lambda row: row["name"]) == audit["declarations"]
                and links == audit["linked_declaration_axioms"]
                and axioms == allowed and counts == audit["module_declaration_counts"],
                "Retained raw kernel declaration/axiom evidence disagrees with the core audit.")
        ready = evidence["complete_ready_kernel"]
        require(type(ready["actual_exit_code"]) is int and ready["actual_exit_code"] == 0
                and ready["chapter_complete"] is True and ready["pending_targets"] == []
                and ready["declaration_count"] == audit["declaration_count"] == len(declarations) == 18199
                and ready["blueprint_link_count"] == len(links) == 435
                and ready["module_origin_closure_count"] == len(counts) == 686
                and set(ready["axioms"]) == allowed,
                "Retained complete-ready kernel counts or axioms disagree.")
        require(evidence["project_olean_sha256"] == audit["project_olean_sha256"],
                "Historical object snapshots disagree; this check does not revalidate rebuilt objects.")
        recorded = dict(audit["kernel_evidence"])
        run_ref = recorded.pop("run_record")
        require(recorded == run, "Retained core audit and raw kernel run record disagree.")
        command = run["command"]
        require(command[:-1] == ["lake", "env", "lean", "-j2", "-DwarningAsError=true",
                "-DautoImplicit=false", "-DrelaxedAutoImplicit=false"]
                and PurePosixPath(command[-1]).name == "Chapter5Audit.lean",
                "Retained raw kernel command differs from the strict audited command.")
        require(run_ref["sha256"] == evidence["artifacts"]["kernel_run"]["sha256"]
                and run["generated_source"]["sha256"] == evidence["artifacts"]["kernel_source"]["sha256"]
                and run["stdout_stderr"]["sha256"] == evidence["artifacts"]["kernel_log"]["sha256"],
                "Historical kernel provenance hashes disagree with committed artifacts.")
        for kind, data in contents.items():
            recorded_artifact = evidence["artifacts"][kind]
            require(digest(data) == recorded_artifact["sha256"]
                    and len(data) == recorded_artifact["size_bytes"],
                    f"Retained {kind} artifact hash or size differs.")
        require(audit["cached_strict_build_gate"] == {
            "command": ["lake", "--wfail", "--no-build", "--no-cache", "build", "BC4lean"],
            "exit_code": 0}, "Retained cached strict-build gate differs.")
        builds = evidence["actual_strict_builds"]
        require(len(builds) == 2, "Retained strict/cached build inventory differs.")
        for build, label, options in zip(builds, ["full_strict", "cached_strict"],
                [["--wfail", "build", "BC4lean"],
                 ["--wfail", "--no-build", "--no-cache", "build", "BC4lean"]]):
            require(build["label"] == label and type(build["actual_exit"]) is int
                    and build["actual_exit"] == 0 and build["all809Source_all10controls_held"] is True
                    and PurePosixPath(build["actual_command"][0]).name == "lake"
                    and build["actual_command"][1:] == options,
                    f"Retained {label} build was not the successful strict command.")
        return []
    except (OSError, UnicodeError, ValueError, TypeError, KeyError, IndexError, RuntimeError) as error:
        return [f"Chapter 5 retained core evidence: {error}"]


if __name__ == "__main__":
    project = Path(__file__).resolve().parent.parent
    try:
        problems = check(project) + check_chapter5_core_evidence(project)
    except OSError as error:
        print(error, file=sys.stderr)
        sys.exit(1)
    if problems:
        print("\n".join(problems), file=sys.stderr)
        sys.exit(1)
    print("All BC4lean modules are imported exactly once.")
