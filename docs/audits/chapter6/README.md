# Chapter 6 audit

`inventory.json` fixes the finite module scope and the mathematical endpoint
declarations for the three original Chapter 6 statements. Changes to that scope
or to an endpoint require review alongside the Lean statements. A `\leanok`
marker alone cannot satisfy a target. The auditor requires every listed endpoint
to exist, and a ready target must link all its own endpoints exactly.

After the strict project build:

```sh
python3 -B scripts/test_audit_chapter6.py
python3 -B scripts/audit_chapter6.py --require-complete \
  --output ../chapter6-evidence/chapter6-audit/audit.json
```

To inspect the generated query without invoking Lean or Lake:

```sh
python3 -B scripts/audit_chapter6.py --generate-only \
  --output ../chapter6-evidence/chapter6-audit/audit.json
```

The scoped files use Lean’s legacy module format. The generated query imports
each one normally, which retains its private constants, sets the environment
to non-exporting, and enumerates constants by `getModuleIdxFor?`. A format
migration is rejected until the import strategy is adapted. The audit also
requires private-name census evidence for every source declaring private data;
a real compiler probe confirms the private geometric helper is visible.
It calls `Lean.collectAxioms` on every constant whose origin is a scoped module,
including generated declarations and declarations in other namespaces. Imported
dependencies are checked transitively by `collectAxioms`; they are not redundantly
enumerated as Chapter 6 declarations. All exact blueprint links are separately
resolved in the environment and audited. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed, and any new axiom declaration in a scoped module fails.

Evidence consists of source/control hashes, scoped `.olean` hashes, per-module
counts, the complete declaration/axiom census, exact link origins, target status,
the generated query, raw Lean output, the subprocess command and exit code, and
the cached strict-build gate log. The independent `ExpectedTypes.lean` fixture is
source-hash-bound, scanned for forbidden proof tokens, and executed strictly;
its actual exit status and output hash are retained separately. Source and object hashes must remain unchanged
during the audit. `--generate-only` makes no verification or completeness claim.
The full aggregate project build is a separate check.
If a blueprint link resolves to an older project module, list that origin in
`additional_source_modules`. The audit fails unless every resolved link origin
has a captured source hash. These additional origins do not expand the Chapter 6
declaration census. `source_revision` and `module_sources_match_revision` identify
whether all captured source modules match the recorded Git commit, as required
for immutable source links in the website.

A separate Chapter 6 CI workflow can run these Python regression checks, install
the pinned toolchain/cache, build `BC4lean` strictly, then run this audit with
`--require-complete` and upload the evidence directory. Existing Chapter 5 checks
remain unchanged. The explicit inventory avoids rerunning Chapter 5's much larger
declaration census solely to verify Chapter 6.
