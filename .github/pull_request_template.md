## What changes?

Explain the problem, the mathematical statement or intended behavior, and the
bounded scope. Link the issue or roadmap task, if applicable.

## Declarations and assumptions

List exact new/changed Lean declarations and relevant blueprint labels.
State hypotheses and any mathematical limitation. For documentation-only work,
write "Not applicable".

## Verification

Give the commands and results actually obtained; explain unchecked items.

- [ ] Relevant pinned Mathlib APIs inspected; dependency pins preserved (or a dedicated upgrade explained).
- [ ] Changed Lean modules compiled individually and `lake --wfail build BC4lean` passed.
- [ ] `python3 scripts/check_project_imports.py` passed.
- [ ] New declarations' `#print axioms` results recorded; no `sorry`, `admit`, or new axioms.
- [ ] Blueprint changes rendered; markers reflect only the statements actually checked.

Mark checks that do not apply as **N/A with a reason**, rather than asserting
that they were run. CI rendering/build success does not replace mathematical review.

## Credit and follow-up

Cite mathematical sources and contributors. Describe remaining work or API
obstructions and any assistance relevant to reviewing the contribution.
