# Contributing to BC4lean

Contributions from mathematicians, Lean developers, writers, and reviewers are
welcome. The scope is the coefficient-free, reduced Baum–Connes conjecture for
countable discrete groups. Use English for mathematical source text and public
technical documentation.

## Choose and coordinate a task

Start with [the roadmap](docs/ROADMAP.md). Search existing issues and PRs, then
open a **Formalization task**, **Build or website problem**, or **Design discussion**
issue. State the exact result, hypotheses, relevant blueprint label, and intended
acceptance checks. For a small typo fix, a PR directly is sufficient.

Comment on an existing task before starting substantial work. A roadmap entry is
a proposal, not an assignment: agreement and progress are recorded in its issue.
Use draft PRs for early feedback. Explain an obstruction rather than replacing a
hard theorem by an easier statement under the same name.

## Work on a branch

Fork the repository on GitHub, clone your fork, and create a branch:

```sh
git switch -c your-task-name
lake exe cache get
```

Use the versions in `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.
Do not upgrade dependencies in an unrelated contribution. Inspect APIs in the
pinned `.lake/packages/mathlib/Mathlib` source before writing replacement code.
Keep each PR focused enough that another person can review the mathematical claim
and its Lean implementation together.

## Verify Lean changes

1. Write the mathematical statement and all hypotheses before the proof. Preserve
   distinctions such as unital/nonunital, reduced/maximal, and hypotheses on
   topological spaces. A conditional result must remain explicitly conditional.
2. Compile each changed module, for example:
   `lake env lean -DwarningAsError=true BC4lean/EquivariantMaps.lean`.
   Build imported changed modules first if their compiled files are out of date.
3. Add new modules to `BC4lean.lean`, with one `import BC4lean.ModuleName` per line.
   Run `python3 scripts/check_project_imports.py` and
   `lake --wfail build BC4lean`.
4. Audit new public declarations with `#print axioms Namespace.declaration` in a
   temporary Lean file importing the relevant module. Include the results in the
   PR. The accepted foundational axioms are `propext`, `Classical.choice`, and
   `Quot.sound`; report anything else as an obstruction.
5. Record exact declaration names and commands, including failures or checks you
   could not run. Remove scratch files and do not commit `.lake` or generated
   build output.

Do not use `sorry`, `admit`, or new axioms to complete a milestone. Do not weaken
its intended mathematical statement to obtain a successful build. A passing
build checks Lean elaboration; it does not by itself certify that the statement
matches the intended mathematics. Review both.

## Keep the blueprint honest

Update the corresponding chapter in `blueprint/src/parts/` when an API or theorem
changes. Link exact declarations using `\lean{...}`. Add `\leanok` only after the
linked declaration has been checked; mark a proof verified only when its full
stated conclusion is proved. Preserve `\notready` for unresolved targets.
Do not mark a universal construction complete because a conditional uniqueness
lemma has been proved. Use `\uses{...}` for actual mathematical dependencies.

For blueprint source changes, use a Python virtual environment with
`leanblueprint` and `plastexshowmore`, plus Graphviz and the required TeX tools.
With that environment active, run:

```sh
cd blueprint/src
python build_web.py
```

The **Check blueprint** workflow documents the Linux dependencies and repeats
this HTML build on PRs. Inspect warnings and changed pages/graphs. HTML generation
is a rendering check, not a Lean declaration or axiom audit. Generated files in
`blueprint/web/` are not committed. Homepage-only edits are reviewed in
`home_page/`; publication is performed after merging by **Publish blueprint**.

## Submit and review

Commit the intended files, push your branch to your fork, and open a PR against
`ylsong1024/BC4lean:main`. Complete the PR template. Link the issue and list
statements, assumptions, checks, and unresolved work. Credit sources and other
contributors. If tools or AI assisted the work, describe the assistance when it
helps reviewers assess provenance; the contributor remains responsible for
checking the result.

The **Build project** check covers imports and a strict Lean build. The
**Build blueprint HTML** check covers blueprint rendering. Both run on PRs,
including documentation-only PRs, so they can serve as consistent required
checks. These checks do not automatically audit all declaration axioms or the
mathematical adequacy of blueprint statements.

The maintainer reviews and merges accepted contributions. Contributors may also
review others' PRs: check the exact hypotheses, definitions, proof dependencies,
and whether the public API is useful beyond one lemma. Mathematical disagreements
belong in issues with precise examples or statements. Follow the
[Code of Conduct](CODE_OF_CONDUCT.md).

## Reuse and upstreaming

Prefer general lemmas when justified by the proof and available APIs. Discuss
potential Mathlib contributions separately; a BC4lean result is not automatically
part of Mathlib, and upstream acceptance is a separate review process. Record the
upstream PR before replacing local code or changing pinned dependencies.
