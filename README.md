# Baum–Connes Conjecture — BC4lean

BC4lean is an open-source Lean formalization project developing the foundations
for the **coefficient-free, reduced Baum–Connes conjecture for countable discrete
groups**. All algebras and Hilbert spaces are complex.

We welcome contributions in mathematics, Lean, documentation, and review.
The project does **not** currently contain a proof of the general conjecture.
Constructing its ingredients, formalizing its statement, and proving special
cases are distinct milestones.

[Project website](https://ylsong1024.github.io/BC4lean/) ·
[Mathematical blueprint](https://ylsong1024.github.io/BC4lean/blueprint/) ·
[Dependency graph](https://ylsong1024.github.io/BC4lean/blueprint/dep_graph_document.html) ·
[Contributing](CONTRIBUTING.md) · [Tasks and roadmap](docs/ROADMAP.md)

## Where to start

1. Read the [contribution guide](CONTRIBUTING.md) and choose a bounded task from
   the [roadmap](docs/ROADMAP.md).
2. Open an [issue](https://github.com/ylsong1024/BC4lean/issues/new/choose) describing
   the intended statement or change. Check existing issues to avoid duplicate work.
3. Work on a branch in your fork and submit a pull request. Repository write access
   is not needed to propose a contribution.

Small API lemmas, examples, mathematical explanations, and careful reviews are
valuable contributions. Advanced milestones should first be split into interfaces
and independently checkable lemmas.

## Current scope

The source contains the group algebra and regular representation, the reduced
group C*-algebra construction, operator K-theory modules, and foundations for
proper actions and equivariant homotopy. These are building blocks for the
assembly map, not a completed assembly construction.

In Chapter 4, equivariant CW infrastructure and a universal proper-space model
remain unfinished. Equivariant KK-theory and the assembly construction are later
milestones. Consult the [roadmap](docs/ROADMAP.md) and individual blueprint nodes
for precise boundaries; a green prerequisite does not verify its successors.

## Build with the pinned dependencies

Install [Lean via elan](https://lean-lang.org/install/) and, if using VS Code,
the Lean 4 extension. Clone this repository (or your fork), then run:

```sh
git clone https://github.com/ylsong1024/BC4lean.git
cd BC4lean
lake exe cache get
python3 scripts/check_project_imports.py
lake --wfail build BC4lean
```

The checkout selects Lean **4.33.1** through `lean-toolchain`.
`lake-manifest.json` pins Mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474`.
Keep the toolchain, Lake configuration, and manifest unchanged in ordinary PRs;
do not run `lake update` as a routine setup step.

For a changed module, first run, for example:

```sh
lake env lean -DwarningAsError=true BC4lean/EquivariantMaps.lean
```

The full build is still required before merging Lean changes. See
[CONTRIBUTING.md](CONTRIBUTING.md) for axiom audits and blueprint checks.

## Repository layout

| Path | Purpose |
| --- | --- |
| `BC4lean/` | Lean definitions and proofs |
| `BC4lean.lean` | Explicit imports of every project module |
| `blueprint/src/parts/` | Mathematical chapters and declaration links |
| `home_page/` | Public project homepage |
| `docs/ROADMAP.md` | Contributor tasks and mathematical dependencies |
| `.github/` | Issue/PR templates and automated checks |

Repository administrators can use the [collaboration launch checklist](docs/MAINTAINERS.md).

## License and credit

The project uses the existing [Apache 2.0 license](LICENSE).
Credit contributors through commits, PRs, and source author acknowledgments as
appropriate; preserve existing credits and cite mathematical sources.
The repository was initialized from the
[LeanProject template](https://github.com/leanprover-community/LeanProject).
Please follow the [Code of Conduct](CODE_OF_CONDUCT.md).
