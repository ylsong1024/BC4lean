# Contributor tasks and roadmap

This is a source-based planning snapshot dated 2026-10-05. Tasks below are
proposals, not opened GitHub issues or assigned work. Check the current source
and [issues](https://github.com/ylsong1024/BC4lean/issues) before claiming one.
Completion requires a reviewed implementation and the checks in
[CONTRIBUTING.md](../CONTRIBUTING.md).

## Mathematical boundaries

| Area | Existing source | Remaining work |
| --- | --- | --- |
| Reduced group C*-algebra | Group algebra, regular representation, reduced completion and comparisons | Examples, API refinement, independent review |
| Operator K-theory | K₀/K₁ constructions, functoriality, nonunital comparisons and homotopy modules | Review exact hypotheses and extend structural results in bounded steps |
| Proper actions | Equivariant CW attachment, Hausdorffness, properness, cellular mapping, finite-group models, labeled orbit simplices, cocompact indexing for a given space | General universal proper CW-model existence and a locally compact second-countable model |
| Equivariant KK-theory | Blueprint specifications | Hilbert module and cycle infrastructure, product and comparison results |
| Topological side and assembly | Blueprint specifications | Transition maps, colimit, descent, cut-off classes and compatibility |

This table describes source organization, not a new verification certificate.
The general conjecture is not proved by this project. In particular,
`HomotopyTerminalFor` gives uniqueness conditional on its hypotheses; it does not
construct a universal proper Γ-space.

## Bounded tasks to propose

### DOC-01 — Audit one chapter's declaration links

**Suitable for:** a contributor learning the project, with basic Lean familiarity.
Choose one section, check each `\lean` target against the pinned source, and
compare its statement with the prose. Start with Chapter 2 or a small part of
Chapter 3. Chapter 1's overview also needs reconciliation with the newer K₁
modules; do not infer proof status from filenames alone.

**Done when:** a PR lists the checked labels and declarations, corrects any
mismatches, and renders the affected blueprint. Verification markers change only
with corresponding Lean evidence. No new mathematical theorem is required.

### C4-01 — Inclusion maps between invariant subspaces

**Suitable for:** a contributor familiar with subtypes and continuous maps.
**Start from:** `BC4lean/CocompactPieces.lean` and `BC4lean/EquivariantMaps.lean`.

For invariant subsets S ⊆ T of a Γ-space X, construct the equivariant continuous
inclusion S → T. Prove identity and composition laws and compatibility with
inclusion into X. Specialize to the underlying invariant subsets of cocompact
pieces. Retain exactly the ambient assumptions needed for these maps; do not
assume the existence of a universal proper space.

**Done when:** the maps and laws compile under the pinned toolchain, their axioms
are audited, the full build passes, and a small example demonstrates composition.
This supplies maps between pieces; it does not yet define K-homology transition
maps or a colimit.

### C4-02 — Fixed points of orbit cells

**Suitable for:** a contributor comfortable with quotient and subspace topology.
**Start from:** `BC4lean/OrbitFixedPoints.lean`, `BC4lean/ProperOrbitCells.lean`, and
`BC4lean/ProperFixedPoints.lean`.

With trivial Γ-action on D, construct the natural homeomorphism
((Γ/H) × D)^K ≅ (Γ/H)^K × D for subgroups H and K. State topology and action
assumptions explicitly and prove the forward/inverse formulas. Normality of H
must not be introduced just to simplify the quotient.

**Done when:** the homeomorphism and formulas compile and are audited, including
empty fixed-point cases. Keep this distinct from an equivariant CW construction.

### C4-03 — Realize the labeled orbit simplices

**Suitable for:** an experienced topology and Lean contributor.
**Start from:** `BC4lean/LabeledOrbitSimplices.lean` and
`BC4lean/EquivariantCW.lean`.

The categorical attachment interface, closed skeletal inclusions, Hausdorffness,
properness, and cellular mapping property are already verified. The labeled
simplices now have a group action without inversions, finite stabilizers for
nonempty simplices, and a fixed vertex at every label for each finite subgroup.
Construct their geometric realization with an actual equivariant CW structure,
using the specified orbit disks, boundary maps, pushouts, and colimit.

**Done when:** the realization and CW witnesses compile and are axiom-audited,
including faces and the empty-simplex boundary case. Fixed-point/realization
compatibility and fixed-space contractibility require their own proofs. The
locally compact second-countable model choice remains a further obligation;
these combinatorial results alone do not verify universal proper CW existence.

### KK-01 — Inventory Hilbert C*-module prerequisites

**Suitable for:** an operator-algebra contributor working with a Lean developer.
Survey the pinned APIs for complex C*-algebras, module-valued inner products,
completeness, and adjointable operators. Propose exact conventions for Chapter 5's
`def:hilbert-modules`, with a small test case and a list of reusable APIs.

**Done when:** the issue/PR contains a checked API inventory and a bounded next
statement. An inventory alone does not justify a verified definition marker.
Do not replace Kasparov theory by an axiomatized interface and call it complete.

## Longer-term dependencies

Equivariant CW and extension results are prerequisites for a general universal
proper-space construction and its mapping property. The chosen model's
hypotheses must support the topological-side construction. Equivariant
KK-theory and operator K-theory comparisons then support descent and the assembly
map. Each arrow needs its own explicit mathematical and Lean interface.

The roadmap intentionally separates these goals from small contributor tasks.
If an attempt yields no new theorem or justified next mechanism, report that
fact and the obstruction in the issue rather than recording the goal as done.
