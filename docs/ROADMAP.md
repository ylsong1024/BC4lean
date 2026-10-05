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
| Proper actions | Equivariant CW attachment, Hausdorffness, properness, cellular mapping, finite-group models, proper weak labeled join with genuine CW structure and fixed-point criterion, universal mapping and uniqueness, locally compact second-countable telescope model, cocompact indexing | API refinement, examples and independent review |
| Equivariant KK-theory | Blueprint specifications | Hilbert module and cycle infrastructure, product and comparison results |
| Topological side and assembly | Blueprint specifications | Transition maps, colimit, descent, cut-off classes and compatibility |

This table describes source organization, not a new verification certificate.
The general conjecture is not proved by this project. In particular,
`HomotopyTerminalFor` gives a conditional mapping property. The verified labeled
join separately constructs a universal proper Γ-CW space; the locally compact
second-countable CW model is now constructed by the verified geometric telescope.

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

**Verified:** `InvariantSubspaceMaps.lean` supplies the maps, all laws and a
composition example. Strict Lean checking and all 11 public-declaration axiom
audits pass with only the accepted standard axioms.

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

**Verified:** `OrbitCellFixedSpace.lean` supplies the actual homeomorphism,
formulas and empty-factor cases. Strict Lean checking and all seven
public-declaration axiom audits pass with only the accepted standard axioms.

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

**Verified:** the weak realization and its genuine CW structure satisfy the full
fixed-point criterion for every discrete group. For countable discrete groups,
the verified prism homeomorphism gives the genuine locally compact
second-countable telescope CW model.

**Suitable for:** an experienced topology and Lean contributor.
**Start from:** `BC4lean/LabeledOrbitSimplices.lean` and
`BC4lean/EquivariantCW.lean`.

The categorical attachment interface, closed skeletal inclusions, Hausdorffness,
properness, and cellular mapping property are already verified. The labeled
simplices now have a group action without inversions, finite stabilizers for
nonempty simplices, and a fixed vertex at every label for each finite subgroup.
The weak realization, compact finite simplex charts and disk pairs, actual
proper action, and skeletal colimit now pass strict Lean checks. Its finite
subgroup fixed spaces are proved contractible by a global factor shift followed
by a cone to a fixed vertex. The full orbit-disk coproduct pushout witness
and its assembly into the categorical CW structure now pass strict Lean
checking; their axiom audit uses only the standard Lean logical principles.
The geometric telescope now supplies the genuine locally compact
second-countable universal proper CW model.

**Done when:** the realization and CW witnesses compile and are axiom-audited,
including faces and the empty-simplex boundary case. Fixed-point/realization
compatibility and fixed-space contractibility require their own proofs. The
locally compact second-countable model choice is now proved;
the verified realization, fixed-point contraction and CW attachments together
prove universal proper CW existence for every discrete group.

### KK-01 — Inventory Hilbert C*-module prerequisites

**Suitable for:** an operator-algebra contributor working with a Lean developer.
Survey the pinned APIs for complex C*-algebras, module-valued inner products,
completeness, and adjointable operators. Propose exact conventions for Chapter 5's
`def:hilbert-modules`, with a small test case and a list of reusable APIs.

**Done when:** the issue/PR contains a checked API inventory and a bounded next
statement. An inventory alone does not justify a verified definition marker.
Do not replace Kasparov theory by an axiomatized interface and call it complete.

## Longer-term dependencies

The verified equivariant CW and extension results now support the universal
proper-space construction and its mapping property. The chosen telescope model
supplies the hypotheses needed for the topological-side construction. Equivariant
KK-theory and operator K-theory comparisons then support descent and the assembly
map. Each arrow needs its own explicit mathematical and Lean interface.

The roadmap intentionally separates these goals from small contributor tasks.
If an attempt yields no new theorem or justified next mechanism, report that
fact and the obstruction in the issue rather than recording the goal as done.
