# Chapter 6 verification record

Chapter 6 constructs the topological side of the coefficient-free, reduced
Baum–Connes assembly problem for countable discrete groups. This construction
does not establish the assembly isomorphism or the general conjecture.

## Statement inventory and mathematical scope

The starting revision is `5504bccd79115c93f140986e7ee57262819e1ebb`.
Its Chapter 6 blueprint contains exactly three targets, all initially marked
`\notready`, with no Lean declaration links:

1. `def:piece-k-homology`: the genuine even/odd groups
   `KK_i^Γ(C₀(S, ℂ), ℂ)`, with the induced source action and trivial scalar action.
2. `prop:topological-transition`: restriction along closed invariant inclusions
   and the forward maps on K-homology, with identity and composition laws.
3. `def:topological-side`: the actual filtered colimit, its universal property,
   independence under cofinal reindexing, and universal proper-model independence.

Spaces used for the analytic construction are locally compact, second-countable
and Hausdorff, with continuous actions. Universal-model independence concerns
genuine equivariant CW models satisfying Chapter 4's subgroup fixed-point
criterion. The ambient action is proper and the group is countable and discrete.
The comparison uses a common space/module universe containing the relevant
carriers; the group universe is independent in the general piecewise construction.

The canonical model is Chapter 4's actual geometric telescope. The source
algebra action is `(g · a)(x) = a(g⁻¹ · x)`. Both parity groups are Chapter 5's
full Kasparov homotopy quotients; no substitute axiomatized K-homology functor
is introduced.

The mathematical reference is [Echterhoff, arXiv:1703.10912v2,
§§4.1–4.2](https://arxiv.org/html/1703.10912v2#S4.SS2), especially the
automatic properness of equivariant maps on cocompact proper spaces and
the displayed definition of the topological group as a KK colimit. The
formalization specializes the coefficient algebra to ℂ and the group to
the project's countable discrete scope. The additional cofinality statement
specifies precisely which replacement indexing families compute this colimit.

## Necessary clarifications

An alternative indexing family must be **cofinal** among the closed invariant
cocompact pieces. Being directed and covering all points is insufficient. For
the trivial group on `[0,1]`, the increasing compact subsets
`[0,1−1/n] ∪ {1}` (`n ≥ 1`) cover the interval but do not contain its terminal
piece. Their even K-homology colimit has two components, whereas the full
system has the interval as a terminal piece. The intended independence theorem
therefore states the precise upper-bound cofinality condition.

Universal comparison maps need not be globally proper. Each map is restricted
to one cocompact source piece, and its actual image is a closed cocompact target
piece. Compact orbit representatives and finite transporters prove properness
of this restriction. The same argument controls the entire interval of a
homotopy inside one target piece. Only these proper restrictions induce C₀
pullbacks.

Supremum-norm separability of C₀ is proved by extension by zero to the one-point
compactification and an isometric embedding into its continuous functions.
Compact-open separability of continuous functions on the uncompactified space
alone would not justify this step.

## Verification method

The finite Chapter 6 audit covers every declaration originating in the new
modules, including private/generated declarations, all blueprint declaration
links, and all required endpoints of the three original targets. It checks
the actual dependency axiom closure against `propext`, `Classical.choice`,
and `Quot.sound`. Mathematical fidelity and the necessary hypotheses are
reviewed separately from kernel acceptance.

Incremental strict module checks precede the aggregate warnings-as-errors
build. Chapter 4 and 5 Lean sources and their frozen mathematical records are
preserved. The historical 809-module aggregate remains an exact hash-bound
prefix of the extended aggregate, retained in
`audits/chapter6/Chapter5Imports.lean`. The existing retained Chapter 5 evidence
remains historical evidence for unchanged mathematical sources; it is not
rewritten to claim new executions.

Publication acceptance requires exact remote-commit equality, successful CI
for that revision, and checks of actual served chapter, graph and source-link
content against the published hash manifest. Final results are recorded only
after those checks have actually completed.

## Runtime verification outcome

The complete audit passed at `d29363fcdbe3b6e91041a4de5af3afdb531cdd1c`:
347 declarations in all 16 new modules, all 22 exact blueprint links and
16 required endpoints, with only `propext`, `Classical.choice` and `Quot.sound`.
The actual private geometric helper is present in the retained census.
The independent expected-type subprocess and strict cached-build gate exited 0;
all captured source and compiled-object hashes stayed unchanged.

All 16 strict module checks and genuine Lake leaf builds passed. The full
warnings-as-errors aggregate build passed with 825 library modules plus the
aggregate (4,220 Lake jobs). Its proof sources are unchanged at the audited
revision. All 23 Chapter 6 safeguard tests, 21 existing Chapter 5 safeguards,
and 12 blueprint-status tests passed. A fresh blueprint render has three
checked nodes, one explicit checked proof and 22 declaration links in both
the chapter and document graphs; Chapter 5's 75-node/435-link rendering also
passes its retained-evidence checks.

See [the completion record](CHAPTER6_COMPLETION.md) for retained raw evidence and
the publication acceptance protocol. The interval indexing example above is an
explanation of the necessary hypothesis; the formal indexing-independence theorem
is the positive theorem for cofinal families.
