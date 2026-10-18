# Chapter 5 completion and publication

**Chapter 5 verification completed on 2026-10-17** at
[`d6e6e3efe5ee5b47b30d01177840849e39a3e171`](https://github.com/ylsong1024/BC4lean/commit/d6e6e3efe5ee5b47b30d01177840849e39a3e171).
All 506 supplemental mathematical checks passed, the ordinary push matched
remote `main`, and all required workflows passed on that exact revision:

- [Build BC4lean](https://github.com/ylsong1024/BC4lean/actions/runs/39055782136), including the warnings-as-errors build and complete-target declaration audit.
- [Check blueprint](https://github.com/ylsong1024/BC4lean/actions/runs/39055782144).
- [Publish blueprint](https://github.com/ylsong1024/BC4lean/actions/runs/39055782119), including Pages deployment.

The [core verification record](CHAPTER5_VERIFICATION.md) contains the mathematical
scope, exact theorem links, hypotheses, trust assumptions, and source corrections.
It is a frozen record from before the later supplemental/publication outcomes;
its historical pending language does not describe the final outcome. The
[final completion index](audits/chapter5/final-completion-index.json),
[supplemental result](audits/chapter5/final-supplemental-result.json), and
[genuine terminal receipt](audits/chapter5/final-supplemental-terminal.json)
are unchanged copies of the final external evidence. Their original local
paths are provenance. The supplemental result's own `Chapter5_complete_claimed`
field remains false because that run preceded publication; the completion
index includes the later successful commit, push and exact-revision CI.

The retained core checks cover 809 Lean modules, all 75 Chapter 5 blueprint
blocks and 435 distinct Lean links, and an uncapped census of 18,199 declarations
in 686 modules. The exact axiom set is `propext`, `Classical.choice`, and
`Quot.sound`. The final supplemental run freshly reconciled 498 retained
successes and executed the eight remaining queries successfully. Earlier
failed runs and unknown interrupted-run outcomes remain recorded honestly.

The scope includes full even/odd equivariant KK groups, Kasparov product
existence, uniqueness and laws, and natural ordinary K₀/K₁ comparisons with
explicit inverses. The partition uses positive contractions, correcting the
inconsistent printed inequalities; creation-operator compactness retains
the appropriate compact-left-action hypothesis. The full correspondence
quotient retains target separability. The general Baum–Connes conjecture
and the later assembly construction are separate milestones.

## Website correction, 2026-10-18

A live-site recheck confirmed that Pages had deployed the verified revision,
but the homepage and overview still contained old status summaries. The
Chapter 5 graph also lacked proof markers for 46 verified propositions,
and the source finder lacked 408 of the chapter's 435 declaration anchors.
A green deployment alone had not detected these content defects.

The publication correction updates the summaries, derives the missing proof
markers from the byte-bound retained kernel evidence in a temporary render
copy, and supplies the missing declaration/source links. The frozen Chapter 5
mathematical source and all audited Lean sources remain unchanged. Existing
proof text and the graph's distinction between verified proofs and verified
ancestors are preserved. Publication checks validate the rendered proof
markers and all 435 source-finder anchors.

[Project website](https://ylsong1024.github.io/BC4lean/) ·
[Chapter 5](https://ylsong1024.github.io/BC4lean/blueprint/ch-equivariant-kk.html) ·
[Chapter 5 proof graph](https://ylsong1024.github.io/BC4lean/blueprint/dep_graph_chapter_5.html)
