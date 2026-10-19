---
usemathjax: true
title: BC4lean
---

## Verification status

**Chapter 5 is verified.** Its full even/odd equivariant KK groups, Kasparov
product laws, and natural comparisons with operator K₀/K₁ have passed the
strict Lean build and axiom audit, together with all 506 supplemental checks.
The [completion record](https://github.com/ylsong1024/BC4lean/blob/main/docs/CHAPTER5_COMPLETION.md)
links the exact verified revision, checks, scope, and source corrections.

**Chapter 6 is verified.** It constructs the actual topological K-homology
colimit, with cofinal indexing and universal proper-model independence under the
[documented hypotheses](https://github.com/ylsong1024/BC4lean/blob/main/docs/CHAPTER6_COMPLETION.md).
All 16 new modules and 347 audited declarations pass.

**Chapter 7 is verified.** It constructs reduced descent and assembly in
degrees zero and one. The checked scope includes
actual descended cycles and additive KK maps, full arbitrary interval homotopy
transport, and compatibility with all four native Kasparov products
(even–even, even–odd, odd–even, and odd–odd). The actual cutoff-class/descent
product defines each piece map; compatibility with transitions induces the
homomorphism on Chapter 6's actual topological K-homology colimit, with values
in the existing reduced operator K₀ and K₁ groups.

The [completion record](https://github.com/ylsong1024/BC4lean/blob/main/docs/CHAPTER7_COMPLETION.md)
states the exact checked proof revision, audit/build evidence, hypotheses,
cofinal indexing comparisons, and compatibility with actual model comparison
maps. It distinguishes native completion from the separate CI and live-content
acceptance receipt for the exact publication revision. The
[historical foundation record](https://github.com/ylsong1024/BC4lean/blob/main/docs/CHAPTER7_VERIFICATION.md)
retains its original, narrower checkpoint.

**Chapter 8 has verified calibration results.** The trivial-group assembly map is verified in both degrees.
For the literal group `Unit : Type`, an explicit additive equivalence equals
the actual canonical assembly map. The checked comparisons also cover model
and cofinal-index invariance, piecewise bijectivity criteria, scalar analytic
targets, and the finite-group point-model formula. The
[verification record](https://github.com/ylsong1024/BC4lean/blob/main/docs/CHAPTER8_VERIFICATION.md)
gives the exact proof scope and native evidence. The general Baum-Connes conjecture remains unproved.

| Chapter | Status | Details |
| --- | --- | --- |
| 4 — Proper actions and the universal proper space | Verified | [Chapter 4](blueprint/ch-proper-actions.html) · [verification record](https://github.com/ylsong1024/BC4lean/blob/main/docs/CHAPTER4_VERIFICATION.md) |
| 5 — Equivariant KK-theory | Verified | [Chapter 5](blueprint/ch-equivariant-kk.html) · [proof dependency graph](blueprint/dep_graph_chapter_5.html) |
| 6 — Topological side | Verified | [Chapter 6](blueprint/ch-topological-k-homology.html) · [proof dependency graph](blueprint/dep_graph_chapter_6.html) |
| 7 — Assembly map | Verified: actual descent and assembly in both degrees | [Chapter 7](blueprint/ch-assembly-map.html) · [proof dependency graph](blueprint/dep_graph_chapter_7.html) · [completion record](https://github.com/ylsong1024/BC4lean/blob/main/docs/CHAPTER7_COMPLETION.md) |
| 8 — The conjecture and examples | Verified Unit case and comparisons; general conjecture pending | [Chapter 8](blueprint/ch-conjecture-and-examples.html) · [proof dependency graph](blueprint/dep_graph_chapter_8.html) · [verification record](https://github.com/ylsong1024/BC4lean/blob/main/docs/CHAPTER8_VERIFICATION.md) |

## Join the project

BC4lean welcomes contributions from mathematicians, Lean developers, and readers
who can improve explanations or review proofs. You can participate through a
GitHub fork and pull request; repository write access is not required.

- [Read the contribution guide](https://github.com/ylsong1024/BC4lean/blob/main/CONTRIBUTING.md).
- [Choose a task from the roadmap](https://github.com/ylsong1024/BC4lean/blob/main/docs/ROADMAP.md).
- [Discuss or claim a task](https://github.com/ylsong1024/BC4lean/issues).

## Mathematical scope

The target is the coefficient-free, reduced Baum–Connes conjecture for countable
discrete groups. Verified foundations include group C*-algebras, operator
K-theory, the universal proper-space construction for countable discrete
groups, and equivariant KK-theory under the hypotheses in the
[Chapter 5 verification record](https://github.com/ylsong1024/BC4lean/blob/main/docs/CHAPTER5_VERIFICATION.md).
The verified topological side uses the actual KK colimit and the constructed
universal proper telescope. Chapter 7 constructs the actual
regular reduced crossed products and scalar identification, normalized cutoff
operator K₀ classes, reduced KK descent, and assembly homomorphisms in both
degrees. Reduced descent retains the countable-group, separable-coefficient
and module-universe hypotheses of the KK APIs, allows nonunital complex
C*-algebras, and requires no amenability or exactness assumption. Full homotopy
transport uses arbitrary complete interval modules, with whole-cycle endpoint
comparisons.

For assembly, the proper models are locally compact, Hausdorff and second
countable, with a continuous action of the countable discrete group. Cutoffs
on cocompact pieces use the supplied proper-action hypothesis. Indexing
independence uses monotone directed systems with the genuine cofinal
upper-bound condition for every cocompact piece. Naturality for ambient
equivariant model maps uses their actual proper restrictions to cocompact
pieces; universal proper CW model independence uses the established
fixed-point criterion and actual comparison maps. The full formal scope is in the
[completion record](https://github.com/ylsong1024/BC4lean/blob/main/docs/CHAPTER7_COMPLETION.md).
The general Baum-Connes conjecture remains unproved.

The blueprint distinguishes checked declarations and proofs from unfinished
targets. Contributions can be small, independently verified lemmas, examples,
or documentation improvements.
