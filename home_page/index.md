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

**Chapter 7 has verified foundations; the assembly map remains incomplete.**
The regular reduced crossed product and normalized cutoff projection are
constructed, including independence of its actual operator K₀ class. Full
Kasparov descent and its product compatibility remain open. The
[verification record](https://github.com/ylsong1024/BC4lean/blob/main/docs/CHAPTER7_VERIFICATION.md)
records the precise checked endpoints and remaining obligations.

| Chapter | Status | Details |
| --- | --- | --- |
| 4 — Proper actions and the universal proper space | Verified | [Chapter 4](blueprint/ch-proper-actions.html) · [verification record](https://github.com/ylsong1024/BC4lean/blob/main/docs/CHAPTER4_VERIFICATION.md) |
| 5 — Equivariant KK-theory | Verified | [Chapter 5](blueprint/ch-equivariant-kk.html) · [proof dependency graph](blueprint/dep_graph_chapter_5.html) |
| 6 — Topological side | Verified | [Chapter 6](blueprint/ch-topological-k-homology.html) · [proof dependency graph](blueprint/dep_graph_chapter_6.html) |
| 7 — Assembly map | Verified foundations; assembly incomplete | [Chapter 7](blueprint/ch-assembly-map.html) · [proof dependency graph](blueprint/dep_graph_chapter_7.html) |

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
universal proper telescope. Chapter 7 adds the regular reduced crossed product
and cutoff K₀ class; full descent and assembly remain incomplete.
The general conjecture is not proved here.

The blueprint distinguishes checked declarations and proofs from unfinished
targets. Contributions can be small, independently verified lemmas, examples,
or documentation improvements.
