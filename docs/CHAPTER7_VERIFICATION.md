# Chapter 7 verification record — historical foundation checkpoint

## Dated preservation note — 2026-10-18

This is the historical foundation verification record, frozen in scope at
proof-source revision **`7af944529243b198d584891762959a954973bb4b`** and
publication revision **P = `d3a357136bbcf5eb88926deb9fa069666d217c51`**.
The historical checkpoint comprises sixteen new modules, 535 audited
declarations, 65 exact blueprint links and 65 endpoints. Exactly one of the
five original targets, the cutoff target, was ready; four original descent
and assembly targets remained pending, and `chapter_complete=false`.

Every statement below about a passed build, audit, safeguard, or ready/pending
target belongs to that foundation checkpoint, not to later source drafts or a
later completion audit. The source and publication identities above must not
be replaced with the final completion revision. Historical audit, generated
query, build, fixture and subprocess-record links are pinned to P so that
later replacements at the same repository paths cannot silently alter the
scope or evidence of this record. The
[historical record as published at P](https://github.com/ylsong1024/BC4lean/blob/d3a357136bbcf5eb88926deb9fa069666d217c51/docs/CHAPTER7_VERIFICATION.md)
and [frozen proof source](https://github.com/ylsong1024/BC4lean/tree/7af944529243b198d584891762959a954973bb4b)
remain the reference points for its original claims.

The [Chapter 7 completion record](CHAPTER7_COMPLETION.md) is a separate
record for the later verified descent and assembly construction. Its scope
includes arbitrary interval homotopy transport, all four native products and
the complete original target inventory, with its own immutable source, actual
complete audit and full build. Native mathematical verification and CI/live
acceptance for the exact later publication revision are distinct records.
Constructing assembly does not prove the general Baum–Connes conjecture.

## Historical foundation record

The text below is retained as the foundation checkpoint narrative. References
to the present construction, remaining obligations and follow-on drafts are
read as statements about that frozen checkpoint.

Work begins at `a70dee4c556da36e065a1d64cc0429ba2831ddd4` (the verified
Chapter 6 publication revision). The intended scope is the coefficient-free,
reduced assembly map for countable discrete groups in degrees zero and one.
Constructing this map is separate from proving that it is an isomorphism.

## Original statement inventory

All five original Chapter 7 statements initially carried `\notready`, with
no Lean declaration links:

| Blueprint label | Required mathematical construction |
| --- | --- |
| `def:reduced-descent` | Reduced crossed products, Kasparov descent, its compatibility with products, and the scalar crossed-product identification |
| `def:cutoff-projection` | Existence of normalized compactly supported cutoff functions, their projections in the actual reduced crossed product, and independence of their operator K-class |
| `def:assembly-piece` | The actual cutoff-class/Kasparov-descent product in both degrees |
| `prop:assembly-compatibility` | Compatibility with piece transitions, auxiliary choices, and universal-model changes |
| `def:assembly-map` | The homomorphism induced on Chapter 6's actual topological K-homology colimit |

No crossed-product or Kasparov-descent implementation existed in the starting
revision. The Chapter 6 colimit universal property does not by itself construct
an assembly map: the required analytic maps and their compatibility must first
be proved.

## Mathematical dependencies and necessary hypotheses

For cutoff existence the space is locally compact Hausdorff, the action is
continuous and proper, the group is discrete, and the orbit quotient is
compact. A `CocompactPiece` alone does not encode properness; the proper-action
hypothesis must be supplied from the ambient model. A trivial action of an
infinite discrete group on one point illustrates why it cannot be omitted.
Cutoff existence itself does not require countability. The countable group
and second-countability assumptions are retained where the project's KK APIs
need separable coefficient algebras.

The present reduced crossed product is its underlying nonunital C*-algebra.
The induced grading for coefficient actions preserving a grading is not yet
bundled; this is another prerequisite for the full graded KK construction.
Reduced descent needs an actual Hilbert module over `B ⋊ᵣ Γ`, an integrated
left representation and descended operator, compact-defect transport, descent
through homotopy, and the interior-tensor comparison for products. The actual
interior tensor `E ⊗_B (B ⋊ᵣ Γ)`, using the constructed coefficient inclusion
and standard right module, is a concrete route; a separate raw `C_c(Γ,E)`
positive-form construction is optional. These are mathematical proof
obligations, not fields to assume in a record. In particular, an arbitrary
covariant representation yields a full crossed-product representation; a
separate reduced-norm bound is required here. No amenability or exactness hypothesis should be added to obtain
the general reduced descent construction.

For a proper equivariant map `f:S→T`, write `r=f*:C₀(T)→C₀(S)` and choose
`c_S=c_T∘f`. The required cutoff naturality is
`(r ⋊ᵣ Γ)(p_cT)=p_cS`. Descent naturality and product associativity then give
`μ_T(f_*x)=μ_S(x)`. For inclusions the homomorphism is the existing
`CZero.pieceRestriction`. For ambient model comparisons one must use the
proper restrictions to cocompact pieces, not assume global properness.

The initial cutoff class is an operator K₀ class. The scalar KK/K₀ comparison
must be used in the correct direction before taking the Kasparov product.

Reference: S. Echterhoff, [Bivariant KK-Theory and the Baum-Connes conjecture,
§4.2](https://arxiv.org/html/1703.10912v2#S4.SS2). The blueprint specializes
the locally compact-group formulas to discrete groups, so no modular factor
appears.

## Meaning of the constructed foundations

The regular module uses the coefficient-valued form `∑g ξg*ηg` and its
C*-module norm. It does not replace that norm by the Banach ℓ² norm of the
coefficient norms. The reduced algebra is the closed **nonunital** star
subalgebra of the actual adjointable operator algebra generated by the twisted
coefficient operators and translations. The integrated finite-support map is
faithful and dense; its norm is the actual reduced operator norm. No chosen
faithful representation, reduced-norm witness, or universal-property conclusion
is an input. Separability requires a countable group and separable coefficients.

For cutoffs, properness supplies compact transporters, giving finite **global**
group support of the compact mixed coefficients. Their actual twisted
convolution and involution yield both partial-isometry equations. The completed
projection class belongs to the existing `OperatorK0`, the scalar kernel of
ordinary projection K₀ in the forced unitization. Its independence is proved
by an explicit one-by-one matrix Murray–von Neumann equivalence. No new quotient
on cutoff functions and no assumed K-theory invariance rule replaces that proof.

The scalar comparison constructs the unitary to the existing `L2Group Γ` and
uses it to identify the two actual closed C*-algebras. The coefficient extension
module uses the existing completed interior tensor with the actual coefficient
inclusion. Its `T ⊗ 1` operator and compactness transport are prerequisites for
descent; they do not define a descended KK class or homomorphism.

## Verification protocol

Each new module is checked with the pinned Lean 4.33.1 compiler, strict
implicit-variable options and warnings as errors. The new aggregate imports
must exactly cover the uncapped module-origin census while preserving the
historical 825-module aggregate as a byte-identical prefix. Every new
declaration, including private and generated declarations, is checked for its
actual axiom dependency closure. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed. An independent expected-type fixture checks the
claimed mathematical endpoints. Sources and compiled objects are hash-bound
throughout the audit.

Verified intermediate statements have their own blueprint labels. They do
not change the readiness of any original target. A successful milestone audit
with pending original targets must report `chapter_complete=false`;
`--require-complete` must reject that state. Publication is checked separately
against the exact pushed revision, actual served chapter and dependency graphs,
declaration anchors, and immutable source file/line links.

## Verified foundation checkpoint

The frozen proof-source revision is
`7af944529243b198d584891762959a954973bb4b`. All sixteen new modules pass
strict compilation. The actual sequential Lake build passes for the full
841-module library and its aggregate (4,239 build jobs), with
`LEAN_NUM_THREADS=1`. The original 825 imports remain a byte-identical prefix.
The toolchain, package manifest, and preserved Chapter 4–6 sources are unchanged.

The uncapped kernel audit checks **535 declarations**, including private and
generated declarations, **65 exact blueprint links**, and **65 mathematical
endpoints**. Their combined axiom closure is exactly `propext`,
`Classical.choice`, and `Quot.sound`. The independent expected-type fixture,
cached strict aggregate gate, frozen historical-import fixture, and all
source/object hash checks pass. See [the historical actual audit at P](https://github.com/ylsong1024/BC4lean/blob/d3a357136bbcf5eb88926deb9fa069666d217c51/docs/audits/chapter7/audit.json),
[its historical generated kernel query at P](https://github.com/ylsong1024/BC4lean/blob/d3a357136bbcf5eb88926deb9fa069666d217c51/docs/audits/chapter7/audit.lean),
[the historical actual full-build record at P](https://github.com/ylsong1024/BC4lean/blob/d3a357136bbcf5eb88926deb9fa069666d217c51/docs/audits/chapter7/build.json), and their retained
[historical fixtures, raw logs and subprocess records at P](https://github.com/ylsong1024/BC4lean/tree/d3a357136bbcf5eb88926deb9fa069666d217c51/docs/audits/chapter7). No simulated subprocess record is used.

The audit reports `status=verified_milestone`, `milestone_verified=true`, and
**`chapter_complete=false`**. Running the actual command with
`--require-complete` returns **2**, deliberately rejecting chapter completion;
all four verification subprocesses return zero. An earlier expected-type
fixture attempt failed on an implicit compact-operator coercion; making that
coercion explicit repaired the fixture without changing a mathematical source.

The blueprint has eleven separately stated prerequisite milestones, 65 exact
declaration links and six explicit proof environments. **Only the original
cutoff target is ready.** All four descent and assembly targets remain pending
at their original strength. Reduced-norm integration on descended modules,
full KK-homotopy transport, product comparison in both degrees, actual piece
assembly maps, and their naturality/colimit construction remain required.
Construction of an assembly map would still not prove the Baum–Connes
conjecture.

All 113 historical and new Python safeguards pass. Chapter 5/6 evidence and
immutable source-finder checks remain in force. The new finder pins each
Chapter 7 declaration to the exact frozen source revision above. Publication
acceptance requires the separate exact-pushed-SHA CI results and an independent
HTTP check of the served homepage, chapter, both dependency graphs, declaration
anchors and actual immutable source files/lines. A successful deployment job
alone does not establish those content checks.

Uncompiled follow-on descent drafts are kept outside this verified checkpoint.
They do not contribute to its declaration counts or readiness claims.
