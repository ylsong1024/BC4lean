# Chapter 8 native verification record

The actual audit reports `status=verified_milestone`, `milestone_verified=true`,
`chapter_complete=false`, and `general_conjecture_proved=false`. Its immutable
mathematical source is [`8d67185c67a7832b72ed466770df9f7d3ec896ed`](https://github.com/ylsong1024/BC4lean/commit/8d67185c67a7832b72ed466770df9f7d3ec896ed).

The original Baum–Connes property definition for countable discrete groups in
degrees zero and one is verified. The general coefficient-free reduced
Baum–Connes conjecture remains unproved and pending, in each Lean universe.
Its named Lean constant is a proposition-valued definition, not a proof.

## Mathematical scope and boundaries

The verified supporting statements concern model and cofinal-index invariance,
piecewise surjectivity/injectivity criteria, compact-model and finite-point
reductions, trivial-group analytic calibration, scalar descent, the scalar unit
projection, the point cutoff, and the actual Unit assembly equivalence.
Indexing comparisons retain their monotonicity and upper-bound cofinality
hypotheses. A finite-group point-model formula does not establish assembly
bijectivity for all finite groups.

The closed theorem `BC4lean.Chapter8Examples.baumConnesProperty_unit` proves exactly

```lean
∀ p : Bool, Function.Bijective (BC4lean.Assembly.reducedAssemblyHom Unit p)
```

Here `Unit` is Lean's literal `Unit : Type 0`. The theorem supplies no assembly
bijectivity, inverse, or compatibility hypothesis. It does not assert transport
to arbitrary universe lifts or every other presentation of a trivial group.
The independent fixture checks the actual canonical assembly map, the exact
universal general-statement definition, and this closed Unit conclusion.

## Actual native evidence

The uncapped module-origin census contains **10 new modules**,
**295 declarations**, including private/generated constants,
**40 exact blueprint links**, and **65 independently
typed endpoints** checked by **67 explicit examples**.
The property definition and all 10 supporting milestones are ready;
the general conjecture is pending. The actual transitive axiom closure is `Classical.choice`, `Quot.sound`, `propext`.

The 40 links contain 38 independently typed endpoints and two supporting
cycle-isomorphism data definitions:

- `BC4lean.KKTheory.UnitScalarDescent.evenCoefficientRestrictionIso`
- `BC4lean.KKTheory.UnitScalarDescent.oddCoefficientRestrictionIso`

Those two definitions receive exact native kind, origin, transitive-axiom and
semantic source checks. They do not have separate expected-type examples.

The actual sequential strict build contains **11 invocations**:
ten new leaf modules followed by the full aggregate of **940
library modules**. The frozen 930-module Chapter 7 proof prefix and its retained
canonical evidence are preserved. The actual **4
verification subprocesses** all returned zero:

- `/Library/Frameworks/Python.framework/Versions/3.14/bin/python3 -B /private/tmp/BC4lean-chapter7-descent-native-20261018/scripts/check_chapter7_retained.py --root /private/tmp/BC4lean-chapter7-descent-native-20261018 --new-inventory docs/audits/chapter8/inventory.json --output /var/folders/_4/cjl9v4654tb9m6kztgmr8pzr0000gn/T/chapter8-retained-actual-opftn12x/receipt.json` — exit 0.
- `lake --wfail --no-build --no-cache build BC4lean` — exit 0.
- `lake env lean -j1 -DwarningAsError=true -DautoImplicit=false -DrelaxedAutoImplicit=false /private/tmp/BC4lean-chapter7-descent-native-20261018/docs/audits/chapter8/ExpectedTypes.lean` — exit 0.
- `lake env lean -j1 -DwarningAsError=true -DautoImplicit=false -DrelaxedAutoImplicit=false /private/tmp/BC4lean-chapter7-descent-native-20261018/docs/audits/chapter8/audit.lean` — exit 0.

The strict retained replayer checks every raw process/log/query binding, full
build segment, independent fixture, private/generated origin and allowed axiom
closure. Source, query, full-build evidence and compiled objects remained
unchanged during the actual audit. Ordinary source elaboration budgets and
strict options remain in force. Unlimited metadata enumeration supplies no
replacement mathematical proof.

| Evidence | SHA-256 |
| --- | --- |
| [Actual audit](audits/chapter8/audit.json) | `b8a62d6e3ec19edd02a7a27dfc4509a9965c8e4681d5b1c617ac656f135b24f5` |
| [Actual eleven-build record](audits/chapter8/build.json) | `7a512e6326701ba6eefd56875ead83c0e729d283e206276d3f2ab1973c65e53d` |
| [Actual combined build log](audits/chapter8/build.log) | `8d29d16fe11adceeb599b76046d21e2eeb57b0d00d2fd7240e7879df8c87402d` |
| Actual generated kernel query | `82deef71687fcca141a58a9324d56799ff4df925f138f0e2dd93143788b6aa4b` |
| Actual independent fixture | `93d0d05fe6f15ca86d85e49dc98f90e6c335a92b2d21af0a0401eefc31e19cf8` |

## Separate publication acceptance

This native record makes no remote, CI, or live-publication success claim.
After the authorized push, a separate `chapter8.postpush.acceptance.v1` receipt
must bind the final remote Q8, immutable S8 above, these actual audit/build
hashes, all six exact-Q8 workflows, and independently fetched live content:

- Build BC4lean
- Check blueprint
- Publish blueprint
- Verify Chapter 6
- Verify Chapter 7 milestones
- Verify Chapter 8 milestones

Live acceptance includes the actual version manifest, homepage, finder,
Chapter 8 and retained Chapter 7 pages, both chapter graphs, the full document
graph, and immutable source files and exact declaration lines at S8/S7. The
general conjecture must remain pending with an orange graph profile and no
checked proof. A successful publisher alone is insufficient.

The post-push receipt stays in durable task evidence outside Q8, avoiding a
commit containing its own hash. Synthetic Python rejection fixtures are not
native, remote, CI, or live proof evidence.
