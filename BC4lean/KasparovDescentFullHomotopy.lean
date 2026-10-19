import BC4lean.KasparovDescentIntervalFibreIso
import BC4lean.KasparovHomotopyRelation
import BC4lean.FullCliffordParityHomotopy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Actual full arbitrary interval homotopy transport for reduced descent

The construction uses the concrete reduced source representation.

 No map on KK quotients or product comparison
is claimed here.

The input witness stores its arbitrary complete interval module. We extend
that same module to continuous crossed coefficients, then compare both whole
fibres by the actual completed tensor unitaries. Carrier universes enlarge
with the genuine crossed coefficient algebra; the result uses their common
enlarged universe rather than assuming the original module universe persists.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB}
  [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]

variable (β : CStarAlgebraAction Γ B) (α : CStarAlgebraAction Γ A)

/-- Bundle the genuine raw even descended cycle in its actual carrier universe. -/
def bundledEvenCycle (c : BundledKasparovCycle.{uΓ, uA, uB, uE} α β) :
    BundledKasparovCycle.{0, max uΓ uA, max uΓ uB, max uE (max uΓ uB)}
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α))
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β)) :=
  BundledKasparovCycle.of (evenCycle β α c.cycle)

/-- Bundle the actual raw odd descended cycle with the same genuine universe. -/
def bundledOddCycle (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    BundledOddKasparovCycle.{0, max uΓ uA, max uΓ uB, max uE (max uΓ uB)}
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α))
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β)) :=
  BundledOddKasparovCycle.of (oddCycle β α c.cycle)

/-- Transport a genuine full even witness, preserving its arbitrary interval
module and identifying its two entire evaluated cycles. -/
def evenFullHomotopy
    {c d : BundledKasparovCycle.{uΓ, uA, uB, uE} α β}
    (h : FullKasparovHomotopy c d) :
    FullKasparovHomotopy (bundledEvenCycle β α c) (bundledEvenCycle β α d) where
  intervalCycle := BundledKasparovCycle.of
    (intervalEvenCycle β h.intervalCycle.carrier α h.intervalCycle.cycle)
  sourceIso := (intervalEvenCycleFibreIso β h.intervalCycle.carrier α h.intervalCycle.cycle 0).trans
    (evenCycleIso β α h.sourceIso)
  targetIso := (intervalEvenCycleFibreIso β h.intervalCycle.carrier α h.intervalCycle.cycle 1).trans
    (evenCycleIso β α h.targetIso)

/-- The actual odd full witness is transported through the same arbitrary
interval-module construction and whole-cycle endpoint unitaries. -/
def oddFullHomotopy
    {c d : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β}
    (h : FullOddKasparovHomotopy c d) :
    FullOddKasparovHomotopy (bundledOddCycle β α c) (bundledOddCycle β α d) where
  intervalCycle := BundledOddKasparovCycle.of
    (intervalOddCycle β h.intervalCycle.carrier α h.intervalCycle.cycle)
  sourceIso := (intervalOddCycleFibreIso β h.intervalCycle.carrier α h.intervalCycle.cycle 0).trans
    (oddCycleIso β α h.sourceIso)
  targetIso := (intervalOddCycleFibreIso β h.intervalCycle.carrier α h.intervalCycle.cycle 1).trans
    (oddCycleIso β α h.targetIso)

end BC4lean.KKTheory.KasparovDescent
