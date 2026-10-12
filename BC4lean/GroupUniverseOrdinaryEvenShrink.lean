import BC4lean.GroupUniverseOrdinaryEven
import BC4lean.GroupShrinkEvenBridge
import BC4lean.OrdinaryScalarCoefficientTensorIso

/-! # Genuine even coefficient pushforward commutes with module shrinking

The source shrinking unitary induces the actual whole first-factor tensor
unitary. Composing it with the inverse of the target shrinking unitary
identifies the two raw representatives. Both sides therefore coincide in
the existing full-homotopy quotient; the coefficient map remains the
independently defined homomorphism-cycle product.
-/

noncomputable section
universe uB uC uE v
namespace BC4lean.KKTheory.GroupUniverseOrdinaryEven
variable {B : Type uB} {C : Type uC}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C]
local notation "α₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
local notation "β₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B)
local notation "γ₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit C)

/-- Arbitrary source and target module universes are compared by actual whole
cycle unitaries, with the tensor's true target universe `max v uC`. -/
theorem coefficientPushforward_shrink (f : B →⋆ₙₐ[ℂ] C)
    (x : KasparovHomotopyClass.{0, 0, uB, uE} α₁ β₁) :
    GroupShrinkEvenBridge.addEquivalence.{0, 0, uC, max uE uC, max v uC}
      (coefficientPushforward f x) =
    coefficientPushforward f
      (GroupShrinkEvenBridge.addEquivalence.{0, 0, uB, uE, v} x) := by
  refine Quotient.inductionOn x ?_
  intro c
  let d : BundledKasparovCycle.{0, 0, uB, v} α₁ β₁ := c.shrink
  let t : BundledKasparovCycle.{0, 0, uC, max uE uC} α₁ γ₁ :=
    BundledKasparovCycle.of (c.cycle.scalarCoefficientTensor f)
  change GroupShrinkEvenBridge.addEquivalence
      (coefficientPushforward f (KasparovHomotopyClass.mk (BundledKasparovCycle.of c.cycle))) =
    coefficientPushforward f (GroupShrinkEvenBridge.addEquivalence (KasparovHomotopyClass.mk c))
  rw [coefficientPushforward_mk_scalarCoefficientTensor,
    GroupShrinkEvenBridge.addEquivalence_mk, GroupShrinkEvenBridge.addEquivalence_mk]
  change KasparovHomotopyClass.mk
      (t.shrink : BundledKasparovCycle.{0, 0, uC, max v uC} α₁ γ₁) =
    coefficientPushforward f (KasparovHomotopyClass.mk (BundledKasparovCycle.of d.cycle))
  rw [coefficientPushforward_mk_scalarCoefficientTensor]
  exact KasparovHomotopyClass.mk_eq_of_iso
    ((t.shrinkIso : KasparovCycleIso t.cycle
      (t.shrink : BundledKasparovCycle.{0, 0, uC, max v uC} α₁ γ₁).cycle).symm.trans
      ((c.shrinkIso : KasparovCycleIso c.cycle d.cycle).scalarCoefficientTensor f))

/-- In particular, the source can be placed in module universe zero and the
actual target product in the coefficient universe `uC`. -/
theorem coefficientPushforward_shrink_zero (f : B →⋆ₙₐ[ℂ] C)
    (x : KasparovHomotopyClass.{0, 0, uB, uE} α₁ β₁) :
    GroupShrinkEvenBridge.addEquivalence.{0, 0, uC, max uE uC, uC}
      (coefficientPushforward f x) =
    coefficientPushforward f
      (GroupShrinkEvenBridge.addEquivalence.{0, 0, uB, uE, 0} x) :=
  coefficientPushforward_shrink.{uB, uC, uE, 0} f x

end BC4lean.KKTheory.GroupUniverseOrdinaryEven
