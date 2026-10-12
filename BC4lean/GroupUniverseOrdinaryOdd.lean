import BC4lean.GroupUniverseCoefficientPushforward
import BC4lean.GroupUniverseCliffordCoordinateBridge
import BC4lean.OrdinaryOddCoefficientTensor

/-! # Actual ordinary odd pushforward for independent coefficient universes

The identity-on-cycle coordinate Clifford bridge and the actual generic
coefficient homomorphism-cycle product define this map. The whole completed
pair-tensor cycle unitary proves that its representative is the ordinary
coefficient tensor with operator F⊗1. It is independent of the K-theory
comparison and needs no nondegeneracy or image-complement hypothesis.
-/

noncomputable section
universe uB uC uE
namespace BC4lean.KKTheory.GroupUniverseOrdinaryOdd
variable {B : Type uB} {C : Type uC}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C]

local notation "α₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
local notation "β₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B)
local notation "γ₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit C)
open GroupUniverseCliffordCoordinateBridge

def coefficientPushforwardClass (f : B →⋆ₙₐ[ℂ] C) (x : OddKK.{0, 0, uB, uE} α₁ β₁) :
    OddKK.{0, 0, uC, max uE uC} α₁ γ₁ :=
  oddClass (GroupUniverseCoefficientPushforward.coefficientPushforward
    (cliffordCoefficientAction_preservesGrading β₁) (cliffordCoefficientAction_preservesGrading γ₁)
    (cliffordCoordinateHom f) (fun _ _ => rfl) (fun _ => rfl) (gradedOddClass x))

set_option maxHeartbeats 2000000 in
theorem coefficientPushforwardClass_add (f : B →⋆ₙₐ[ℂ] C)
    (x y : OddKK.{0, 0, uB, uE} α₁ β₁) :
    coefficientPushforwardClass f (x + y) =
      coefficientPushforwardClass f x + coefficientPushforwardClass f y := by
  let p : GradedKasparovHomotopyClass.{0,0,uB,uE} α₁ (cliffordCoefficientAction β₁)
      CStarGrading.trivial cliffordCoefficientGrading →
      GradedKasparovHomotopyClass.{0,0,uC,max uE uC} α₁ (cliffordCoefficientAction γ₁)
        CStarGrading.trivial cliffordCoefficientGrading :=
    GroupUniverseCoefficientPushforward.coefficientPushforward
    (cliffordCoefficientAction_preservesGrading β₁) (cliffordCoefficientAction_preservesGrading γ₁)
    (cliffordCoordinateHom f) (fun _ _ => rfl) (fun _ => rfl)
  have hp := GroupUniverseCoefficientPushforward.coefficientPushforward_add
    (cliffordCoefficientAction_preservesGrading β₁) (cliffordCoefficientAction_preservesGrading γ₁)
    (cliffordCoordinateHom f) (fun _ _ => rfl) (fun _ => rfl)
    (gradedOddClass x) (gradedOddClass y)
  exact (congrArg oddClass ((congrArg p (gradedOddClass_add x y)).trans hp)).trans
    (oddClass_add _ _)

def coefficientPushforward (f : B →⋆ₙₐ[ℂ] C) : OddKK.{0, 0, uB, uE} α₁ β₁ →+
    OddKK.{0, 0, uC, max uE uC} α₁ γ₁ :=
  AddMonoidHom.mk' (coefficientPushforwardClass f) (coefficientPushforwardClass_add f)

@[simp] theorem coefficientPushforward_apply (f : B →⋆ₙₐ[ℂ] C)
    (x : OddKK.{0, 0, uB, uE} α₁ β₁) :
    coefficientPushforward f x = coefficientPushforwardClass f x := rfl

theorem gradedOddClass_coefficientPushforward (f : B →⋆ₙₐ[ℂ] C)
    (x : OddKK.{0, 0, uB, uE} α₁ β₁) :
    gradedOddClass (coefficientPushforward f x) =
      GroupUniverseCoefficientPushforward.coefficientPushforward
        (cliffordCoefficientAction_preservesGrading β₁) (cliffordCoefficientAction_preservesGrading γ₁)
        (cliffordCoordinateHom f) (fun _ _ => rfl) (fun _ => rfl) (gradedOddClass x) :=
  gradedOddClass_oddClass _

set_option maxHeartbeats 2000000 in
theorem coefficientPushforward_mk_coefficientTensor {E : Type uE}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
    [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
    (c : OddKasparovCycle α₁ β₁ E) (f : B →⋆ₙₐ[ℂ] C) :
    coefficientPushforward f (OddKK.mk (BundledOddKasparovCycle.of c)) =
      OddKK.mk (BundledOddKasparovCycle.of (c.coefficientTensor f)) := by
  apply gradedOddClass_injective
  let p : GradedKasparovHomotopyClass.{0,0,uB,uE} α₁ (cliffordCoefficientAction β₁)
      CStarGrading.trivial cliffordCoefficientGrading →
      GradedKasparovHomotopyClass.{0,0,uC,max uE uC} α₁ (cliffordCoefficientAction γ₁)
        CStarGrading.trivial cliffordCoefficientGrading :=
    GroupUniverseCoefficientPushforward.coefficientPushforward
    (cliffordCoefficientAction_preservesGrading β₁) (cliffordCoefficientAction_preservesGrading γ₁)
    (cliffordCoordinateHom f) (fun _ _ => rfl) (fun _ => rfl)
  have hp := GroupUniverseCoefficientPushforward.coefficientPushforward_mk_tensor
    (cliffordCoefficientAction_preservesGrading β₁) (cliffordCoefficientAction_preservesGrading γ₁)
    (cliffordCoordinateHom f) (fun _ _ => rfl) (fun _ => rfl)
    (BundledOddKasparovCycle.of c).cliffordExpansion
  have hi := GradedKasparovHomotopyClass.mk_eq_of_iso
    (c := BundledGradedKasparovCycle.of (OrdinaryOddCoefficientTensor.coordinateProduct c f))
    (d := (BundledOddKasparovCycle.of (c.coefficientTensor f)).cliffordExpansion)
    (OrdinaryOddCoefficientTensor.coordinateProductIso c f)
  exact (gradedOddClass_coefficientPushforward f (OddKK.mk (BundledOddKasparovCycle.of c))).trans
    ((congrArg p (gradedOddClass_mk (BundledOddKasparovCycle.of c))).trans
      (hp.trans (hi.trans
        (gradedOddClass_mk (BundledOddKasparovCycle.of (c.coefficientTensor f))).symm)))

end BC4lean.KKTheory.GroupUniverseOrdinaryOdd
