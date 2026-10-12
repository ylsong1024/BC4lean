import BC4lean.GroupUniverseOddSourceInterval
import BC4lean.GroupUniverseMatrixMoritaTransport
import BC4lean.CliffordOddSourceDirectSumIso
import BC4lean.GradedMatrixMoritaSeparable
import BC4lean.CliffordTensorHom
import BC4lean.OddKasparovHomotopyGroup
import BC4lean.GradedKasparovSourcePullbackClass

/-! # Genuine external odd extension with independent universes

The actual Pauli source cycle is tensored with the true row module. Its
module universe is max(uE,uC). The same arbitrary odd interval witness is
transported through the real evaluated fibre and row tensor unitaries.
Addition uses the actual four-coordinate shuffle and completed tensor sum
unitary, and source pullback uses the true complete Clifford equivalence.
-/

noncomputable section
universe uΓ uB uC uE
namespace BC4lean.KKTheory.GroupUniverseExternalOddClass
open GradedMatrixMoritaEquivariant GroupUniverseMatrixMoritaTransport
variable {Γ : Type uΓ} {B : Type uB} {C : Type uC} [Group Γ]
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder C] [StarOrderedRing C] [TopologicalSpace.SeparableSpace C]
  {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

def cycle {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Cᵐᵒᵖ E]
    [CStarModule Cᵐᵒᵖ E] [CompleteSpace E] (c : OddKasparovCycle β γ E) :=
  GradedMatrixMoritaCycle.coefficientToMatrix γ (CliffordOddSourceCycle.cycle c)

def full {c d : BundledOddKasparovCycle.{uΓ,uB,uC,uE} β γ}
    (h : FullOddKasparovHomotopy c d) :
    FullGradedKasparovHomotopy
      (BundledGradedKasparovCycle.of (cycle c.cycle))
      (BundledGradedKasparovCycle.of (cycle d.cycle)) := by
  let transported := toMatrixFull
    (Γ := Γ) (A := B × B) (B := C)
    (α := cliffordCoefficientAction β)
    (δA := (cliffordCoefficientGrading : CStarGrading (B × B))) γ
    (GroupUniverseOddSourceCycle.full (β := β) (γ := γ) (c := c) (d := d) h)
  exact {
    intervalCycle := transported.intervalCycle
    sourceIso := transported.sourceIso
    targetIso := transported.targetIso }

def coordinateClass : OddKK.{uΓ,uB,uC,uE} β γ →
    GradedKasparovHomotopyClass.{uΓ,uB,uC,max uE uC}
      (cliffordCoefficientAction β) (matrixAction γ)
      cliffordCoefficientGrading GradedMatrixMoritaMatrix.grading :=
  Quotient.lift (fun c : BundledOddKasparovCycle.{uΓ,uB,uC,uE} β γ =>
    GradedKasparovHomotopyClass.mk (.of (cycle c.cycle))) (by
      intro c d h
      obtain ⟨h⟩ := h
      exact GradedKasparovHomotopyClass.mk_eq_of_full (full h))

@[simp] theorem coordinateClass_mk (c : BundledOddKasparovCycle.{uΓ,uB,uC,uE} β γ) :
    coordinateClass (OddKK.mk c) = GradedKasparovHomotopyClass.mk (.of (cycle c.cycle)) := rfl

set_option maxHeartbeats 1200000 in
theorem coordinateClass_add (x y : OddKK.{uΓ,uB,uC,uE} β γ) :
    coordinateClass (x + y) = coordinateClass x + coordinateClass y := by
  refine Quotient.inductionOn₂ x y ?_
  intro c d
  change coordinateClass (OddKK.mk c + OddKK.mk d) =
    coordinateClass (OddKK.mk c) + coordinateClass (OddKK.mk d)
  rw [← OddKK.mk_directSum, coordinateClass_mk, coordinateClass_mk, coordinateClass_mk,
    ← GradedKasparovHomotopyClass.mk_directSum]
  let first := toMatrixIso
    (Γ := Γ) (A := B × B) (B := C)
    (α := cliffordCoefficientAction β)
    (δA := (cliffordCoefficientGrading : CStarGrading (B × B)))
    (c := BundledGradedKasparovCycle.of
      (CliffordOddSourceCycle.cycle (c.cycle.directSum d.cycle)))
    (d := BundledGradedKasparovCycle.of
      ((CliffordOddSourceCycle.cycle c.cycle).directSum
        (CliffordOddSourceCycle.cycle d.cycle))) γ
    (CliffordOddSourceCycle.directSumIso c.cycle d.cycle)
  let second := toMatrixDirectSumIso
    (Γ := Γ) (A := B × B) (B := C)
    (α := cliffordCoefficientAction β)
    (δA := (cliffordCoefficientGrading : CStarGrading (B × B))) γ
    (.of (CliffordOddSourceCycle.cycle c.cycle))
    (.of (CliffordOddSourceCycle.cycle d.cycle))
  exact GradedKasparovHomotopyClass.mk_eq_of_iso (first.trans second)

def externalClass (x : OddKK.{uΓ,uB,uC,uE} β γ) :
    GradedKasparovHomotopyClass.{uΓ,uB,uC,max uE uC} (cliffordTensorAction β) (matrixAction γ)
      cliffordTensorGrading GradedMatrixMoritaMatrix.grading :=
  GradedKasparovHomotopyClass.sourcePullback
    (α := cliffordCoefficientAction β) (β := matrixAction γ)
    (δA := (cliffordCoefficientGrading : CStarGrading (B × B)))
    (δB := GradedMatrixMoritaMatrix.grading)
    (cliffordTensorAction β) cliffordTensorGrading
    (cliffordTensorAction_preservesGrading β)
    (cliffordTensorCoordinateStarAlgEquiv (B := B)).toNonUnitalStarAlgHom
    (fun g a => cliffordTensorCoordinate_action β g a)
    (fun a => cliffordTensorCoordinate_grading (B := B) a) (coordinateClass x)

theorem externalClass_add (x y : OddKK.{uΓ,uB,uC,uE} β γ) :
    externalClass (x + y) = externalClass x + externalClass y := by
  unfold externalClass
  rw [coordinateClass_add]
  erw [GradedKasparovHomotopyClass.sourcePullback_add]

end BC4lean.KKTheory.GroupUniverseExternalOddClass
