import BC4lean.GroupUniverseMatrixMoritaTransport
import BC4lean.GroupUniverseEvenBridge
import BC4lean.PositiveGradedULiftFullWitness
import BC4lean.GradedMatrixMoritaSeparable

/-! # Genuine matrix Morita quotient maps with independent universes

Both maps tensor whole cycles and arbitrary full interval witnesses with
the actual row or column module. A tensor raises uE to max(uE,uB), and
the genuine double-tensor contraction identifies each roundtrip with the
actual ULift of its input. Hence at the common module universe containing
uB these maps are inverse additive equivalences. The even bridge uses the
actual trivial-grading full-witness conversion and the true column map.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory.GroupUniverseMatrixMoritaBridge
open GroupUniverseMatrixMoritaTransport GradedMatrixMoritaEquivariant
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {δA : CStarGrading A}

def toMatrixClass :
    GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α β δA CStarGrading.trivial →
    GradedKasparovHomotopyClass.{uΓ,uA,uB,max uE uB} α (matrixAction β)
      δA GradedMatrixMoritaMatrix.grading :=
  Quotient.lift (fun c => GradedKasparovHomotopyClass.mk (toMatrix β c)) (by
    intro c d h
    obtain ⟨h⟩ := h
    exact GradedKasparovHomotopyClass.mk_eq_of_full (toMatrixFull β h))

def toCoefficientClass :
    GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α (matrixAction β)
      δA GradedMatrixMoritaMatrix.grading →
    GradedKasparovHomotopyClass.{uΓ,uA,uB,max uE uB} α β δA CStarGrading.trivial :=
  Quotient.lift (fun c => GradedKasparovHomotopyClass.mk (toCoefficient β c)) (by
    intro c d h
    obtain ⟨h⟩ := h
    exact GradedKasparovHomotopyClass.mk_eq_of_full (toCoefficientFull β h))

@[simp] theorem toMatrixClass_mk
    (c : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA CStarGrading.trivial) :
    toMatrixClass (GradedKasparovHomotopyClass.mk c) =
      GradedKasparovHomotopyClass.mk (toMatrix β c) := rfl

@[simp] theorem toCoefficientClass_mk
    (c : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α (matrixAction β)
      δA GradedMatrixMoritaMatrix.grading) :
    toCoefficientClass (GradedKasparovHomotopyClass.mk c) =
      GradedKasparovHomotopyClass.mk (toCoefficient β c) := rfl

theorem toMatrixClass_add
    (x y : GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α β δA CStarGrading.trivial) :
    toMatrixClass (x + y) = toMatrixClass x + toMatrixClass y := by
  refine Quotient.inductionOn₂ x y ?_
  intro c d
  exact GradedKasparovHomotopyClass.mk_eq_of_iso (toMatrixDirectSumIso β c d)

theorem toCoefficientClass_add
    (x y : GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α (matrixAction β)
      δA GradedMatrixMoritaMatrix.grading) :
    toCoefficientClass (x + y) = toCoefficientClass x + toCoefficientClass y := by
  refine Quotient.inductionOn₂ x y ?_
  intro c d
  exact GradedKasparovHomotopyClass.mk_eq_of_iso (toCoefficientDirectSumIso β c d)

theorem coefficient_roundtrip
    (x : GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α β δA CStarGrading.trivial) :
    toCoefficientClass (toMatrixClass x) =
      GradedKasparovHomotopyClass.ulift.{uΓ,uA,uB,uE,uB} x := by
  refine Quotient.inductionOn x ?_
  intro c
  exact GradedKasparovHomotopyClass.mk_eq_of_iso
    ((coefficientInverseIso β c).trans (c.cycle.uliftIso : GradedKasparovCycleIso c.cycle
      (c.ulift : BundledGradedKasparovCycle.{uΓ,uA,uB,max uE uB}
        α β δA CStarGrading.trivial).cycle))

theorem matrix_roundtrip
    (x : GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α (matrixAction β)
      δA GradedMatrixMoritaMatrix.grading) :
    toMatrixClass (toCoefficientClass x) =
      GradedKasparovHomotopyClass.ulift.{uΓ,uA,uB,uE,uB} x := by
  refine Quotient.inductionOn x ?_
  intro c
  exact GradedKasparovHomotopyClass.mk_eq_of_iso
    ((matrixInverseIso β c).trans (c.cycle.uliftIso : GradedKasparovCycleIso c.cycle
      (c.ulift : BundledGradedKasparovCycle.{uΓ,uA,uB,max uE uB}
        α (matrixAction β) δA GradedMatrixMoritaMatrix.grading).cycle))

def addEquivalence :
    GradedKasparovHomotopyClass.{uΓ,uA,uB,max uE uB} α (matrixAction β)
      δA GradedMatrixMoritaMatrix.grading ≃+
    GradedKasparovHomotopyClass.{uΓ,uA,uB,max uE uB} α β δA CStarGrading.trivial where
  toFun := toCoefficientClass
  invFun := toMatrixClass
  left_inv x := (matrix_roundtrip x).trans
    (GradedKasparovHomotopyClass.ulift_eq_self.{uΓ,uA,uB,uE,uB} x)
  right_inv x := (coefficient_roundtrip x).trans
    (GradedKasparovHomotopyClass.ulift_eq_self.{uΓ,uA,uB,uE,uB} x)
  map_add' := toCoefficientClass_add

def evenClass
    (x : GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α (matrixAction β)
      CStarGrading.trivial GradedMatrixMoritaMatrix.grading) :
    KasparovHomotopyClass.{uΓ,uA,uB,max uE uB} α β :=
  GroupUniverseEvenBridge.evenClass (toCoefficientClass x)

theorem evenClass_add
    (x y : GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α (matrixAction β)
      CStarGrading.trivial GradedMatrixMoritaMatrix.grading) :
    evenClass (x + y) = evenClass x + evenClass y := by
  unfold evenClass
  rw [toCoefficientClass_add, GroupUniverseEvenBridge.evenClass_add]

def evenAddEquivalence :
    GradedKasparovHomotopyClass.{uΓ,uA,uB,max uE uB} α (matrixAction β)
      CStarGrading.trivial GradedMatrixMoritaMatrix.grading ≃+
    KasparovHomotopyClass.{uΓ,uA,uB,max uE uB} α β :=
  addEquivalence.trans GroupUniverseEvenBridge.addEquivalence

@[simp] theorem evenAddEquivalence_apply
    (x : GradedKasparovHomotopyClass.{uΓ,uA,uB,max uE uB} α (matrixAction β)
      CStarGrading.trivial GradedMatrixMoritaMatrix.grading) :
    evenAddEquivalence x = evenClass x := rfl

end BC4lean.KKTheory.GroupUniverseMatrixMoritaBridge
