import BC4lean.CliffordExternalOddForm
import BC4lean.CliffordExternalOddGrading
import BC4lean.CliffordExternalOddSource
import BC4lean.CliffordExternalOddAction

/-! # Completion of the genuine odd external Clifford module

The actual algebraic module tensor has the full graded external form proved
in `CliffordExternalOddForm`. Its bijective completed row coordinates supply
the induced Hilbert-module norm and prove completeness. The coefficient
action below is the proved Koszul action on elementary tensors, and the
unitary preserves the entire coefficient-valued inner product.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordExternalOddHilbertModule
open scoped InnerProductSpace TensorProduct
open CliffordExternalOddCoordinates

variable {C H : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H]
  [CStarModule Cᵐᵒᵖ H] [CompleteSpace H]

local instance cliffordExternalOddHilbertModuleLocalInstance1 : CompleteSpace (HilbertModuleSum C H H) := hilbertModuleSum_complete

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 200000 in
instance normedAddCommGroup : NormedAddCommGroup (ExternalTensor (C := C) (H := H)) :=
  NormedAddCommGroup.induced
    (ExternalTensor (C := C) (H := H)) (ExternalModule (C := C) (H := H))
    (coordinates (C := C) (H := H)) (coordinates (C := C) (H := H)).injective

instance normedSpace : NormedSpace ℂ (ExternalTensor (C := C) (H := H)) :=
  NormedSpace.induced ℂ _ _ coordinates

instance coefficientSMul : SMul (GradedMatrixMoritaMatrix C)ᵐᵒᵖ
    (ExternalTensor (C := C) (H := H)) where
  smul a x := coordinates.symm (a • coordinates x)

@[simp] theorem coordinates_op_smul (a : (GradedMatrixMoritaMatrix C)ᵐᵒᵖ)
    (x : ExternalTensor (C := C) (H := H)) :
    coordinates (a • x) = a • coordinates x := coordinates.apply_symm_apply _

@[simp] theorem norm_eq_tensorNorm (x : ExternalTensor (C := C) (H := H)) :
    ‖x‖ = tensorNorm x := rfl

set_option maxHeartbeats 1200000 in
instance cStarModule : CStarModule (GradedMatrixMoritaMatrix C)ᵐᵒᵖ
    (ExternalTensor (C := C) (H := H)) where
  inner x y := ⟪coordinates x, coordinates y⟫_((GradedMatrixMoritaMatrix C)ᵐᵒᵖ)
  inner_add_right := by
    intro x y z
    simp only [map_add]
    exact CStarModule.inner_add_right
      (A := (GradedMatrixMoritaMatrix C)ᵐᵒᵖ) (E := ExternalModule (C := C) (H := H))
      (x := coordinates x) (y := coordinates y) (z := coordinates z)
  inner_self_nonneg := by
    intro x
    exact CStarModule.inner_self_nonneg
      (A := (GradedMatrixMoritaMatrix C)ᵐᵒᵖ) (E := ExternalModule (C := C) (H := H))
      (x := coordinates x)
  inner_self := by
    intro x
    change (⟪coordinates x, coordinates x⟫_((GradedMatrixMoritaMatrix C)ᵐᵒᵖ) = 0 ↔ x = 0)
    rw [CStarModule.inner_self
      (A := (GradedMatrixMoritaMatrix C)ᵐᵒᵖ) (E := ExternalModule (C := C) (H := H))
      (x := coordinates x)]
    constructor
    · intro h
      apply coordinates.injective
      simpa only [map_zero] using h
    · intro h
      simp only [h, map_zero]
  inner_op_smul_right := by
    intro a x y
    change ⟪coordinates x, coordinates (a • y)⟫_((GradedMatrixMoritaMatrix C)ᵐᵒᵖ) =
      a * ⟪coordinates x, coordinates y⟫_((GradedMatrixMoritaMatrix C)ᵐᵒᵖ)
    rw [coordinates_op_smul (C := C) (H := H) a y]
    exact CStarModule.inner_op_smul_right
      (A := (GradedMatrixMoritaMatrix C)ᵐᵒᵖ) (E := ExternalModule (C := C) (H := H))
      (a := a) (x := coordinates x) (y := coordinates y)
  inner_smul_right_complex := by
    intro a x y
    simp only [map_smul]
    exact CStarModule.inner_smul_right_complex
      (A := (GradedMatrixMoritaMatrix C)ᵐᵒᵖ) (E := ExternalModule (C := C) (H := H))
      (z := a) (x := coordinates x) (y := coordinates y)
  star_inner x y := CStarModule.star_inner
    (A := (GradedMatrixMoritaMatrix C)ᵐᵒᵖ) (E := ExternalModule (C := C) (H := H))
    (coordinates x) (coordinates y)
  norm_eq_sqrt_norm_inner_self x :=
    CStarModule.norm_eq_sqrt_norm_inner_self
      (A := (GradedMatrixMoritaMatrix C)ᵐᵒᵖ) (E := ExternalModule (C := C) (H := H))
      (coordinates x)

def coordinateIsometryEquiv : ExternalTensor (C := C) (H := H) ≃ₗᵢ[ℂ]
    ExternalModule (C := C) (H := H) where
  toLinearEquiv := coordinates
  norm_map' _ := rfl

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 200000 in
instance completeSpace : CompleteSpace (ExternalTensor (C := C) (H := H)) :=
  (coordinateIsometryEquiv (C := C) (H := H)).toIsometryEquiv.completeSpace

/-- The genuine completed external module is unitarily the actual row tensor. -/
def hilbertEquiv : HilbertModuleEquiv (GradedMatrixMoritaMatrix C)
    (ExternalTensor (C := C) (H := H)) (ExternalModule (C := C) (H := H)) where
  linearIsometryEquiv := coordinateIsometryEquiv
  inner_map _ _ := rfl

/-- The coefficient action has the genuine pure Koszul formula. -/
theorem op_smul_tmul (a : C × C) (z w : CliffordOne) (y : CliffordPairModule C H) :
    MulOpposite.op (CliffordExternalOddCoefficient.pureMatrix a w) • (y ⊗ₜ[ℂ] z) =
      (MulOpposite.op a • y) ⊗ₜ[ℂ] (CliffordTwo.evenPart z * w) +
        (MulOpposite.op (a.2, a.1) • y) ⊗ₜ[ℂ] (CliffordTwo.oddPart z * w) := by
  apply coordinates.injective
  rw [coordinates_op_smul, CliffordExternalOddModule.coordinates_right_tmul]

/-- The full module pairing is the genuine pure graded tensor pairing. -/
theorem inner_tmul (x y : CliffordPairModule C H) (z w : CliffordOne) :
    MulOpposite.unop ⟪x ⊗ₜ[ℂ] z, y ⊗ₜ[ℂ] w⟫_((GradedMatrixMoritaMatrix C)ᵐᵒᵖ) =
      CliffordExternalOddCoefficient.coordinates
        ((MulOpposite.unop ⟪x, y⟫_((C × C)ᵐᵒᵖ)) ⊗ₜ[ℂ]
          (CliffordTwo.evenPart (star z) * w) +
        ((MulOpposite.unop ⟪x, y⟫_((C × C)ᵐᵒᵖ)).2,
          (MulOpposite.unop ⟪x, y⟫_((C × C)ᵐᵒᵖ)).1) ⊗ₜ[ℂ]
          (CliffordTwo.oddPart (star z) * w)) :=
  CliffordExternalOddForm.coordinates_inner_tmul x y z w

end BC4lean.KKTheory.CliffordExternalOddHilbertModule
