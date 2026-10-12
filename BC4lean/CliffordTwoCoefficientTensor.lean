import BC4lean.CliffordTwoUnital
import BC4lean.GradedMatrixMoritaMatrix
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Algebra.Star.TensorProduct

/-! # The actual Cl₂ coefficient tensor over trivially graded B

The actual complex tensor B ⊗ Cl₂ maps bijectively to the actual operator-norm
matrix algebra M₂(B), by b ⊗ M ↦ (Mᵢⱼ b). Its multiplication, tensor star and
grading are proved in those coordinates. Completeness is the genuine matrix
C⋆ completeness. B is trivially graded; the earlier Koszul tensor supplies
Cl₂ itself and is kept separate from this ordinary coefficient tensor.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped TensorProduct

namespace CliffordTwoCoefficientTensor

def matrixEntries {C : Type*} [AddCommGroup C] [Module ℂ C] :
    CStarMatrix (Fin 2) (Fin 2) C ≃ₗ[ℂ] ((Fin 2 × Fin 2) → C) where
  toFun M k := M k.1 k.2
  invFun f := CStarMatrix.ofMatrix fun i j => f (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- An actual linear bijection from the algebraic tensor to coefficient matrices. -/
def algebraicCoordinates : (B ⊗[ℂ] CliffordTwo) ≃ₗ[ℂ] GradedMatrixMoritaMatrix B :=
  (TensorProduct.congr (LinearEquiv.refl ℂ B) matrixEntries).trans
    ((TensorProduct.piScalarRight ℂ ℂ B (Fin 2 × Fin 2)).trans matrixEntries.symm)

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem algebraicCoordinates_tmul (b : B) (M : CliffordTwo) :
    algebraicCoordinates (b ⊗ₜ[ℂ] M) = CStarMatrix.ofMatrix fun i j => M i j • b := by
  simp [algebraicCoordinates, matrixEntries, TensorProduct.congr_tmul]
  rfl

omit [PartialOrder B] [StarOrderedRing B] in
theorem algebraicCoordinates_star (x : B ⊗[ℂ] CliffordTwo) :
    algebraicCoordinates (star x) = star (algebraicCoordinates x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b M =>
    ext i j
    simp only [TensorProduct.star_tmul, algebraicCoordinates_tmul, CStarMatrix.star_apply]
    change star (M j i) • star b = star (M j i • b)
    exact (star_smul (M j i) b).symm
  | add x y hx hy => simp only [star_add, map_add, hx, hy]

end CliffordTwoCoefficientTensor

def CliffordTwoCoefficientTensor (B : Type*) [NonUnitalCStarAlgebra B] := B ⊗[ℂ] CliffordTwo

namespace CliffordTwoCoefficientTensor

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

instance addCommGroup : AddCommGroup (CliffordTwoCoefficientTensor B) :=
  inferInstanceAs (AddCommGroup (B ⊗[ℂ] CliffordTwo))
instance complexModule : Module ℂ (CliffordTwoCoefficientTensor B) :=
  inferInstanceAs (Module ℂ (B ⊗[ℂ] CliffordTwo))
instance star : Star (CliffordTwoCoefficientTensor B) :=
  inferInstanceAs (Star (B ⊗[ℂ] CliffordTwo))

local notation "star" => Star.star

def coordinates : CliffordTwoCoefficientTensor B ≃ₗ[ℂ] GradedMatrixMoritaMatrix B := algebraicCoordinates
def tensor (b : B) (M : CliffordTwo) : CliffordTwoCoefficientTensor B := b ⊗ₜ[ℂ] M

instance mul : Mul (CliffordTwoCoefficientTensor B) :=
  ⟨fun x y => coordinates.symm (coordinates x * coordinates y)⟩

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem coordinates_mul (x y : CliffordTwoCoefficientTensor B) :
    coordinates (x * y) = coordinates x * coordinates y := coordinates.apply_symm_apply _
omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem coordinates_star (x : CliffordTwoCoefficientTensor B) :
    coordinates (star x) = star (coordinates x) := algebraicCoordinates_star x
omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem coordinates_tensor (b : B) (M : CliffordTwo) :
    coordinates (tensor b M) = CStarMatrix.ofMatrix fun i j => M i j • b := algebraicCoordinates_tmul b M

omit [PartialOrder B] [StarOrderedRing B] in
/-- The constructed product has the actual ordinary tensor formula, since B is even. -/
theorem tensor_mul (b c : B) (M N : CliffordTwo) :
    tensor b M * tensor c N = tensor (b * c) (M * N) := by
  apply coordinates.injective
  simp only [coordinates_mul, coordinates_tensor]
  ext i j
  simp only [CStarMatrix.mul_apply, Finset.sum_smul]
  change (∑ k : Fin 2, (M i k • b) * (N k j • c)) =
    ∑ k : Fin 2, (M i k * N k j) • (b * c)
  apply Finset.sum_congr rfl
  intro k _
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [mul_comm (N k j) (M i k)]

instance nonUnitalRing : NonUnitalRing (CliffordTwoCoefficientTensor B) :=
  coordinates.injective.nonUnitalRing coordinates (map_zero _) (map_add _) coordinates_mul
    (map_neg _) (map_sub _) (fun n x => map_nsmul _ n x) (fun n x => map_zsmul _ n x)
instance starRing : StarRing (CliffordTwoCoefficientTensor B) :=
  coordinates.injective.starRing coordinates coordinates_star (map_add _) coordinates_mul

instance normedAddCommGroup : NormedAddCommGroup (CliffordTwoCoefficientTensor B) := by
  letI : SeminormedAddCommGroup (CliffordTwoCoefficientTensor B) :=
    SeminormedAddCommGroup.induced _ _ coordinates
  exact NormedAddCommGroup.ofSeparation (fun x hx =>
    coordinates.injective (by simpa only [map_zero] using norm_eq_zero.mp hx))

@[simp] theorem norm_coordinates (x : CliffordTwoCoefficientTensor B) : ‖coordinates x‖ = ‖x‖ := rfl

instance normedSpace : NormedSpace ℂ (CliffordTwoCoefficientTensor B) where
  norm_smul_le z x := by
    change ‖coordinates (z • x)‖ ≤ ‖z‖ * ‖coordinates x‖
    rw [map_smul]
    exact norm_smul_le z (coordinates x)

instance nonUnitalNormedRing : NonUnitalNormedRing (CliffordTwoCoefficientTensor B) where
  toNonUnitalRing := nonUnitalRing
  toMetricSpace := inferInstance
  norm := (‖·‖)
  dist_eq x y := dist_eq_norm_neg_add x y
  norm_mul_le x y := by
    change ‖coordinates (x * y)‖ ≤ ‖coordinates x‖ * ‖coordinates y‖
    rw [coordinates_mul]
    exact norm_mul_le _ _

instance starModule : StarModule ℂ (CliffordTwoCoefficientTensor B) where
  star_smul z x := by
    apply coordinates.injective
    rw [coordinates_star, map_smul, star_smul, map_smul, coordinates_star]
instance scalarTower : IsScalarTower ℂ (CliffordTwoCoefficientTensor B) (CliffordTwoCoefficientTensor B) where
  smul_assoc z x y := by
    apply coordinates.injective
    change coordinates ((z • x) * y) = coordinates (z • (x * y))
    rw [coordinates_mul, map_smul, map_smul, coordinates_mul, smul_mul_assoc]
instance smulCommClass : SMulCommClass ℂ (CliffordTwoCoefficientTensor B) (CliffordTwoCoefficientTensor B) where
  smul_comm z x y := by
    apply coordinates.injective
    change coordinates (z • (x * y)) = coordinates (x * (z • y))
    rw [map_smul, coordinates_mul, coordinates_mul, map_smul, mul_smul_comm]
instance cstarRing : CStarRing (CliffordTwoCoefficientTensor B) where
  norm_mul_self_le x := by
    change ‖coordinates x‖ * ‖coordinates x‖ ≤ ‖coordinates (star x * x)‖
    rw [coordinates_mul, coordinates_star, CStarRing.norm_star_mul_self]

def coordinateLinearIsometry : CliffordTwoCoefficientTensor B ≃ₗᵢ[ℂ] GradedMatrixMoritaMatrix B where
  toLinearEquiv := coordinates
  norm_map' _ := rfl
instance completeSpace : CompleteSpace (CliffordTwoCoefficientTensor B) :=
  coordinateLinearIsometry.toIsometryEquiv.completeSpace
instance nonUnitalCStarAlgebra : NonUnitalCStarAlgebra (CliffordTwoCoefficientTensor B) where

def coordinateStarAlgEquiv : CliffordTwoCoefficientTensor B ≃⋆ₐ[ℂ] GradedMatrixMoritaMatrix B where
  toEquiv := coordinates.toEquiv
  map_add' := coordinates.map_add
  map_mul' := coordinates_mul
  map_star' := coordinates_star
  map_smul' := coordinates.map_smul

def grading : CStarGrading (CliffordTwoCoefficientTensor B) where
  automorphism := coordinateStarAlgEquiv.trans
    (GradedMatrixMoritaMatrix.parityEquiv.trans coordinateStarAlgEquiv.symm)
  involutive x :=
    (coordinateStarAlgEquiv.trans
      (GradedMatrixMoritaMatrix.parityEquiv.trans coordinateStarAlgEquiv.symm)).symm_apply_apply x

/-- Matrix parity is precisely the Cl₂ tensor-factor grading. -/
theorem grading_tensor (b : B) (M : CliffordTwo) :
    grading.automorphism (tensor b M) = tensor b (CliffordTwo.grading.automorphism M) := by
  have hparity : CliffordTwo.grading.automorphism M =
      CStarMatrix.ofMatrix !![M 0 0, -M 0 1; -M 1 0, M 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CliffordTwo.grading, CliffordTwo.parityConjugation,
        CliffordTwo.parity, CStarMatrix.mul_apply, Fin.sum_univ_two]
  apply coordinates.injective
  have hδ (x : CliffordTwoCoefficientTensor B) :
      coordinates (grading.automorphism x) = GradedMatrixMoritaMatrix.parity (coordinates x) :=
    coordinateStarAlgEquiv.apply_symm_apply _
  rw [hδ]
  simp only [coordinates_tensor]
  rw [hparity]
  ext i j
  fin_cases i <;> fin_cases j
  · change M 0 0 • b = M 0 0 • b
    rfl
  · change -(M 0 1 • b) = (-M 0 1) • b
    exact (neg_smul (M 0 1) b).symm
  · change -(M 1 0 • b) = (-M 1 0) • b
    exact (neg_smul (M 1 0) b).symm
  · change M 1 1 • b = M 1 1 • b
    rfl

end CliffordTwoCoefficientTensor
end BC4lean.KKTheory
