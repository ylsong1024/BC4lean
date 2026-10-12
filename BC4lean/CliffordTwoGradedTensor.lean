import BC4lean.CliffordTwoCoordinates

/-! # The genuine Koszul-twisted Cl₁ ⊗̂ Cl₁ C⋆ tensor

The underlying complex vector space is Mathlib's actual algebraic tensor.
Multiplication and star are the proved Pauli-coordinate transports, and the
pure tensor formulas below identify them with the Koszul twist. In particular
the two odd generators anticommute. The actual C⋆ norm and completeness come
from the bijective Pauli coordinates and their operator norm.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped TensorProduct

def CliffordTwoGradedTensor := CliffordOne ⊗[ℂ] CliffordOne

namespace CliffordTwoGradedTensor

instance addCommGroup : AddCommGroup CliffordTwoGradedTensor :=
  inferInstanceAs (AddCommGroup (CliffordOne ⊗[ℂ] CliffordOne))

instance complexModule : Module ℂ CliffordTwoGradedTensor :=
  inferInstanceAs (Module ℂ (CliffordOne ⊗[ℂ] CliffordOne))

def coordinates : CliffordTwoGradedTensor ≃ₗ[ℂ] CliffordTwo := CliffordTwo.tensorPauliCoordinates
def tensor (z w : CliffordOne) : CliffordTwoGradedTensor := z ⊗ₜ[ℂ] w

instance mul : Mul CliffordTwoGradedTensor :=
  ⟨fun x y => coordinates.symm (coordinates x * coordinates y)⟩
instance gradedTensorStar : Star CliffordTwoGradedTensor :=
  ⟨fun x => coordinates.symm (star (coordinates x))⟩

@[simp] theorem coordinates_mul (x y : CliffordTwoGradedTensor) :
    coordinates (x * y) = coordinates x * coordinates y := coordinates.apply_symm_apply _

@[simp] theorem coordinates_star (x : CliffordTwoGradedTensor) :
    coordinates (star x) = star (coordinates x) := coordinates.apply_symm_apply _

instance nonUnitalRing : NonUnitalRing CliffordTwoGradedTensor :=
  coordinates.injective.nonUnitalRing coordinates (map_zero _) (map_add _) coordinates_mul
    (map_neg _) (map_sub _) (fun n x => map_nsmul _ n x) (fun n x => map_zsmul _ n x)

instance starRing : StarRing CliffordTwoGradedTensor :=
  coordinates.injective.starRing coordinates coordinates_star (map_add _) coordinates_mul

instance normedAddCommGroup : NormedAddCommGroup CliffordTwoGradedTensor := by
  letI : SeminormedAddCommGroup CliffordTwoGradedTensor := SeminormedAddCommGroup.induced _ _ coordinates
  exact NormedAddCommGroup.ofSeparation (fun x hx =>
    coordinates.injective (by simpa only [map_zero] using norm_eq_zero.mp hx))

@[simp] theorem norm_coordinates (x : CliffordTwoGradedTensor) : ‖coordinates x‖ = ‖x‖ := rfl

instance normedSpace : NormedSpace ℂ CliffordTwoGradedTensor where
  norm_smul_le z x := by
    change ‖coordinates (z • x)‖ ≤ ‖z‖ * ‖coordinates x‖
    rw [map_smul]
    exact norm_smul_le z (coordinates x)

instance nonUnitalNormedRing : NonUnitalNormedRing CliffordTwoGradedTensor where
  toNonUnitalRing := nonUnitalRing
  toMetricSpace := inferInstance
  norm := (‖·‖)
  dist_eq x y := dist_eq_norm_neg_add x y
  norm_mul_le x y := by
    change ‖coordinates (x * y)‖ ≤ ‖coordinates x‖ * ‖coordinates y‖
    rw [coordinates_mul]
    exact norm_mul_le _ _

instance starModule : StarModule ℂ CliffordTwoGradedTensor where
  star_smul z x := by
    apply coordinates.injective
    rw [coordinates_star, map_smul, star_smul, map_smul, coordinates_star]

instance scalarTower : IsScalarTower ℂ CliffordTwoGradedTensor CliffordTwoGradedTensor where
  smul_assoc z x y := by
    apply coordinates.injective
    change coordinates ((z • x) * y) = coordinates (z • (x * y))
    rw [coordinates_mul, map_smul, map_smul, coordinates_mul, smul_mul_assoc]

instance smulCommClass : SMulCommClass ℂ CliffordTwoGradedTensor CliffordTwoGradedTensor where
  smul_comm z x y := by
    apply coordinates.injective
    change coordinates (z • (x * y)) = coordinates (x * (z • y))
    rw [map_smul, coordinates_mul, coordinates_mul, map_smul, mul_smul_comm]

instance cstarRing : CStarRing CliffordTwoGradedTensor where
  norm_mul_self_le x := by
    change ‖coordinates x‖ * ‖coordinates x‖ ≤ ‖coordinates (star x * x)‖
    rw [coordinates_mul, coordinates_star, CStarRing.norm_star_mul_self]

def coordinateLinearIsometry : CliffordTwoGradedTensor ≃ₗᵢ[ℂ] CliffordTwo where
  toLinearEquiv := coordinates
  norm_map' _ := rfl

instance completeSpace : CompleteSpace CliffordTwoGradedTensor :=
  coordinateLinearIsometry.toIsometryEquiv.completeSpace

instance nonUnitalCStarAlgebra : NonUnitalCStarAlgebra CliffordTwoGradedTensor where
  norm_mul_self_le x := cstarRing.norm_mul_self_le x

/-- The actual complete graded tensor is star-isomorphic to M₂(ℂ). -/
def coordinateStarAlgEquiv : CliffordTwoGradedTensor ≃⋆ₐ[ℂ] CliffordTwo where
  toEquiv := coordinates.toEquiv
  map_add' := coordinates.map_add
  map_mul' := coordinates_mul
  map_star' := coordinates_star
  map_smul' := coordinates.map_smul

@[simp] theorem coordinates_tensor (z w : CliffordOne) :
    coordinates (tensor z w) = CliffordTwo.fromCoefficients
      ((CliffordTwo.evenCoefficient z * CliffordTwo.evenCoefficient w,
        CliffordTwo.oddCoefficient z * CliffordTwo.evenCoefficient w),
       (CliffordTwo.evenCoefficient z * CliffordTwo.oddCoefficient w,
        CliffordTwo.oddCoefficient z * CliffordTwo.oddCoefficient w)) :=
  CliffordTwo.tensorPauliCoordinates_tmul z w

/-- The full pure tensor multiplication formula includes its actual Koszul twist. -/
theorem tensor_mul (z w z' w' : CliffordOne) :
    tensor z w * tensor z' w' =
      tensor (z * z') (CliffordTwo.evenPart w * w') +
        tensor (z * CliffordOne.grading.automorphism z') (CliffordTwo.oddPart w * w') := by
  apply coordinates.injective
  rw [coordinates_mul, map_add]
  simp only [coordinates_tensor]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CliffordTwo.fromCoefficients, CliffordTwo.evenCoefficient, CliffordTwo.oddCoefficient,
      CliffordTwo.evenPart, CliffordTwo.oddPart, CliffordOne.grading, CliffordOne.swap,
      CliffordOne.epsilon, CStarMatrix.mul_apply, Fin.sum_univ_two, smul_eq_mul] <;>
    ring_nf <;> simp only [Complex.I_sq] <;> ring

/-- The C⋆ star includes the Koszul sign on an odd-odd pure tensor. -/
theorem star_tensor (z w : CliffordOne) :
    star (tensor z w) =
      tensor (star z) (CliffordTwo.evenPart (star w)) +
        tensor (CliffordOne.grading.automorphism (star z)) (CliffordTwo.oddPart (star w)) := by
  apply coordinates.injective
  rw [coordinates_star, map_add]
  simp only [coordinates_tensor]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CliffordTwo.fromCoefficients, CliffordTwo.evenCoefficient, CliffordTwo.oddCoefficient,
      CliffordTwo.evenPart, CliffordTwo.oddPart, CliffordOne.grading, CliffordOne.swap,
      CliffordOne.epsilon, CStarMatrix.star_apply, smul_eq_mul] <;>
    ring_nf <;> simp_all

def epsilonOne : CliffordTwoGradedTensor := tensor CliffordOne.epsilon 1
def epsilonTwo : CliffordTwoGradedTensor := tensor 1 CliffordOne.epsilon

@[simp] theorem coordinates_epsilonOne : coordinates epsilonOne = CliffordTwo.epsilonOne :=
  CliffordTwo.tensorPauliCoordinates_epsilonOne
@[simp] theorem coordinates_epsilonTwo : coordinates epsilonTwo = CliffordTwo.epsilonTwo :=
  CliffordTwo.tensorPauliCoordinates_epsilonTwo

/-- The two tensor-factor odd generators anticommute in the actual algebra. -/
theorem epsilonTwo_mul_epsilonOne : epsilonTwo * epsilonOne = -(epsilonOne * epsilonTwo) := by
  apply coordinates.injective
  simp only [coordinates_mul, coordinates_epsilonOne, coordinates_epsilonTwo, map_neg]
  exact CliffordTwo.epsilonTwo_mul_epsilonOne

def grading : CStarGrading CliffordTwoGradedTensor where
  automorphism := coordinateStarAlgEquiv.trans
    (CliffordTwo.grading.automorphism.trans coordinateStarAlgEquiv.symm)
  involutive x := by
    apply coordinateStarAlgEquiv.injective
    simp [StarAlgEquiv.trans_apply]

@[simp] theorem coordinates_grading (x : CliffordTwoGradedTensor) :
    coordinates (grading.automorphism x) = CliffordTwo.grading.automorphism (coordinates x) := by
  change coordinates (coordinates.symm (CliffordTwo.grading.automorphism (coordinates x))) = _
  exact coordinates.apply_symm_apply _

/-- The grading is the actual tensor product of the two Cl₁ gradings. -/
theorem grading_tensor (z w : CliffordOne) :
    grading.automorphism (tensor z w) =
      tensor (CliffordOne.grading.automorphism z) (CliffordOne.grading.automorphism w) := by
  apply coordinates.injective
  rw [coordinates_grading]
  simp only [coordinates_tensor]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CliffordTwo.grading, CliffordTwo.parityConjugation, CliffordTwo.parity,
      CliffordTwo.fromCoefficients, CliffordTwo.evenCoefficient, CliffordTwo.oddCoefficient,
      CliffordOne.grading, CliffordOne.swap, CStarMatrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The maximal norm from actual matrix representations is the constructed
graded tensor norm, and the algebraic tensor is already complete for it. -/
theorem maximalNorm_eq (x : CliffordTwoGradedTensor) :
    CliffordTwo.maximalNorm (coordinates x) = ‖x‖ := by
  rw [CliffordTwo.maximalNorm_eq, norm_coordinates]

end CliffordTwoGradedTensor
end BC4lean.KKTheory
