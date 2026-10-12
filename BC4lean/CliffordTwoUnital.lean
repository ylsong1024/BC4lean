import BC4lean.CliffordTwoGradedTensor

/-! # The unit and universal law of the genuine graded Clifford tensor

The transported multiplication has the actual tensor 1 ⊗ 1 as its identity.
This file supplies the full unital C⋆ algebra structure and transports the
proved two-generator universal law to the genuine Koszul tensor.
-/

noncomputable section
namespace BC4lean.KKTheory
namespace CliffordTwoGradedTensor

instance one : One CliffordTwoGradedTensor := ⟨coordinates.symm 1⟩
instance natCast : NatCast CliffordTwoGradedTensor := ⟨fun n => coordinates.symm n⟩
instance intCast : IntCast CliffordTwoGradedTensor := ⟨fun n => coordinates.symm n⟩
instance pow : Pow CliffordTwoGradedTensor ℕ :=
  ⟨fun x n => coordinates.symm (coordinates x ^ n)⟩

@[simp] theorem coordinates_one : coordinates (1 : CliffordTwoGradedTensor) = 1 :=
  coordinates.apply_symm_apply _
@[simp] theorem coordinates_natCast (n : ℕ) : coordinates (n : CliffordTwoGradedTensor) = n :=
  coordinates.apply_symm_apply _
@[simp] theorem coordinates_intCast (n : ℤ) : coordinates (n : CliffordTwoGradedTensor) = n :=
  coordinates.apply_symm_apply _
@[simp] theorem coordinates_pow (x : CliffordTwoGradedTensor) (n : ℕ) :
    coordinates (x ^ n) = coordinates x ^ n := coordinates.apply_symm_apply _

instance ring : Ring CliffordTwoGradedTensor :=
  coordinates.injective.ring coordinates (map_zero _) coordinates_one (map_add _)
    coordinates_mul (map_neg _) (map_sub _) (fun n x => map_nsmul _ n x)
    (fun n x => map_zsmul _ n x) coordinates_pow coordinates_natCast coordinates_intCast

instance normedRing : NormedRing CliffordTwoGradedTensor where
  toRing := ring
  toMetricSpace := inferInstance
  norm := (‖·‖)
  dist_eq x y := dist_eq_norm_neg_add x y
  norm_mul_le x y := by
    change ‖coordinates (x * y)‖ ≤ ‖coordinates x‖ * ‖coordinates y‖
    rw [coordinates_mul]
    exact norm_mul_le _ _

def scalarHom : ℂ →+* CliffordTwoGradedTensor where
  toFun z := coordinates.symm (algebraMap ℂ CliffordTwo z)
  map_zero' := by apply coordinates.injective; simp
  map_one' := by apply coordinates.injective; simp
  map_add' z w := by apply coordinates.injective; simp
  map_mul' z w := by apply coordinates.injective; simp

instance algebra : Algebra ℂ CliffordTwoGradedTensor where
  algebraMap := scalarHom
  smul := (· • ·)
  commutes' z x := by
    apply coordinates.injective
    change coordinates (coordinates.symm (algebraMap ℂ CliffordTwo z) * x) =
      coordinates (x * coordinates.symm (algebraMap ℂ CliffordTwo z))
    rw [coordinates_mul, coordinates_mul, coordinates.apply_symm_apply]
    exact Algebra.commutes z (coordinates x)
  smul_def' z x := by
    apply coordinates.injective
    change coordinates (z • x) =
      coordinates (coordinates.symm (algebraMap ℂ CliffordTwo z) * x)
    rw [map_smul, coordinates_mul, coordinates.apply_symm_apply]
    exact Algebra.smul_def z (coordinates x)

instance normedAlgebra : NormedAlgebra ℂ CliffordTwoGradedTensor where
  norm_smul_le := norm_smul_le

instance cstarAlgebra : CStarAlgebra CliffordTwoGradedTensor where

@[simp] theorem tensor_one_one : tensor 1 1 = (1 : CliffordTwoGradedTensor) := by
  apply coordinates.injective
  exact CliffordTwo.tensorPauliCoordinates_one.trans coordinates_one.symm

@[simp] theorem epsilonOne_star : star epsilonOne = epsilonOne := by
  apply coordinates.injective
  simp
@[simp] theorem epsilonTwo_star : star epsilonTwo = epsilonTwo := by
  apply coordinates.injective
  simp
@[simp] theorem epsilonOne_square : epsilonOne * epsilonOne = 1 := by
  apply coordinates.injective
  simp
@[simp] theorem epsilonTwo_square : epsilonTwo * epsilonTwo = 1 := by
  apply coordinates.injective
  simp

@[simp] theorem coordinateStarAlgEquiv_symm_epsilonOne :
    coordinateStarAlgEquiv.symm CliffordTwo.epsilonOne = epsilonOne := by
  change coordinates.symm CliffordTwo.epsilonOne = epsilonOne
  apply coordinates.injective
  rw [coordinates.apply_symm_apply]
  exact coordinates_epsilonOne.symm
@[simp] theorem coordinateStarAlgEquiv_symm_epsilonTwo :
    coordinateStarAlgEquiv.symm CliffordTwo.epsilonTwo = epsilonTwo := by
  change coordinates.symm CliffordTwo.epsilonTwo = epsilonTwo
  apply coordinates.injective
  rw [coordinates.apply_symm_apply]
  exact coordinates_epsilonTwo.symm

@[simp] theorem epsilonOne_odd : grading.automorphism epsilonOne = -epsilonOne := by
  apply coordinates.injective
  simp
@[simp] theorem epsilonTwo_odd : grading.automorphism epsilonTwo = -epsilonTwo := by
  apply coordinates.injective
  simp

variable {D : Type*} [CStarAlgebra D]

def lift (u v : D) (hu : star u = u) (hv : star v = v)
    (hu₂ : u * u = 1) (hv₂ : v * v = 1) (hanti : v * u = -(u * v)) :
    CliffordTwoGradedTensor →⋆ₐ[ℂ] D :=
  (CliffordTwo.lift u v hu hv hu₂ hv₂ hanti).comp coordinateStarAlgEquiv.toStarAlgHom

@[simp] theorem lift_epsilonOne (u v : D) (hu : star u = u) (hv : star v = v)
    (hu₂ : u * u = 1) (hv₂ : v * v = 1) (hanti : v * u = -(u * v)) :
    lift u v hu hv hu₂ hv₂ hanti epsilonOne = u := by
  change (CliffordTwo.lift u v hu hv hu₂ hv₂ hanti) (coordinates epsilonOne) = _
  rw [coordinates_epsilonOne]
  exact CliffordTwo.lift_epsilonOne u v hu hv hu₂ hv₂ hanti
@[simp] theorem lift_epsilonTwo (u v : D) (hu : star u = u) (hv : star v = v)
    (hu₂ : u * u = 1) (hv₂ : v * v = 1) (hanti : v * u = -(u * v)) :
    lift u v hu hv hu₂ hv₂ hanti epsilonTwo = v := by
  change (CliffordTwo.lift u v hu hv hu₂ hv₂ hanti) (coordinates epsilonTwo) = _
  rw [coordinates_epsilonTwo]
  exact CliffordTwo.lift_epsilonTwo u v hu hv hu₂ hv₂ hanti

theorem lift_unique (u v : D) (hu : star u = u) (hv : star v = v)
    (hu₂ : u * u = 1) (hv₂ : v * v = 1) (hanti : v * u = -(u * v))
    (φ : CliffordTwoGradedTensor →⋆ₐ[ℂ] D)
    (hφu : φ epsilonOne = u) (hφv : φ epsilonTwo = v) :
    φ = lift u v hu hv hu₂ hv₂ hanti := by
  have h := CliffordTwo.lift_unique u v hu hv hu₂ hv₂ hanti
    (φ.comp coordinateStarAlgEquiv.symm.toStarAlgHom)
    (by
      change φ (coordinateStarAlgEquiv.symm CliffordTwo.epsilonOne) = u
      rw [coordinateStarAlgEquiv_symm_epsilonOne]
      exact hφu)
    (by
      change φ (coordinateStarAlgEquiv.symm CliffordTwo.epsilonTwo) = v
      rw [coordinateStarAlgEquiv_symm_epsilonTwo]
      exact hφv)
  ext x
  have hx := DFunLike.congr_fun h (coordinates x)
  change φ (coordinates.symm (coordinates x)) =
    (CliffordTwo.lift u v hu hv hu₂ hv₂ hanti) (coordinates x) at hx
  rw [coordinates.symm_apply_apply] at hx
  change φ x = (CliffordTwo.lift u v hu hv hu₂ hv₂ hanti) (coordinates x)
  exact hx

/-- The actual Clifford-generator inclusions of the two graded factors. -/
def firstFactor : CliffordOne →⋆ₐ[ℂ] CliffordTwoGradedTensor :=
  CliffordOne.lift epsilonOne epsilonOne_star epsilonOne_square
def secondFactor : CliffordOne →⋆ₐ[ℂ] CliffordTwoGradedTensor :=
  CliffordOne.lift epsilonTwo epsilonTwo_star epsilonTwo_square

theorem firstFactor_eq_tensor (z : CliffordOne) : firstFactor z = tensor z 1 := by
  apply coordinates.injective
  change coordinates (z.1 • CliffordOne.plusProjection epsilonOne +
    z.2 • CliffordOne.minusProjection epsilonOne) = coordinates (tensor z 1)
  simp only [CliffordOne.plusProjection, CliffordOne.minusProjection, map_add, map_sub,
    map_smul, coordinates_one, coordinates_epsilonOne, coordinates_tensor]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CliffordTwo.fromCoefficients, CliffordTwo.evenCoefficient, CliffordTwo.oddCoefficient,
      CliffordTwo.epsilonOne, smul_eq_mul] <;> ring

theorem secondFactor_eq_tensor (z : CliffordOne) : secondFactor z = tensor 1 z := by
  apply coordinates.injective
  change coordinates (z.1 • CliffordOne.plusProjection epsilonTwo +
    z.2 • CliffordOne.minusProjection epsilonTwo) = coordinates (tensor 1 z)
  simp only [CliffordOne.plusProjection, CliffordOne.minusProjection, map_add, map_sub,
    map_smul, coordinates_one, coordinates_epsilonTwo, coordinates_tensor]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CliffordTwo.fromCoefficients, CliffordTwo.evenCoefficient, CliffordTwo.oddCoefficient,
      CliffordTwo.epsilonTwo, smul_eq_mul] <;> ring

theorem firstFactor_graded (z : CliffordOne) : grading.automorphism (firstFactor z) =
    firstFactor (CliffordOne.grading.automorphism z) := by
  rw [firstFactor_eq_tensor, grading_tensor, firstFactor_eq_tensor]
  simp
theorem secondFactor_graded (z : CliffordOne) : grading.automorphism (secondFactor z) =
    secondFactor (CliffordOne.grading.automorphism z) := by
  rw [secondFactor_eq_tensor, grading_tensor, secondFactor_eq_tensor]
  simp

end CliffordTwoGradedTensor
end BC4lean.KKTheory
