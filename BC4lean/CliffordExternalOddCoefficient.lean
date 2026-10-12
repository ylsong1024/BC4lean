import BC4lean.CliffordTwoCoordinates
import BC4lean.CliffordTwoCoefficientTensor
import Mathlib.Tactic.Module

/-! # Genuine coefficient coordinates for the second Clifford extension

The actual complex tensor (C⊗Cl₁)⊗Cl₁ maps bijectively through the genuine
tensor associator and Pauli coordinates to M₂(C). The pure product formula
below includes the Koszul sign. C remains possibly nonunital throughout.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordExternalOddCoefficient
open scoped TensorProduct

variable {C : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

abbrev Tensor := (C × C) ⊗[ℂ] CliffordOne

def coordinates : Tensor (C := C) ≃ₗ[ℂ] GradedMatrixMoritaMatrix C :=
  (TensorProduct.congr (cliffordTensorCoordinates (B := C)).symm
    (LinearEquiv.refl ℂ CliffordOne)).trans
    ((TensorProduct.assoc ℂ C CliffordOne CliffordOne).trans
      ((TensorProduct.congr (LinearEquiv.refl ℂ C) CliffordTwo.tensorPauliCoordinates).trans
        CliffordTwoCoefficientTensor.algebraicCoordinates))

def evenCoefficient (a : C × C) : C := (2 : ℂ)⁻¹ • (a.1 + a.2)
def oddCoefficient (a : C × C) : C := (2 : ℂ)⁻¹ • (a.1 - a.2)

/-- The actual Pauli coefficient matrix of an elementary external tensor. -/
def pureMatrix (a : C × C) (z : CliffordOne) : GradedMatrixMoritaMatrix C :=
  CStarMatrix.ofMatrix !![
    CliffordTwo.evenCoefficient z • evenCoefficient a +
      (Complex.I * CliffordTwo.oddCoefficient z) • oddCoefficient a,
    CliffordTwo.evenCoefficient z • oddCoefficient a +
      (-Complex.I * CliffordTwo.oddCoefficient z) • evenCoefficient a;
    CliffordTwo.evenCoefficient z • oddCoefficient a +
      (Complex.I * CliffordTwo.oddCoefficient z) • evenCoefficient a,
    CliffordTwo.evenCoefficient z • evenCoefficient a +
      (-Complex.I * CliffordTwo.oddCoefficient z) • oddCoefficient a]

@[simp] theorem coordinates_tmul (a : C × C) (z : CliffordOne) :
    coordinates (a ⊗ₜ[ℂ] z) = pureMatrix a z := by
  let _retainedOriginalPartialOrderC : PartialOrder C := inferInstance
  let _retainedOriginalStarOrderedRingC : StarOrderedRing C := inferInstance
  have hdecompose : cliffordTensorCoordinates.symm a =
      evenCoefficient a ⊗ₜ[ℂ] (1 : CliffordOne) +
        oddCoefficient a ⊗ₜ[ℂ] CliffordOne.epsilon := by
    apply cliffordTensorCoordinates.injective
    simp only [LinearEquiv.apply_symm_apply, map_add, cliffordTensorCoordinates_tmul]
    apply Prod.ext <;>
      simp [evenCoefficient, oddCoefficient, CliffordOne.epsilon] <;> module
  have hEvenOne : CliffordTwo.evenCoefficient (1 : CliffordOne) = 1 := by
    norm_num [CliffordTwo.evenCoefficient]
  have hOddOne : CliffordTwo.oddCoefficient (1 : CliffordOne) = 0 := by
    norm_num [CliffordTwo.oddCoefficient]
  have hEvenEpsilon : CliffordTwo.evenCoefficient CliffordOne.epsilon = 0 := by
    norm_num [CliffordTwo.evenCoefficient, CliffordOne.epsilon]
  have hOddEpsilon : CliffordTwo.oddCoefficient CliffordOne.epsilon = 1 := by
    norm_num [CliffordTwo.oddCoefficient, CliffordOne.epsilon]
  have hOne : CliffordTwo.tensorPauliCoordinates ((1 : CliffordOne) ⊗ₜ[ℂ] z) =
      CStarMatrix.ofMatrix !![
        CliffordTwo.evenCoefficient z, -Complex.I * CliffordTwo.oddCoefficient z;
        Complex.I * CliffordTwo.oddCoefficient z, CliffordTwo.evenCoefficient z] := by
    rw [CliffordTwo.tensorPauliCoordinates_tmul, hEvenOne, hOddOne]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CliffordTwo.fromCoefficients]
  have hEpsilon : CliffordTwo.tensorPauliCoordinates (CliffordOne.epsilon ⊗ₜ[ℂ] z) =
      CStarMatrix.ofMatrix !![
        Complex.I * CliffordTwo.oddCoefficient z, CliffordTwo.evenCoefficient z;
        CliffordTwo.evenCoefficient z, -Complex.I * CliffordTwo.oddCoefficient z] := by
    rw [CliffordTwo.tensorPauliCoordinates_tmul, hEvenEpsilon, hOddEpsilon]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CliffordTwo.fromCoefficients]
  simp only [coordinates, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    hdecompose, TensorProduct.add_tmul, map_add,
    TensorProduct.assoc_tmul, LinearEquiv.refl_apply, hOne, hEpsilon,
    CliffordTwoCoefficientTensor.algebraicCoordinates_tmul]
  ext i j
  fin_cases i <;> fin_cases j
  · change CliffordTwo.evenCoefficient z • evenCoefficient a +
        (Complex.I * CliffordTwo.oddCoefficient z) • oddCoefficient a =
      CliffordTwo.evenCoefficient z • evenCoefficient a +
        (Complex.I * CliffordTwo.oddCoefficient z) • oddCoefficient a
    rfl
  · change (-Complex.I * CliffordTwo.oddCoefficient z) • evenCoefficient a +
        CliffordTwo.evenCoefficient z • oddCoefficient a =
      CliffordTwo.evenCoefficient z • oddCoefficient a +
        (-Complex.I * CliffordTwo.oddCoefficient z) • evenCoefficient a
    exact add_comm _ _
  · change (Complex.I * CliffordTwo.oddCoefficient z) • evenCoefficient a +
        CliffordTwo.evenCoefficient z • oddCoefficient a =
      CliffordTwo.evenCoefficient z • oddCoefficient a +
        (Complex.I * CliffordTwo.oddCoefficient z) • evenCoefficient a
    exact add_comm _ _
  · change CliffordTwo.evenCoefficient z • evenCoefficient a +
        (-Complex.I * CliffordTwo.oddCoefficient z) • oddCoefficient a =
      CliffordTwo.evenCoefficient z • evenCoefficient a +
        (-Complex.I * CliffordTwo.oddCoefficient z) • oddCoefficient a
    rfl

/-- The Koszul product is supplied by the genuine Pauli matrix product. -/
def mul (x y : Tensor (C := C)) : Tensor (C := C) :=
  coordinates.symm (coordinates x * coordinates y)

omit [PartialOrder C] [StarOrderedRing C] in
@[simp] theorem coordinates_mul [PartialOrder C] [StarOrderedRing C]
    (x y : Tensor (C := C)) :
    coordinates (mul x y) = coordinates x * coordinates y :=
  coordinates.apply_symm_apply _

/-- Full elementary tensor multiplication, including the odd crossing sign. -/
theorem mul_tmul (a b : C × C) (z w : CliffordOne) :
    mul (a ⊗ₜ[ℂ] z) (b ⊗ₜ[ℂ] w) =
      (a * b) ⊗ₜ[ℂ] (CliffordTwo.evenPart z * w) +
        (a * (b.2, b.1)) ⊗ₜ[ℂ] (CliffordTwo.oddPart z * w) := by
  apply coordinates.injective
  simp only [coordinates_mul, map_add, coordinates_tmul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pureMatrix, evenCoefficient, oddCoefficient,
      CliffordTwo.evenCoefficient, CliffordTwo.oddCoefficient,
      CliffordTwo.evenPart, CliffordTwo.oddPart, CliffordOne.epsilon,
      CStarMatrix.mul_apply, Fin.sum_univ_two,
      smul_mul_assoc, mul_smul_comm, smul_smul,
      add_mul, mul_add, sub_mul, mul_sub] <;>
    match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

def starTensor (x : Tensor (C := C)) : Tensor (C := C) :=
  coordinates.symm (star (coordinates x))

omit [PartialOrder C] [StarOrderedRing C] in
@[simp] theorem coordinates_starTensor [PartialOrder C] [StarOrderedRing C]
    (x : Tensor (C := C)) :
    coordinates (starTensor x) = star (coordinates x) :=
  coordinates.apply_symm_apply _

/-- The tensor star carries the same required odd crossing sign. -/
theorem starTensor_tmul (a : C × C) (z : CliffordOne) :
    starTensor (a ⊗ₜ[ℂ] z) =
      star a ⊗ₜ[ℂ] CliffordTwo.evenPart (star z) +
        (star a.2, star a.1) ⊗ₜ[ℂ] CliffordTwo.oddPart (star z) := by
  apply coordinates.injective
  simp only [coordinates_starTensor, map_add, coordinates_tmul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pureMatrix, evenCoefficient, oddCoefficient,
      CliffordTwo.evenCoefficient, CliffordTwo.oddCoefficient,
      CliffordTwo.evenPart, CliffordTwo.oddPart, CliffordOne.epsilon,
      CStarMatrix.star_apply, star_smul, Complex.conj_I] <;>
    match_scalars <;> ring_nf

omit [PartialOrder C] [StarOrderedRing C] in
/-- The genuine external grading is the actual matrix grading. -/
theorem grading_tmul [PartialOrder C] [StarOrderedRing C]
    (a : C × C) (z : CliffordOne) :
    GradedMatrixMoritaMatrix.parity (pureMatrix a z) =
      pureMatrix (a.2, a.1) (CliffordOne.grading.automorphism z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pureMatrix, GradedMatrixMoritaMatrix.parity,
      evenCoefficient, oddCoefficient, CliffordTwo.evenCoefficient,
      CliffordTwo.oddCoefficient, CliffordOne.grading, CliffordOne.swap] <;> module

end BC4lean.KKTheory.CliffordExternalOddCoefficient
