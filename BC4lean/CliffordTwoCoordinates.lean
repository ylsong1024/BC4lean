import BC4lean.CliffordTwoUniversal
import BC4lean.CliffordAlgebraTensor

/-! # Explicit linear coordinates for the genuine graded Clifford tensor

Cl₁ has the proved linear coordinates z=a+bε. Tensor distributivity gives
four actual complex coordinates. The Pauli map sends them to aI+bX+cY+dXY.
Its inverse is calculated from the four matrix entries. This is a linear
equivalence; multiplication and star are supplied separately by the Koszul
construction, so the ordinary ungraded tensor algebra is not used.
-/

noncomputable section
namespace BC4lean.KKTheory
namespace CliffordTwo
open scoped TensorProduct Matrix

def evenCoefficient (z : CliffordOne) : ℂ := (z.1 + z.2) / 2
def oddCoefficient (z : CliffordOne) : ℂ := (z.1 - z.2) / 2

/-- Actual even/odd coordinates, with inverse (a,b) ↦ (a+b,a-b). -/
def oneEvenOddCoordinates : CliffordOne ≃ₗ[ℂ] CliffordOne where
  toFun z := (evenCoefficient z, oddCoefficient z)
  invFun z := (z.1 + z.2, z.1 - z.2)
  left_inv z := by apply Prod.ext <;> simp [evenCoefficient, oddCoefficient] <;> ring
  right_inv z := by apply Prod.ext <;> simp [evenCoefficient, oddCoefficient]
  map_add' z w := by apply Prod.ext <;> simp [evenCoefficient, oddCoefficient] <;> ring
  map_smul' r z := by
    apply Prod.ext <;> simp [evenCoefficient, oddCoefficient, smul_eq_mul] <;> ring

theorem one_decompose (z : CliffordOne) :
    z = evenCoefficient z • (1 : CliffordOne) + oddCoefficient z • CliffordOne.epsilon := by
  apply Prod.ext <;> simp [evenCoefficient, oddCoefficient, CliffordOne.epsilon, smul_eq_mul] <;> ring

def evenPart (z : CliffordOne) : CliffordOne := evenCoefficient z • (1 : CliffordOne)
def oddPart (z : CliffordOne) : CliffordOne := oddCoefficient z • CliffordOne.epsilon

theorem evenPart_add_oddPart (z : CliffordOne) : evenPart z + oddPart z = z :=
  (one_decompose z).symm

/-- The matrix belonging to the four ordered Clifford-word coordinates. -/
def fromCoefficients (p : CliffordOne × CliffordOne) : CliffordTwo :=
  CStarMatrix.ofMatrix
    !![p.1.1 + Complex.I * p.2.2, p.1.2 - Complex.I * p.2.1;
       p.1.2 + Complex.I * p.2.1, p.1.1 - Complex.I * p.2.2]

def matrixCoefficients (M : CliffordTwo) : CliffordOne × CliffordOne :=
  ((coefficient M (0, 0), coefficient M (1, 0)),
    (coefficient M (0, 1), coefficient M (1, 1)))

/-- This bijection is proved by actual entries and their four-word coordinates. -/
def pauliCoordinateEquiv : (CliffordOne × CliffordOne) ≃ₗ[ℂ] CliffordTwo where
  toFun := fromCoefficients
  invFun := matrixCoefficients
  left_inv p := by
    apply Prod.ext <;> apply Prod.ext <;>
      simp [fromCoefficients, matrixCoefficients, coefficient] <;>
      ring_nf <;> simp only [Complex.I_sq] <;> ring
  right_inv M := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [fromCoefficients, matrixCoefficients, coefficient] <;>
      ring_nf <;> simp only [Complex.I_sq] <;> ring
  map_add' p q := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [fromCoefficients] <;> ring
  map_smul' r p := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [fromCoefficients, smul_eq_mul] <;> ring

/-- The actual complex tensor vector space has the proved Pauli coordinates. -/
def tensorPauliCoordinates : (CliffordOne ⊗[ℂ] CliffordOne) ≃ₗ[ℂ] CliffordTwo :=
  (TensorProduct.congr oneEvenOddCoordinates oneEvenOddCoordinates).trans
    ((cliffordTensorCoordinates (B := CliffordOne)).trans pauliCoordinateEquiv)

theorem tensorPauliCoordinates_tmul (z w : CliffordOne) :
    tensorPauliCoordinates (z ⊗ₜ[ℂ] w) =
      fromCoefficients
        ((evenCoefficient z * evenCoefficient w, oddCoefficient z * evenCoefficient w),
          (evenCoefficient z * oddCoefficient w, oddCoefficient z * oddCoefficient w)) := by
  simp [tensorPauliCoordinates, TensorProduct.congr_tmul, cliffordTensorCoordinates_tmul,
    oneEvenOddCoordinates, pauliCoordinateEquiv, smul_eq_mul, mul_comm]

@[simp] theorem tensorPauliCoordinates_one :
    tensorPauliCoordinates ((1 : CliffordOne) ⊗ₜ[ℂ] (1 : CliffordOne)) = 1 := by
  rw [tensorPauliCoordinates_tmul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fromCoefficients, evenCoefficient, oddCoefficient, CStarMatrix.one_apply]

@[simp] theorem tensorPauliCoordinates_epsilonOne :
    tensorPauliCoordinates (CliffordOne.epsilon ⊗ₜ[ℂ] (1 : CliffordOne)) = epsilonOne := by
  rw [tensorPauliCoordinates_tmul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fromCoefficients, evenCoefficient, oddCoefficient, CliffordOne.epsilon, epsilonOne]

@[simp] theorem tensorPauliCoordinates_epsilonTwo :
    tensorPauliCoordinates ((1 : CliffordOne) ⊗ₜ[ℂ] CliffordOne.epsilon) = epsilonTwo := by
  rw [tensorPauliCoordinates_tmul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fromCoefficients, evenCoefficient, oddCoefficient, CliffordOne.epsilon, epsilonTwo]

end CliffordTwo
end BC4lean.KKTheory
