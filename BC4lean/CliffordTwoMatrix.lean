import BC4lean.CliffordOne
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Star.Unitary

/-! # The actual complex two-generator Clifford C⋆ algebra

The carrier is the genuine C⋆ matrix algebra M₂(ℂ), with its operator norm.
The two generators are the selfadjoint Pauli matrices X and Y. They square
to one and anticommute. Its grading is conjugation by diag(1,-1).
The four words 1, X, Y, XY are an explicitly proved complex-linear basis.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped Matrix

abbrev CliffordTwo := CStarMatrix (Fin 2) (Fin 2) ℂ

namespace CliffordTwo

/-- Mathlib's actual operator-norm matrix C⋆ algebra. Its construction uses
the proved spectral star order on the complex coefficient algebra. -/
instance pauliCStarAlgebra : CStarAlgebra CliffordTwo := by
  letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  letI : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ
  exact CStarMatrix.instCStarAlgebra

def epsilonOne : CliffordTwo := CStarMatrix.ofMatrix !![0, 1; 1, 0]
def epsilonTwo : CliffordTwo := CStarMatrix.ofMatrix !![0, -Complex.I; Complex.I, 0]
def parity : CliffordTwo := CStarMatrix.ofMatrix !![1, 0; 0, -1]

@[simp] theorem epsilonOne_star : star epsilonOne = epsilonOne := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [epsilonOne, CStarMatrix.star_apply]

@[simp] theorem epsilonTwo_star : star epsilonTwo = epsilonTwo := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [epsilonTwo, CStarMatrix.star_apply]

@[simp] theorem parity_star : star parity = parity := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [parity, CStarMatrix.star_apply]

@[simp] theorem epsilonOne_square : epsilonOne * epsilonOne = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [epsilonOne, CStarMatrix.mul_apply, Fin.sum_univ_two, CStarMatrix.one_apply]

@[simp] theorem epsilonTwo_square : epsilonTwo * epsilonTwo = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [epsilonTwo, CStarMatrix.mul_apply, Fin.sum_univ_two, CStarMatrix.one_apply]

@[simp] theorem parity_square : parity * parity = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [parity, CStarMatrix.mul_apply, Fin.sum_univ_two, CStarMatrix.one_apply]

theorem epsilonOne_mem_unitary : epsilonOne ∈ unitary CliffordTwo := by
  rw [Unitary.mem_iff]
  simp
theorem epsilonTwo_mem_unitary : epsilonTwo ∈ unitary CliffordTwo := by
  rw [Unitary.mem_iff]
  simp
theorem parity_mem_unitary : parity ∈ unitary CliffordTwo := by
  rw [Unitary.mem_iff]
  simp

/-- The required Clifford relation, with the Koszul minus sign. -/
theorem epsilonTwo_mul_epsilonOne : epsilonTwo * epsilonOne = -(epsilonOne * epsilonTwo) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [epsilonOne, epsilonTwo, CStarMatrix.mul_apply, Fin.sum_univ_two]

def parityConjugation : CliffordTwo ≃⋆ₐ[ℂ] CliffordTwo where
  toFun M := parity * M * parity
  invFun M := parity * M * parity
  left_inv M := by
    calc
      parity * (parity * M * parity) * parity = (parity * parity) * M * (parity * parity) := by
        noncomm_ring
      _ = M := by simp
  right_inv M := by
    calc
      parity * (parity * M * parity) * parity = (parity * parity) * M * (parity * parity) := by
        noncomm_ring
      _ = M := by simp
  map_add' M N := by simp only [mul_add, add_mul]
  map_mul' M N := by
    calc
      parity * (M * N) * parity = parity * M * (parity * parity) * N * parity := by simp [mul_assoc]
      _ = (parity * M * parity) * (parity * N * parity) := by noncomm_ring
  map_star' M := by simp [star_mul, mul_assoc]
  map_smul' z M := by simp only [mul_smul_comm, smul_mul_assoc]

def grading : CStarGrading CliffordTwo where
  automorphism := parityConjugation
  involutive M := parityConjugation.symm_apply_apply M

@[simp] theorem epsilonOne_odd : grading.automorphism epsilonOne = -epsilonOne := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [grading, parityConjugation, parity, epsilonOne,
      CStarMatrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem epsilonTwo_odd : grading.automorphism epsilonTwo = -epsilonTwo := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [grading, parityConjugation, parity, epsilonTwo,
      CStarMatrix.mul_apply, Fin.sum_univ_two]

/-- The four Clifford words, in their required ordered generator convention. -/
def word {D : Type*} [CStarAlgebra D] (u v : D) (k : Fin 2 × Fin 2) : D :=
  (if k.1 = 0 then 1 else u) * (if k.2 = 0 then 1 else v)

def koszulSign (k l : Fin 2 × Fin 2) : ℂ := if k.2 = 1 ∧ l.1 = 1 then -1 else 1
def starSign (k : Fin 2 × Fin 2) : ℂ := if k.1 = 1 ∧ k.2 = 1 then -1 else 1
def wordIndexMul (k l : Fin 2 × Fin 2) : Fin 2 × Fin 2 := (k.1 + l.1, k.2 + l.2)

theorem word_mul {D : Type*} [CStarAlgebra D] (u v : D)
    (hu : u * u = 1) (hv : v * v = 1) (hanti : v * u = -(u * v))
    (k l : Fin 2 × Fin 2) :
    word u v k * word u v l = koszulSign k l • word u v (wordIndexMul k l) := by
  have huu_v : u * (u * v) = v := by rw [← mul_assoc, hu, one_mul]
  have huv_v : (u * v) * v = u := by rw [mul_assoc, hv, mul_one]
  have huv_u : (u * v) * u = -v := by
    rw [mul_assoc, hanti, mul_neg, ← mul_assoc, hu, one_mul]
  have hv_uv : v * (u * v) = -u := by
    rw [← mul_assoc, hanti, neg_mul, mul_assoc, hv, mul_one]
  have huv_uv : (u * v) * (u * v) = -1 := by rw [← mul_assoc, huv_u, neg_mul, hv]
  rcases k with ⟨i, j⟩
  rcases l with ⟨r, s⟩
  fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases s <;>
    simp [word, koszulSign, wordIndexMul, hu, hv, hanti, huu_v, huv_v, huv_u, hv_uv, huv_uv]

theorem word_star {D : Type*} [CStarAlgebra D] (u v : D)
    (hu : star u = u) (hv : star v = v) (hanti : v * u = -(u * v))
    (k : Fin 2 × Fin 2) : star (word u v k) = starSign k • word u v k := by
  rcases k with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [word, starSign, star_mul, hu, hv, hanti]

/-- Matrix coordinates in the four words 1, X, Y, XY. -/
def coefficient (M : CliffordTwo) (k : Fin 2 × Fin 2) : ℂ :=
  if k.1 = 0 then
    if k.2 = 0 then (M 0 0 + M 1 1) / 2 else (-Complex.I / 2) * (M 1 0 - M 0 1)
  else
    if k.2 = 0 then (M 0 1 + M 1 0) / 2 else (-Complex.I / 2) * (M 0 0 - M 1 1)

def coefficientLinear (k : Fin 2 × Fin 2) : CliffordTwo →ₗ[ℂ] ℂ where
  toFun M := coefficient M k
  map_add' M N := by
    rcases k with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [coefficient] <;> ring
  map_smul' z M := by
    rcases k with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [coefficient, smul_eq_mul] <;> ring

@[simp] theorem coefficientLinear_apply (k : Fin 2 × Fin 2) (M : CliffordTwo) :
    coefficientLinear k M = coefficient M k := rfl

@[simp] theorem coefficient_word (k l : Fin 2 × Fin 2) :
    coefficient (word epsilonOne epsilonTwo k) l = if l = k then 1 else 0 := by
  rcases k with ⟨i, j⟩
  rcases l with ⟨r, s⟩
  fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases s <;>
    norm_num [coefficient, word, epsilonOne, epsilonTwo, CStarMatrix.mul_apply,
      CStarMatrix.one_apply, Fin.sum_univ_two]
  all_goals
    calc
      -Complex.I / 2 * (Complex.I + Complex.I) = -(Complex.I * Complex.I) := by ring
      _ = 1 := by simp only [Complex.I_mul_I, neg_neg]

/-- Every actual operator-norm matrix has the explicit four-word expansion. -/
theorem decompose (M : CliffordTwo) :
    M = ∑ k : Fin 2 × Fin 2, coefficient M k • word epsilonOne epsilonTwo k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, coefficient, word, epsilonOne, epsilonTwo,
      CStarMatrix.mul_apply, smul_eq_mul] <;>
    ring_nf <;> simp only [Complex.I_sq] <;> ring

end CliffordTwo
end BC4lean.KKTheory
