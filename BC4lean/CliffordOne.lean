import BC4lean.GradedHilbertModule
import Mathlib.Tactic.Module

/-! # The complex C⋆-algebra Cl₁ in its product model

The underlying C⋆-algebra is ℂ × ℂ, with coordinatewise complex conjugation
and its ordinary C⋆ product norm. Its odd selfadjoint unitary generator is
`epsilon = (1,-1)` and its grading swaps the coordinates. We prove the actual
universal star-algebra property for a selfadjoint unitary, using the two
orthogonal projections `(1+u)/2` and `(1-u)/2`.

Mathlib's `CliffordAlgebra.Star` instead supplies algebraic Clifford
conjugation: it fixes scalars and negates vector generators. That operation
is different from the complex C⋆ star used here, and we do not reuse it.
The operator-cycle parity equivalence is a further construction; this file
does not assume or assert it.
-/

noncomputable section
namespace BC4lean.KKTheory

/-- The one-generator complex Clifford C⋆-algebra in its product model. -/
abbrev CliffordOne := ℂ × ℂ

namespace CliffordOne

/-- Coordinate swap is an actual complex star-algebra automorphism. -/
def swap : CliffordOne ≃⋆ₐ[ℂ] CliffordOne where
  toFun := Prod.swap
  invFun := Prod.swap
  left_inv := Prod.swap_swap
  right_inv := Prod.swap_swap
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem swap_apply (z : CliffordOne) : swap z = (z.2, z.1) := rfl

/-- The Z/2 grading is coordinate swap. -/
def grading : CStarGrading CliffordOne where
  automorphism := swap
  involutive := Prod.swap_swap

/-- The selfadjoint unitary generator of Cl₁. -/
def epsilon : CliffordOne := (1, -1)

@[simp] theorem epsilon_star : star epsilon = epsilon := by
  ext <;> simp [epsilon]

@[simp] theorem epsilon_square : epsilon * epsilon = 1 := by
  ext <;> simp [epsilon]

@[simp] theorem epsilon_odd : grading.automorphism epsilon = -epsilon := by
  ext <;> simp [grading, swap, epsilon]

variable {D : Type*} [CStarAlgebra D]

/-- The +1 spectral projection of a selfadjoint unitary. -/
def plusProjection (u : D) : D := (2 : ℂ)⁻¹ • (1 + u)

/-- The -1 spectral projection of a selfadjoint unitary. -/
def minusProjection (u : D) : D := (2 : ℂ)⁻¹ • (1 - u)

theorem plus_add_minus (u : D) : plusProjection u + minusProjection u = 1 := by
  unfold plusProjection minusProjection
  module

theorem plus_sub_minus (u : D) : plusProjection u - minusProjection u = u := by
  unfold plusProjection minusProjection
  module

theorem plusProjection_star (u : D) (hu : star u = u) :
    star (plusProjection u) = plusProjection u := by
  simp [plusProjection, hu]

theorem minusProjection_star (u : D) (hu : star u = u) :
    star (minusProjection u) = minusProjection u := by
  simp [minusProjection, hu]

theorem plusProjection_square (u : D) (hsq : u * u = 1) :
    plusProjection u * plusProjection u = plusProjection u := by
  unfold plusProjection
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [add_mul, mul_add, mul_add]
  simp only [one_mul, mul_one, hsq]
  module

theorem minusProjection_square (u : D) (hsq : u * u = 1) :
    minusProjection u * minusProjection u = minusProjection u := by
  unfold minusProjection
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [sub_mul, mul_sub, mul_sub]
  simp only [one_mul, mul_one, hsq]
  module

theorem plus_mul_minus (u : D) (hsq : u * u = 1) :
    plusProjection u * minusProjection u = 0 := by
  unfold plusProjection minusProjection
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [add_mul, mul_sub, mul_sub]
  simp only [one_mul, mul_one, hsq]
  module

theorem minus_mul_plus (u : D) (hsq : u * u = 1) :
    minusProjection u * plusProjection u = 0 := by
  unfold plusProjection minusProjection
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [sub_mul, mul_add, mul_add]
  simp only [one_mul, mul_one, hsq]
  module

/-- The genuine universal unital complex star homomorphism sending the odd
Clifford generator to a specified selfadjoint unitary. -/
def lift (u : D) (hu : star u = u) (hsq : u * u = 1) : CliffordOne →⋆ₐ[ℂ] D where
  toFun z := z.1 • plusProjection u + z.2 • minusProjection u
  map_zero' := by simp
  map_add' z w := by
    change (z.1 + w.1) • plusProjection u + (z.2 + w.2) • minusProjection u = _
    module
  map_one' := by
    change 1 • plusProjection u + 1 • minusProjection u = 1
    simpa only [one_smul] using plus_add_minus u
  map_mul' z w := by
    change (z.1 * w.1) • plusProjection u + (z.2 * w.2) • minusProjection u =
      (z.1 • plusProjection u + z.2 • minusProjection u) *
        (w.1 • plusProjection u + w.2 • minusProjection u)
    rw [add_mul, mul_add, mul_add]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul,
      plusProjection_square u hsq, minusProjection_square u hsq,
      plus_mul_minus u hsq, minus_mul_plus u hsq, smul_zero, add_zero, zero_add, mul_comm]
  commutes' r := by
    change r • plusProjection u + r • minusProjection u = algebraMap ℂ D r
    rw [← smul_add, plus_add_minus, Algebra.algebraMap_eq_smul_one]
  map_star' z := by
    change star z.1 • plusProjection u + star z.2 • minusProjection u =
      star (z.1 • plusProjection u + z.2 • minusProjection u)
    rw [star_add, star_smul, star_smul, plusProjection_star u hu, minusProjection_star u hu]

@[simp] theorem lift_apply (u : D) (hu : star u = u) (hsq : u * u = 1)
    (z : CliffordOne) :
    lift u hu hsq z = z.1 • plusProjection u + z.2 • minusProjection u := rfl

@[simp] theorem lift_epsilon (u : D) (hu : star u = u) (hsq : u * u = 1) :
    lift u hu hsq epsilon = u := by
  rw [lift_apply]
  change 1 • plusProjection u + (-1 : ℂ) • minusProjection u = u
  simpa only [one_smul, neg_one_smul, ← sub_eq_add_neg] using plus_sub_minus u

@[simp] theorem plusProjection_epsilon : plusProjection epsilon = (1, 0) := by
  ext <;> norm_num [plusProjection, epsilon, smul_eq_mul]

@[simp] theorem minusProjection_epsilon : minusProjection epsilon = (0, 1) := by
  ext <;> norm_num [minusProjection, epsilon, smul_eq_mul]

/-- Every element is generated by 1 and the odd unitary; equivalently by
its two actual spectral projections. -/
theorem decompose (z : CliffordOne) :
    z = z.1 • plusProjection epsilon + z.2 • minusProjection epsilon := by
  rw [plusProjection_epsilon, minusProjection_epsilon]
  ext <;> simp [smul_eq_mul]

theorem map_plusProjection (φ : CliffordOne →⋆ₐ[ℂ] D) :
    φ (plusProjection epsilon) = plusProjection (φ epsilon) := by
  simp [plusProjection]

theorem map_minusProjection (φ : CliffordOne →⋆ₐ[ℂ] D) :
    φ (minusProjection epsilon) = minusProjection (φ epsilon) := by
  simp [minusProjection]

/-- The lift is determined by its value on the Clifford generator. -/
theorem lift_unique (u : D) (hu : star u = u) (hsq : u * u = 1)
    (φ : CliffordOne →⋆ₐ[ℂ] D) (hφ : φ epsilon = u) : φ = lift u hu hsq := by
  ext z
  calc
    φ z = φ (z.1 • plusProjection epsilon + z.2 • minusProjection epsilon) :=
      congrArg φ (decompose z)
    _ = z.1 • plusProjection u + z.2 • minusProjection u := by
      rw [map_add, map_smul, map_smul, map_plusProjection, map_minusProjection, hφ]
    _ = lift u hu hsq z := rfl

/-- The one-generator universal C⋆ star-algebra property holds concretely. -/
theorem existsUnique_lift (u : D) (hu : star u = u) (hsq : u * u = 1) :
    ∃! φ : CliffordOne →⋆ₐ[ℂ] D, φ epsilon = u :=
  ⟨lift u hu hsq, lift_epsilon u hu hsq,
    fun φ hφ => lift_unique u hu hsq φ hφ⟩

end CliffordOne
end BC4lean.KKTheory
