import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Analysis.Complex.Basic

/-!
# The complex group algebra of an arbitrary group

This file verifies the algebraic starting point for the reduced group C*-algebra.
Multiplication is Mathlib's convolution product, not pointwise multiplication.
The involution conjugates coefficients and reverses group elements.
No topology, countability, regular representation, or completion is assumed here.
-/

noncomputable section

namespace BC4lean

/-- Finitely supported complex coefficients with convolution multiplication. -/
abbrev GroupAlgebra (Γ : Type*) := MonoidAlgebra ℂ Γ

namespace GroupAlgebra

variable {Γ : Type*} [Group Γ]

/-- The basis vector at a group element. -/
def delta (g : Γ) : GroupAlgebra Γ := MonoidAlgebra.single g 1

/-- The finite coefficient ℓ¹-norm; no normed-algebra instance is claimed. -/
def l1Norm (a : GroupAlgebra Γ) : ℝ := ∑ g ∈ a.coeff.support, ‖a.coeff g‖

/-- Conjugation of coefficients followed by inversion of the group index. -/
def involution (a : GroupAlgebra Γ) : GroupAlgebra Γ :=
  .ofCoeff (Finsupp.equivMapDomain (Equiv.inv Γ)
    (a.coeff.mapRange star (star_zero ℂ)))

@[simp]
theorem coeff_involution (a : GroupAlgebra Γ) (g : Γ) :
    (involution a).coeff g = star (a.coeff g⁻¹) := rfl

@[simp]
theorem involution_zero : involution (0 : GroupAlgebra Γ) = 0 := by
  ext g
  simp

theorem involution_add (a b : GroupAlgebra Γ) :
    involution (a + b) = involution a + involution b := by
  ext g
  simp

theorem involution_smul (z : ℂ) (a : GroupAlgebra Γ) :
    involution (z • a) = star z • involution a := by
  ext g
  simp

@[simp]
theorem involution_involution (a : GroupAlgebra Γ) :
    involution (involution a) = a := by
  ext g
  simp

@[simp]
theorem involution_single (g : Γ) (z : ℂ) :
    involution (MonoidAlgebra.single g z) = MonoidAlgebra.single g⁻¹ (star z) := by
  simp only [involution, MonoidAlgebra.coeff_single, Finsupp.mapRange_single,
    Finsupp.equivMapDomain_single, Equiv.inv_apply, MonoidAlgebra.ofCoeff_single]

theorem involution_mul (a b : GroupAlgebra Γ) :
    involution (a * b) = involution b * involution a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a c ha hc => simp only [add_mul, involution_add, ha, hc, mul_add]
  | single g z =>
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add b c hb hc => simp only [mul_add, involution_add, hb, hc, add_mul]
    | single h w => simp [MonoidAlgebra.single_mul_single, mul_inv_rev, mul_comm]

/-- The group-algebra star is conjugation combined with inversion. -/
instance instStar : Star (GroupAlgebra Γ) := ⟨involution⟩

/-- Convolution and the group-algebra involution form a star ring. -/
instance instStarRing : StarRing (GroupAlgebra Γ) where
  star_involutive := involution_involution
  star_mul := involution_mul
  star_add := involution_add

/-- The involution is conjugate-linear over the complex scalars. -/
instance instStarModule : StarModule ℂ (GroupAlgebra Γ) where
  star_smul := involution_smul

@[simp]
theorem coeff_star (a : GroupAlgebra Γ) (g : Γ) :
    (star a).coeff g = star (a.coeff g⁻¹) := coeff_involution a g

/-- The multiplication agrees with the blueprint's convolution formula. -/
theorem coeff_convolution (a b : GroupAlgebra Γ) (h : Γ) :
    (a * b).coeff h = ∑ g ∈ a.coeff.support, a.coeff g * b.coeff (g⁻¹ * h) :=
  MonoidAlgebra.coeff_mul_apply_left a b h

@[simp]
theorem delta_one : delta (1 : Γ) = 1 := rfl

@[simp]
theorem delta_mul (g h : Γ) : delta g * delta h = delta (g * h) := by
  simp [delta, MonoidAlgebra.single_mul_single]

@[simp]
theorem delta_star (g : Γ) : star (delta g) = delta g⁻¹ := by
  change involution (MonoidAlgebra.single g 1) = _
  simp [delta]

theorem delta_expansion (a : GroupAlgebra Γ) :
    ∑ g ∈ a.coeff.support, a.coeff g • delta g = a := by
  simpa [delta, MonoidAlgebra.smul_single, Finsupp.sum] using a.sum_coeff_single

open scoped Pointwise in
theorem support_convolution [DecidableEq Γ] (a b : GroupAlgebra Γ) :
    (a * b).coeff.support ⊆ a.coeff.support * b.coeff.support :=
  MonoidAlgebra.support_coeff_mul_subset a b

theorem support_star (a : GroupAlgebra Γ) :
    (star a).coeff.support = a.coeff.support.map (Equiv.inv Γ).toEmbedding := by
  classical
  ext g
  simp only [Finsupp.mem_support_iff, coeff_star, star_ne_zero, Finset.mem_map,
    Equiv.toEmbedding_apply, Equiv.inv_apply]
  constructor
  · intro h
    exact ⟨g⁻¹, h, inv_inv g⟩
  · rintro ⟨h, hh, rfl⟩
    simpa using hh

theorem convolution_bilinear (a b c : GroupAlgebra Γ) (z : ℂ) :
    (a + b) * c = a * c + b * c ∧ a * (b + c) = a * b + a * c ∧
    (z • a) * b = z • (a * b) ∧ a * (z • b) = z • (a * b) :=
  ⟨add_mul a b c, mul_add a b c, smul_mul_assoc z a b, mul_smul_comm z a b⟩

/-- The laws appearing together in the blueprint's algebraic proposition. -/
theorem star_algebra_laws (a b c : GroupAlgebra Γ) (z w : ℂ) :
    (a * b) * c = a * (b * c) ∧
    (delta 1) * a = a ∧ a * (delta 1) = a ∧
    star (a * b) = star b * star a ∧ star (star a) = a ∧
    star (z • a + w • b) = star z • star a + star w • star b := by
  simp only [mul_assoc, delta_one, one_mul, mul_one, star_mul, star_star,
    star_add, star_smul, and_self]

end GroupAlgebra
end BC4lean
