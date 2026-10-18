import BC4lean.ProperActions
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-! # The coefficient calculation for cutoff projections

These are the actual twisted convolution and involution formulas, at the
coefficient level. Normalization forces every orbit row to have finite support.
No crossed-product completion or K-theory class is asserted by this file.
The mixed coefficient gives the two partial-isometry identities used to
compare cutoff projections once they are embedded in a crossed product.
-/

noncomputable section
namespace BC4lean.ProperActions.CutoffCoefficients

variable {Γ X : Type*} [Group Γ] [MulAction Γ X]

/-- Mixed cutoff coefficient; real cutoffs are included through `Complex.ofReal`. -/
def mixed (c d : X → ℂ) (g : Γ) (x : X) : ℂ :=
  c x * star (d (g⁻¹ • x))

/-- The discrete twisted convolution formula. All rows used below have finite
support; this is not an algebra structure on arbitrary coefficient functions. -/
def convolution (f h : Γ → X → ℂ) (g : Γ) (x : X) : ℂ :=
  ∑ᶠ t : Γ, f t x * h (t⁻¹ * g) (t⁻¹ • x)

/-- The discrete crossed-product involution formula. -/
def involution (f : Γ → X → ℂ) (g : Γ) (x : X) : ℂ :=
  star (f g⁻¹ (g⁻¹ • x))

/-- Pointwise orbit normalization, including the finite orbit-support condition
implicitly forced by the nonzero finite sum. -/
def Normalized (c : X → ℂ) : Prop :=
  ∀ x, ∑ᶠ g : Γ, star (c (g⁻¹ • x)) * c (g⁻¹ • x) = 1

/-- Normalization cannot be satisfied through the default value of an infinite
support `finsum`: each actual orbit row has finite support. -/
theorem Normalized.finite_orbit_support {c : X → ℂ} (hc : Normalized (Γ := Γ) c)
    (x : X) : (Function.support (fun g : Γ => c (g⁻¹ • x))).Finite := by
  have h := hasFiniteSupport_of_finsum_eq_one (hc x)
  apply h.subset
  intro g hg
  simpa only [Function.mem_support, ne_eq, mul_eq_zero, star_eq_zero,
    or_self] using hg

theorem mixed_finite_row_support (c : X → ℂ) {d : X → ℂ}
    (hd : Normalized (Γ := Γ) d) (x : X) :
    (Function.support (fun g : Γ => mixed c d g x)).Finite := by
  apply (hd.finite_orbit_support x).subset
  intro g hg
  simp only [Function.mem_support, mixed, ne_eq, mul_eq_zero, star_eq_zero,
    not_or] at hg
  exact hg.2

/-- Inversion and conjugation exchange the two mixed cutoffs. -/
@[simp] theorem involution_mixed (c d : X → ℂ) :
    involution (mixed (Γ := Γ) c d) = mixed d c := by
  funext g x
  simp [involution, mixed, smul_smul, mul_comm]

/-- The entire convolution calculation, before applying orbit normalization. -/
theorem convolution_mixed (c d e : X → ℂ) (g : Γ) (x : X) :
    convolution (Γ := Γ) (mixed c d) (mixed d e) g x =
      c x * (∑ᶠ t : Γ, star (d (t⁻¹ • x)) * d (t⁻¹ • x)) *
        star (e (g⁻¹ • x)) := by
  simp only [convolution, mixed]
  rw [mul_finsum, finsum_mul]
  apply finsum_congr
  intro t
  simp only [mul_inv_rev, inv_inv, smul_smul, mul_inv_cancel_right]
  ring

/-- Two mixed coefficients compose by cancelling the normalized middle cutoff. -/
theorem convolution_mixed_of_normalized (c : X → ℂ) {d : X → ℂ}
    (hd : Normalized (Γ := Γ) d) (e : X → ℂ) :
    convolution (Γ := Γ) (mixed c d) (mixed d e) = mixed c e := by
  funext g x
  rw [convolution_mixed, hd x, mul_one]
  rfl

/-- The cutoff coefficient is self-adjoint for the actual involution formula. -/
theorem projection_selfadjoint (c : X → ℂ) :
    involution (mixed (Γ := Γ) c c) = mixed c c := involution_mixed c c

/-- The cutoff coefficient is idempotent for the actual convolution formula. -/
theorem projection_idempotent {c : X → ℂ} (hc : Normalized (Γ := Γ) c) :
    convolution (Γ := Γ) (mixed c c) (mixed c c) = mixed c c :=
  convolution_mixed_of_normalized c hc c

/-- The mixed coefficient times its adjoint is the first cutoff projection. -/
theorem mixed_mul_adjoint (c : X → ℂ) {d : X → ℂ}
    (hd : Normalized (Γ := Γ) d) :
    convolution (Γ := Γ) (mixed c d) (involution (mixed c d)) = mixed c c := by
  rw [involution_mixed]
  exact convolution_mixed_of_normalized c hd c

/-- Its adjoint times itself is the second cutoff projection. -/
theorem adjoint_mul_mixed {c : X → ℂ} (hc : Normalized (Γ := Γ) c)
    (d : X → ℂ) :
    convolution (Γ := Γ) (involution (mixed c d)) (mixed c d) = mixed d d := by
  rw [involution_mixed]
  exact convolution_mixed_of_normalized d hc d

end BC4lean.ProperActions.CutoffCoefficients
