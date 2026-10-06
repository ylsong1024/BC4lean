import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Tactic.NoncommRing

/-! # Strong coefficient approximate units on Hilbert modules

An actual positive contractive coefficient approximate unit acts strongly on
every Hilbert C⋆-module. This follows from a quantitative diagonal estimate;
neither module completeness nor a separate essentiality assumption is used.
The proper canonical approximate-unit filter also gives selfadjoint
contractive coefficients approximating any finite family of vectors.
-/

noncomputable section
namespace BC4lean.KKTheory

open Filter
open scoped Topology

variable {D M : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul D M] [CStarModule D M]

/-- A selfadjoint coefficient's strong-action error is controlled by its
approximate-unit error on the actual diagonal inner product. -/
theorem norm_sub_coefficient_smul_sq_le (e : D) (he : star e = e) (x : M) :
    ‖x - e • x‖ ^ 2 ≤
      (1 + ‖e‖) * ‖inner D x x - e * inner D x x‖ := by
  have hexpand : inner D (x - e • x) (x - e • x) =
      (inner D x x - e * inner D x x) -
        (inner D x x - e * inner D x x) * e := by
    simp only [CStarModule.inner_sub_right, CStarModule.inner_sub_left,
      CStarModule.inner_op_smul_right, CStarModule.inner_op_smul_left, he]
    noncomm_ring
  rw [CStarModule.norm_sq_eq D, hexpand]
  calc
    _ ≤ ‖inner D x x - e * inner D x x‖ +
        ‖(inner D x x - e * inner D x x) * e‖ := norm_sub_le _ _
    _ ≤ ‖inner D x x - e * inner D x x‖ +
        ‖inner D x x - e * inner D x x‖ * ‖e‖ :=
      add_le_add (le_refl _) (norm_mul_le _ _)
    _ = _ := by ring

variable [StarOrderedRing D]

/-- Every vector has arbitrarily small strong-action error eventually along
an actual increasing coefficient approximate-unit filter. -/
theorem _root_.Filter.IsIncreasingApproximateUnit.eventually_norm_sub_smul_lt
    {l : Filter D} (hau : l.IsIncreasingApproximateUnit) (x : M) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ e : D in l, ‖x - e • x‖ < δ := by
  let a := inner D x x
  have hlim : Tendsto (fun e : D => ‖a - e * a‖)
      l (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      ((tendsto_const_nhds (x := a)).sub (hau.tendsto_mul_right a)).norm
  have hsmall : ∀ᶠ e : D in l,
      ‖a - e * a‖ < δ ^ 2 / 2 :=
    hlim.eventually (gt_mem_nhds (by positivity : 0 < δ ^ 2 / 2))
  filter_upwards [hau.eventually_norm, hau.eventually_star_eq, hsmall]
    with e he1 he heδ
  apply (pow_lt_pow_iff_left₀ (norm_nonneg _) hδ.le (by decide : (2 : ℕ) ≠ 0)).mp
  calc
    ‖x - e • x‖ ^ 2 ≤ (1 + ‖e‖) * ‖a - e * a‖ :=
      norm_sub_coefficient_smul_sq_le e he x
    _ ≤ 2 * ‖a - e * a‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < δ ^ 2 := by linarith

/-- Canonical-filter version of the generic increasing-AU error estimate. -/
theorem eventually_norm_sub_coefficient_smul_lt (x : M) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ e : D in CStarAlgebra.approximateUnit D, ‖x - e • x‖ < δ :=
  (CStarAlgebra.increasingApproximateUnit D).eventually_norm_sub_smul_lt x δ hδ

/-- Every increasing coefficient approximate-unit filter acts strongly on
the module. This also applies to actual mapped approximate-unit filters. -/
theorem _root_.Filter.IsIncreasingApproximateUnit.tendsto_smul
    {l : Filter D} (hau : l.IsIncreasingApproximateUnit) (x : M) :
    Tendsto (fun e : D => e • x) l (𝓝 x) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  filter_upwards [hau.eventually_norm_sub_smul_lt x δ hδ] with e he
  simpa only [dist_eq_norm, norm_sub_rev] using he

/-- The positive contractive canonical coefficient approximate unit acts
strongly on the Hilbert module, with no completeness assumption on it. -/
theorem tendsto_coefficient_approximateUnit_smul (x : M) :
    Tendsto (fun e : D => e • x) (CStarAlgebra.approximateUnit D) (𝓝 x) :=
  (CStarAlgebra.increasingApproximateUnit D).tendsto_smul x

/-- One actual selfadjoint contractive coefficient approximates every vector
in a specified finite family. Positivity is retained from the canonical AU. -/
theorem exists_positive_selfadjoint_contraction_smul_approx_on (s : Finset M)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ e : D, 0 ≤ e ∧ ‖e‖ ≤ 1 ∧ star e = e ∧
      ∀ x ∈ s, ‖x - e • x‖ < δ := by
  classical
  have hau := CStarAlgebra.increasingApproximateUnit D
  have herr : ∀ᶠ e : D in CStarAlgebra.approximateUnit D,
      ∀ x ∈ s, ‖x - e • x‖ < δ :=
    (eventually_all_finset s).mpr (fun x _ =>
      eventually_norm_sub_coefficient_smul_lt x δ hδ)
  exact (hau.eventually_nonneg.and
    (hau.eventually_norm.and (hau.eventually_star_eq.and herr))).exists

/-- Finite-family selection with exactly the contraction/selfadjoint data
needed in norm comparison and cutoff arguments. -/
theorem exists_selfadjoint_contraction_smul_approx_on (s : Finset M)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ e : D, ‖e‖ ≤ 1 ∧ star e = e ∧ ∀ x ∈ s, ‖x - e • x‖ < δ := by
  obtain ⟨e, _, he1, he, herr⟩ :=
    exists_positive_selfadjoint_contraction_smul_approx_on (D := D) s δ hδ
  exact ⟨e, he1, he, herr⟩

/-- Single-vector selection as a direct consequence of the actual finite
selection, without a separate essentiality or multiplier action hypothesis. -/
theorem exists_selfadjoint_contraction_smul_approx (x : M) (δ : ℝ) (hδ : 0 < δ) :
    ∃ e : D, ‖e‖ ≤ 1 ∧ star e = e ∧ ‖x - e • x‖ < δ := by
  classical
  obtain ⟨e, he1, he, herr⟩ :=
    exists_selfadjoint_contraction_smul_approx_on (D := D) ({x} : Finset M) δ hδ
  exact ⟨e, he1, he, herr x (Finset.mem_singleton_self x)⟩

end BC4lean.KKTheory
