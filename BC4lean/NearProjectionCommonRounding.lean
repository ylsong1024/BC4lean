import BC4lean.NearProjectionSpectralRounding

/-! # Common rounding of two actual approximants to one projection

Two selfadjoint elements lying within 1/64 of the same actual projection have
a convex interpolation with the same strict bound. The proved defect estimate
therefore derives a gap at every interpolation point. One fixed continuous
CFC function yields a genuine projection path between the rounded endpoints.
An exact common reference tail is preserved throughout this actual path.
-/

noncomputable section
namespace BC4lean.KKTheory
open unitInterval

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- The interpolation of two selfadjoint elements is genuinely selfadjoint. -/
theorem nearProjectionAffine_isSelfAdjoint_of_selfAdjoint
    (a₀ a₁ : A) (h₀ : IsSelfAdjoint a₀) (h₁ : IsSelfAdjoint a₁) (t : I) :
    IsSelfAdjoint (nearProjectionAffine a₀ a₁ t) := by
  change star (a₀ + (t : ℝ) • (a₁ - a₀)) = a₀ + (t : ℝ) • (a₁ - a₀)
  simp only [star_add, star_smul, star_sub, star_trivial, h₀.star_eq, h₁.star_eq]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Actual closeness to one element persists across the whole convex segment. -/
theorem norm_nearProjectionAffine_sub_common_lt
    (p a₀ a₁ : A) {ε : ℝ}
    (h₀ : ‖a₀ - p‖ < ε) (h₁ : ‖a₁ - p‖ < ε) (t : I) :
    ‖nearProjectionAffine a₀ a₁ t - p‖ < ε := by
  have hEq : nearProjectionAffine a₀ a₁ t - p =
      (1 - (t : ℝ)) • (a₀ - p) + (t : ℝ) • (a₁ - p) := by
    simp only [nearProjectionAffine, sub_smul, smul_sub, one_smul]
    abel
  have ht₀ := t.property.1
  have ht₁ : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.property.2
  have hMax : max ‖a₀ - p‖ ‖a₁ - p‖ < ε := max_lt_iff.mpr ⟨h₀, h₁⟩
  calc
    ‖nearProjectionAffine a₀ a₁ t - p‖ ≤
        (1 - (t : ℝ)) * ‖a₀ - p‖ + (t : ℝ) * ‖a₁ - p‖ := by
      rw [hEq]
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht₀, abs_of_nonneg ht₁]
        using norm_add_le ((1 - (t : ℝ)) • (a₀ - p)) ((t : ℝ) • (a₁ - p))
    _ ≤ (1 - (t : ℝ)) * max ‖a₀ - p‖ ‖a₁ - p‖ +
        (t : ℝ) * max ‖a₀ - p‖ ‖a₁ - p‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ht₁)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) ht₀)
    _ = max ‖a₀ - p‖ ‖a₁ - p‖ := by ring
    _ < ε := hMax

omit [PartialOrder A] [StarOrderedRing A] in
/-- The gap and a common compact spectral interval follow from the actual
common norm estimate, rather than being additional conditions. -/
theorem nearProjectionCommonAffine_spectrum_subset
    (p a₀ a₁ : A) (hp : IsStarProjection p)
    (h₀ : IsSelfAdjoint a₀) (h₁ : IsSelfAdjoint a₁)
    (hc₀ : ‖a₀ - p‖ < 1 / 64) (hc₁ : ‖a₁ - p‖ < 1 / 64) (t : I) :
    spectrum ℝ (nearProjectionAffine a₀ a₁ t) ⊆ Set.Icc (-2) 2 := by
  simpa only [nearProjectionAffine_one] using nearProjectionAffine_spectrum_subset
    p (nearProjectionAffine a₀ a₁ t) hp
    (nearProjectionAffine_isSelfAdjoint_of_selfAdjoint a₀ a₁ h₀ h₁ t)
    (norm_nearProjectionAffine_sub_common_lt p a₀ a₁ hc₀ hc₁ t) (1 : I)

omit [PartialOrder A] [StarOrderedRing A] in
/-- One fixed CFC cutoff varies continuously along the actual common segment. -/
theorem continuous_commonNearProjectionRounded
    (p a₀ a₁ : A) (hp : IsStarProjection p)
    (h₀ : IsSelfAdjoint a₀) (h₁ : IsSelfAdjoint a₁)
    (hc₀ : ‖a₀ - p‖ < 1 / 64) (hc₁ : ‖a₁ - p‖ < 1 / 64) :
    Continuous (fun t : I => spectralGapRoundedProjection (nearProjectionAffine a₀ a₁ t)) := by
  exact (continuousOn_cfc A (isCompact_Icc : IsCompact (Set.Icc (-2 : ℝ) 2))
    projectionRoundCutoff continuous_projectionRoundCutoff.continuousOn).comp_continuous
      (continuous_nearProjectionAffine a₀ a₁)
      (fun t => ⟨nearProjectionAffine_isSelfAdjoint_of_selfAdjoint a₀ a₁ h₀ h₁ t,
        nearProjectionCommonAffine_spectrum_subset p a₀ a₁ hp h₀ h₁ hc₀ hc₁ t⟩)

/-- Actual rounded endpoints are joined by a constructed continuous path. -/
def commonNearProjectionRoundedPath
    (p a₀ a₁ : A) (hp : IsStarProjection p)
    (h₀ : IsSelfAdjoint a₀) (h₁ : IsSelfAdjoint a₁)
    (hc₀ : ‖a₀ - p‖ < 1 / 64) (hc₁ : ‖a₁ - p‖ < 1 / 64) :
    Path (spectralGapRoundedProjection a₀) (spectralGapRoundedProjection a₁) where
  toFun t := spectralGapRoundedProjection (nearProjectionAffine a₀ a₁ t)
  continuous_toFun := continuous_commonNearProjectionRounded p a₀ a₁ hp h₀ h₁ hc₀ hc₁
  source' := by rw [nearProjectionAffine_zero]
  target' := by rw [nearProjectionAffine_one]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Each path value is a genuine projection by the derived spectral gap. -/
theorem commonNearProjectionRoundedPath_isStarProjection
    (p a₀ a₁ : A) (hp : IsStarProjection p)
    (h₀ : IsSelfAdjoint a₀) (h₁ : IsSelfAdjoint a₁)
    (hc₀ : ‖a₀ - p‖ < 1 / 64) (hc₁ : ‖a₁ - p‖ < 1 / 64) (t : I) :
    IsStarProjection (commonNearProjectionRoundedPath p a₀ a₁ hp h₀ h₁ hc₀ hc₁ t) :=
  spectralGapRoundedProjection_isStarProjection p (nearProjectionAffine a₀ a₁ t) hp
    (nearProjectionAffine_isSelfAdjoint_of_selfAdjoint a₀ a₁ h₀ h₁ t)
    (norm_nearProjectionAffine_sub_common_lt p a₀ a₁ hc₀ hc₁ t)

omit [PartialOrder A] [StarOrderedRing A] in
/-- A common exact reference tail survives every actual rounded interpolation. -/
theorem commonNearProjectionRoundedPath_reference_right_tail
    (p a₀ a₁ q e : A) (hp : IsStarProjection p)
    (h₀ : IsSelfAdjoint a₀) (h₁ : IsSelfAdjoint a₁)
    (hc₀ : ‖a₀ - p‖ < 1 / 64) (hc₁ : ‖a₁ - p‖ < 1 / 64)
    (hq : IsStarProjection q) (h₀e : a₀ * e = q * e) (h₁e : a₁ * e = q * e)
    (hqe : q * e = e * q) (t : I) :
    commonNearProjectionRoundedPath p a₀ a₁ hp h₀ h₁ hc₀ hc₁ t * e = q * e := by
  apply spectralGapRoundedProjection_reference_right_tail _ _ _
    (nearProjectionAffine_isSelfAdjoint_of_selfAdjoint a₀ a₁ h₀ h₁ t) hq _ hqe
  simp only [nearProjectionAffine, add_mul, smul_mul_assoc, sub_mul,
    h₀e, h₁e, sub_self, smul_zero, add_zero]

end BC4lean.KKTheory
