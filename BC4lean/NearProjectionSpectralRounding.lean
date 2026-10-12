import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
import Mathlib.Topology.Path
import Mathlib.Tactic.NoncommRing

/-! # Genuine spectral rounding of an operator near a projection

Operator-norm closeness to an actual projection gives a quantitative bound
on a²−a. The real CFC norm bound then excludes the middle spectral interval,
without a spectral-gap hypothesis. A fixed globally continuous cutoff rounds
the entire affine interpolation to actual projections and supplies a genuine
norm-continuous projection path.
-/

noncomputable section
namespace BC4lean.KKTheory

open unitInterval

/-- The continuous rounding function, zero below 1/4 and one above 3/4. -/
def projectionRoundCutoff (r : ℝ) : ℝ := min 1 (max 0 (2 * r - 1 / 2))

@[fun_prop] theorem continuous_projectionRoundCutoff : Continuous projectionRoundCutoff :=
  continuous_const.min
    (continuous_const.max ((continuous_const.mul continuous_id).sub continuous_const))

theorem projectionRoundCutoff_eq_zero {r : ℝ} (hr : r ≤ 1 / 4) :
    projectionRoundCutoff r = 0 := by
  have hh : 2 * r - 1 / 2 ≤ 0 := by linarith
  simp only [projectionRoundCutoff, max_eq_left hh]
  norm_num

theorem projectionRoundCutoff_eq_one {r : ℝ} (hr : 3 / 4 ≤ r) :
    projectionRoundCutoff r = 1 := by
  have hh : 1 ≤ 2 * r - 1 / 2 := by linarith
  rw [projectionRoundCutoff, max_eq_right (zero_le_one.trans hh), min_eq_left hh]

@[simp] theorem projectionRoundCutoff_zero : projectionRoundCutoff 0 = 0 :=
  projectionRoundCutoff_eq_zero (by norm_num)

@[simp] theorem projectionRoundCutoff_one : projectionRoundCutoff 1 = 1 :=
  projectionRoundCutoff_eq_one (by norm_num)

/-- Continuous division away from the flat zero region of the cutoff. -/
def projectionRoundZeroFactor (r : ℝ) : ℝ := projectionRoundCutoff r / max (1 / 4) r

/-- Continuous division away from the flat one region of the cutoff. -/
def projectionRoundOneFactor (r : ℝ) : ℝ :=
  (projectionRoundCutoff r - 1) / min (-1 / 4) (r - 1)

@[fun_prop] theorem continuous_projectionRoundZeroFactor : Continuous projectionRoundZeroFactor :=
  continuous_projectionRoundCutoff.div (continuous_const.max continuous_id)
    (fun r => ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) (le_max_left _ _)))

@[fun_prop] theorem continuous_projectionRoundOneFactor : Continuous projectionRoundOneFactor :=
  (continuous_projectionRoundCutoff.sub continuous_const).div
    (continuous_const.min (continuous_id.sub continuous_const))
    (fun r => ne_of_lt (lt_of_le_of_lt (min_le_left _ _) (by norm_num : (-1 / 4 : ℝ) < 0)))

theorem projectionRoundCutoff_zero_factor (r : ℝ) :
    projectionRoundCutoff r = projectionRoundZeroFactor r * r := by
  rcases le_total r (1 / 4) with hr | hr
  · rw [projectionRoundCutoff_eq_zero hr]
    simp only [projectionRoundZeroFactor, projectionRoundCutoff_eq_zero hr, zero_div, zero_mul]
  · have hn : r ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hr)
    rw [projectionRoundZeroFactor, max_eq_right hr, div_mul_cancel₀ _ hn]

theorem projectionRoundCutoff_one_factor (r : ℝ) :
    projectionRoundCutoff r - 1 = projectionRoundOneFactor r * (r - 1) := by
  rcases le_total r (3 / 4) with hr | hr
  · have hd : r - 1 ≤ -1 / 4 := by linarith
    have hn : r - 1 ≠ 0 := ne_of_lt (lt_of_le_of_lt hd (by norm_num : (-1 / 4 : ℝ) < 0))
    rw [projectionRoundOneFactor, min_eq_right hd, div_mul_cancel₀ _ hn]
  · rw [projectionRoundCutoff_eq_one hr]
    simp only [projectionRoundOneFactor, projectionRoundCutoff_eq_one hr, sub_self, zero_div, zero_mul]

variable {A : Type*} [CStarAlgebra A]

/-- An actual near-projection has its polynomial defect bounded directly by
its operator-norm distance to the given projection. -/
theorem norm_projection_defect_le (p a : A) (hp : IsStarProjection p) :
    ‖a * a - a‖ ≤ ‖a - p‖ * ‖a - p‖ + 3 * ‖a - p‖ := by
  have hexpand : (a - p) * (a - p) + (a - p) * p + p * (a - p) - (a - p) =
      a * a - a + (p - p * p) := by noncomm_ring
  rw [hp.isIdempotentElem.eq, sub_self, add_zero] at hexpand
  rw [← hexpand]
  have hpNorm : ‖p‖ ≤ 1 := IsStarProjection.norm_le p hp
  have hright : ‖(a - p) * p‖ ≤ ‖a - p‖ := by
    calc
      ‖(a - p) * p‖ ≤ ‖a - p‖ * ‖p‖ := norm_mul_le _ _
      _ ≤ ‖a - p‖ * 1 := mul_le_mul_of_nonneg_left hpNorm (norm_nonneg _)
      _ = ‖a - p‖ := mul_one _
  have hleft : ‖p * (a - p)‖ ≤ ‖a - p‖ := by
    calc
      ‖p * (a - p)‖ ≤ ‖p‖ * ‖a - p‖ := norm_mul_le _ _
      _ ≤ 1 * ‖a - p‖ := mul_le_mul_of_nonneg_right hpNorm (norm_nonneg _)
      _ = ‖a - p‖ := one_mul _
  calc
    ‖(a - p) * (a - p) + (a - p) * p + p * (a - p) - (a - p)‖ ≤
        ‖(a - p) * (a - p) + (a - p) * p + p * (a - p)‖ + ‖a - p‖ := norm_sub_le _ _
    _ ≤ ‖(a - p) * (a - p) + (a - p) * p‖ + ‖p * (a - p)‖ + ‖a - p‖ :=
      add_le_add (norm_add_le _ _) (le_refl _)
    _ ≤ ‖(a - p) * (a - p)‖ + ‖(a - p) * p‖ + ‖p * (a - p)‖ + ‖a - p‖ :=
      add_le_add (add_le_add (norm_add_le _ _) (le_refl _)) (le_refl _)
    _ ≤ ‖a - p‖ * ‖a - p‖ + ‖a - p‖ + ‖a - p‖ + ‖a - p‖ :=
      add_le_add (add_le_add (add_le_add (norm_mul_le _ _) hright) hleft) (le_refl _)
    _ = ‖a - p‖ * ‖a - p‖ + 3 * ‖a - p‖ := by ring

theorem norm_projection_defect_lt (p a : A) (hp : IsStarProjection p)
    (hclose : ‖a - p‖ < 1 / 64) : ‖a * a - a‖ < 3 / 16 := by
  have hsq := mul_self_lt_mul_self (norm_nonneg (a - p)) hclose
  have hbound := norm_projection_defect_le p a hp
  nlinarith

/-- The spectral middle interval is excluded by the polynomial defect norm;
the gap is proved from actual norm closeness, rather than assumed. -/
theorem spectrum_near_projection_gap (p a : A) (hp : IsStarProjection p)
    (ha : IsSelfAdjoint a) (hclose : ‖a - p‖ < 1 / 64)
    {r : ℝ} (hr : r ∈ spectrum ℝ a) : r < 1 / 4 ∨ 3 / 4 < r := by
  have hcfc : cfc (fun s : ℝ => s * s - s) a = a * a - a := by
    rw [cfc_sub (fun s : ℝ => s * s) (fun s : ℝ => s) a
      (continuous_id.mul continuous_id).continuousOn continuousOn_id,
      cfc_mul (fun s : ℝ => s) (fun s : ℝ => s) a continuousOn_id continuousOn_id,
      cfc_id' ℝ a ha]
  have hnorm := norm_apply_le_norm_cfc (fun s : ℝ => s * s - s) a hr (by fun_prop) ha
  rw [hcfc] at hnorm
  have hsmall := norm_projection_defect_lt p a hp hclose
  by_contra hgap
  push Not at hgap
  have hproduct : 0 ≤ (r - 1 / 4) * (3 / 4 - r) :=
    mul_nonneg (sub_nonneg.mpr hgap.1) (sub_nonneg.mpr hgap.2)
  have hlower : 3 / 16 ≤ r - r * r := by nlinarith
  have habs : r - r * r ≤ ‖r * r - r‖ := by
    simpa only [Real.norm_eq_abs, neg_sub] using neg_le_abs (r * r - r)
  linarith

/-- CFC rounding is defined on the actual ambient C⋆-algebra. -/
def spectralGapRoundedProjection (a : A) : A := cfc projectionRoundCutoff a

/-- The rounded operator is a genuine continuous factor times the original
operator. This factor controls the exact zero tail. -/
theorem spectralGapRoundedProjection_zero_factor (a : A) (ha : IsSelfAdjoint a) :
    spectralGapRoundedProjection a = cfc projectionRoundZeroFactor a * a := by
  calc
    spectralGapRoundedProjection a = cfc (fun r : ℝ => projectionRoundZeroFactor r * r) a :=
      cfc_congr (fun r _ => projectionRoundCutoff_zero_factor r)
    _ = cfc projectionRoundZeroFactor a * a := by
      rw [cfc_mul projectionRoundZeroFactor (fun r : ℝ => r) a
        continuous_projectionRoundZeroFactor.continuousOn continuousOn_id, cfc_id' ℝ a ha]

/-- The difference from identity is a genuine continuous factor times a−1.
This factor controls the exact identity tail. -/
theorem spectralGapRoundedProjection_one_factor (a : A) (ha : IsSelfAdjoint a) :
    spectralGapRoundedProjection a - 1 = cfc projectionRoundOneFactor a * (a - 1) := by
  have hc : cfc (fun r : ℝ => projectionRoundCutoff r - 1) a =
      spectralGapRoundedProjection a - 1 := by
    rw [cfc_sub projectionRoundCutoff (fun _ : ℝ => 1) a
      continuous_projectionRoundCutoff.continuousOn continuousOn_const, cfc_const_one ℝ a ha]
    rfl
  rw [← hc]
  calc
    _ = cfc (fun r : ℝ => projectionRoundOneFactor r * (r - 1)) a :=
      cfc_congr (fun r _ => projectionRoundCutoff_one_factor r)
    _ = cfc projectionRoundOneFactor a * (a - 1) := by
      rw [cfc_mul projectionRoundOneFactor (fun r : ℝ => r - 1) a
        continuous_projectionRoundOneFactor.continuousOn
          (continuous_id.sub continuous_const).continuousOn,
        cfc_sub (fun r : ℝ => r) (fun _ : ℝ => 1) a continuousOn_id continuousOn_const,
        cfc_id' ℝ a ha, cfc_const_one ℝ a ha]

/-- A genuine zero eigenspace is fixed at zero by the constructed rounding. -/
theorem spectralGapRoundedProjection_mul_eq_zero (a x : A) (ha : IsSelfAdjoint a)
    (hx : a * x = 0) : spectralGapRoundedProjection a * x = 0 := by
  rw [spectralGapRoundedProjection_zero_factor a ha, mul_assoc, hx, mul_zero]

/-- A genuine identity eigenspace is fixed at identity by the constructed rounding. -/
theorem spectralGapRoundedProjection_mul_eq_self (a x : A) (ha : IsSelfAdjoint a)
    (hx : a * x = x) : spectralGapRoundedProjection a * x = x := by
  have hh : (a - 1) * x = 0 := by rw [sub_mul, hx, one_mul, sub_self]
  have hr : (spectralGapRoundedProjection a - 1) * x = 0 := by
    rw [spectralGapRoundedProjection_one_factor a ha, mul_assoc, hh, mul_zero]
  rw [sub_mul, one_mul] at hr
  exact sub_eq_zero.mp hr

/-- The actual rounded difference from a reference projection factors through
the original difference. No quotient C⋆-algebra or compactness of the reference
projection is assumed. -/
theorem spectralGapRoundedProjection_sub_projection (a q : A) (ha : IsSelfAdjoint a)
    (hq : IsStarProjection q) :
    spectralGapRoundedProjection a - q =
      cfc projectionRoundZeroFactor a * (a - q) * (1 - q) +
        cfc projectionRoundOneFactor a * (a - q) * q := by
  have hzero : a * (1 - q) = (a - q) * (1 - q) := by
    rw [sub_mul, hq.mul_one_sub_self, sub_zero]
  have hone : (a - 1) * q = (a - q) * q := by
    simp only [sub_mul, one_mul, hq.isIdempotentElem.eq]
  calc
    spectralGapRoundedProjection a - q = spectralGapRoundedProjection a * (1 - q) +
        (spectralGapRoundedProjection a - 1) * q := by noncomm_ring
    _ = cfc projectionRoundZeroFactor a * (a * (1 - q)) +
        cfc projectionRoundOneFactor a * ((a - 1) * q) := by
      rw [spectralGapRoundedProjection_one_factor a ha,
        spectralGapRoundedProjection_zero_factor a ha]
      simp only [mul_assoc]
    _ = _ := by rw [hzero, hone]; simp only [mul_assoc]

/-- An exact reference tail is retained under the actual CFC rounding, proved
by the zero/identity factorization on its two reference subspaces. -/
theorem spectralGapRoundedProjection_reference_right_tail (a q e : A)
    (ha : IsSelfAdjoint a) (hq : IsStarProjection q)
    (hTail : a * e = q * e) (hCommute : q * e = e * q) :
    spectralGapRoundedProjection a * e = q * e := by
  have hzero : a * (e * (1 - q)) = 0 := by
    rw [← mul_assoc, hTail, hCommute, mul_assoc, hq.mul_one_sub_self, mul_zero]
  have hone : a * (e * q) = e * q := by
    rw [← mul_assoc, hTail, hCommute, mul_assoc, hq.isIdempotentElem.eq]
  calc
    spectralGapRoundedProjection a * e =
        spectralGapRoundedProjection a * (e * (1 - q) + e * q) := by
      congr 1
      noncomm_ring
    _ = e * q := by
      rw [mul_add, spectralGapRoundedProjection_mul_eq_zero a _ ha hzero,
        spectralGapRoundedProjection_mul_eq_self a _ ha hone, zero_add]
    _ = q * e := hCommute.symm

/-- The rounded element is a genuine projection whenever the stated actual
norm closeness to a projection holds. -/
theorem spectralGapRoundedProjection_isStarProjection (p a : A) (hp : IsStarProjection p)
    (ha : IsSelfAdjoint a) (hclose : ‖a - p‖ < 1 / 64) :
    IsStarProjection (spectralGapRoundedProjection a) := by
  apply isStarProjection_iff'.mpr
  constructor
  · change cfc projectionRoundCutoff a * cfc projectionRoundCutoff a = cfc projectionRoundCutoff a
    rw [← cfc_mul projectionRoundCutoff projectionRoundCutoff a
      continuous_projectionRoundCutoff.continuousOn continuous_projectionRoundCutoff.continuousOn]
    apply cfc_congr
    intro r hr
    rcases spectrum_near_projection_gap p a hp ha hclose hr with hr | hr
    · change projectionRoundCutoff r * projectionRoundCutoff r = projectionRoundCutoff r
      rw [projectionRoundCutoff_eq_zero hr.le, zero_mul]
    · change projectionRoundCutoff r * projectionRoundCutoff r = projectionRoundCutoff r
      rw [projectionRoundCutoff_eq_one hr.le, one_mul]
  · exact (cfc_predicate projectionRoundCutoff a).star_eq

/-- Rounding fixes every actual projection, including both scalar values. -/
@[simp] theorem spectralGapRoundedProjection_projection (p : A) (hp : IsStarProjection p) :
    spectralGapRoundedProjection p = p := by
  change cfc projectionRoundCutoff p = p
  calc
    cfc projectionRoundCutoff p = cfc (fun r : ℝ => r) p := by
      apply cfc_congr
      intro r hr
      rcases hp.isIdempotentElem.spectrum_subset ℝ hr with hr | hr
      · rw [Set.mem_singleton_iff.mp hr]
        exact projectionRoundCutoff_zero
      · rw [Set.mem_singleton_iff.mp hr]
        exact projectionRoundCutoff_one
    _ = p := cfc_id' ℝ p hp.isSelfAdjoint

/-- The actual affine interpolation before rounding. -/
def nearProjectionAffine (p a : A) (t : I) : A := p + (t : ℝ) • (a - p)

theorem continuous_nearProjectionAffine (p a : A) : Continuous (nearProjectionAffine p a) :=
  continuous_const.add (continuous_subtype_val.smul continuous_const)

@[simp] theorem nearProjectionAffine_zero (p a : A) : nearProjectionAffine p a 0 = p := by
  simp [nearProjectionAffine]

@[simp] theorem nearProjectionAffine_one (p a : A) : nearProjectionAffine p a 1 = a := by
  change p + (1 : ℝ) • (a - p) = a
  rw [one_smul]
  abel

theorem nearProjectionAffine_isSelfAdjoint (p a : A) (hp : IsStarProjection p)
    (ha : IsSelfAdjoint a) (t : I) : IsSelfAdjoint (nearProjectionAffine p a t) := by
  change star (p + (t : ℝ) • (a - p)) = p + (t : ℝ) • (a - p)
  simp only [star_add, star_smul, star_sub, star_trivial, hp.isSelfAdjoint.star_eq, ha.star_eq]

/-- Every interpolation point remains at most as far from p as the original a. -/
theorem norm_nearProjectionAffine_sub_le (p a : A) (t : I) :
    ‖nearProjectionAffine p a t - p‖ ≤ ‖a - p‖ := by
  have heq : nearProjectionAffine p a t - p = (t : ℝ) • (a - p) := by
    dsimp only [nearProjectionAffine]
    abel
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg (a - p))

theorem nearProjectionAffine_spectrum_subset (p a : A) (hp : IsStarProjection p)
    (ha : IsSelfAdjoint a) (hclose : ‖a - p‖ < 1 / 64) (t : I) :
    spectrum ℝ (nearProjectionAffine p a t) ⊆ Set.Icc (-2) 2 := by
  have hnorm : ‖nearProjectionAffine p a t‖ < 2 := by
    have hb : ‖nearProjectionAffine p a t‖ ≤ ‖nearProjectionAffine p a t - p‖ + ‖p‖ := by
      calc
        ‖nearProjectionAffine p a t‖ = ‖(nearProjectionAffine p a t - p) + p‖ := by rw [sub_add_cancel]
        _ ≤ ‖nearProjectionAffine p a t - p‖ + ‖p‖ := norm_add_le _ _
    have hd := norm_nearProjectionAffine_sub_le p a t
    have hpNorm : ‖p‖ ≤ 1 := IsStarProjection.norm_le p hp
    linarith
  intro r hr
  have hb := norm_apply_le_norm_cfc (fun s : ℝ => s) (nearProjectionAffine p a t) hr
    continuousOn_id (nearProjectionAffine_isSelfAdjoint p a hp ha t)
  rw [cfc_id' ℝ _ (nearProjectionAffine_isSelfAdjoint p a hp ha t)] at hb
  have hh : |r| < 2 := by simpa only [Real.norm_eq_abs] using hb.trans_lt hnorm
  exact ⟨(abs_lt.mp hh).1.le, (abs_lt.mp hh).2.le⟩

/-- The fixed CFC cutoff gives a genuinely norm-continuous rounded interpolation. -/
theorem continuous_spectralGapRoundedProjection_affine (p a : A) (hp : IsStarProjection p)
    (ha : IsSelfAdjoint a) (hclose : ‖a - p‖ < 1 / 64) :
    Continuous (fun t : I => spectralGapRoundedProjection (nearProjectionAffine p a t)) := by
  exact (continuousOn_cfc A (isCompact_Icc : IsCompact (Set.Icc (-2 : ℝ) 2))
    projectionRoundCutoff continuous_projectionRoundCutoff.continuousOn).comp_continuous
      (continuous_nearProjectionAffine p a)
      (fun t => ⟨nearProjectionAffine_isSelfAdjoint p a hp ha t,
        nearProjectionAffine_spectrum_subset p a hp ha hclose t⟩)

/-- A genuine projection path from p to the rounded actual near-projection a. -/
def nearProjectionRoundedPath (p a : A) (hp : IsStarProjection p)
    (ha : IsSelfAdjoint a) (hclose : ‖a - p‖ < 1 / 64) :
    Path p (spectralGapRoundedProjection a) where
  toFun t := spectralGapRoundedProjection (nearProjectionAffine p a t)
  continuous_toFun := continuous_spectralGapRoundedProjection_affine p a hp ha hclose
  source' := by rw [nearProjectionAffine_zero, spectralGapRoundedProjection_projection p hp]
  target' := by rw [nearProjectionAffine_one]

/-- Every point on the constructed path is an actual projection, with its
gap deduced from the uniform interpolation estimate. -/
theorem nearProjectionRoundedPath_isStarProjection (p a : A) (hp : IsStarProjection p)
    (ha : IsSelfAdjoint a) (hclose : ‖a - p‖ < 1 / 64) (t : I) :
    IsStarProjection (nearProjectionRoundedPath p a hp ha hclose t) :=
  spectralGapRoundedProjection_isStarProjection p (nearProjectionAffine p a t) hp
    (nearProjectionAffine_isSelfAdjoint p a hp ha t)
    ((norm_nearProjectionAffine_sub_le p a t).trans_lt hclose)

end BC4lean.KKTheory
