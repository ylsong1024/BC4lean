import BC4lean.NearProjectionCommonRounding
import BC4lean.StandardCountableProjectionRounding

/-! # Actual common-corner comparison of two coordinate cutoffs

The genuine coordinate projections are nested, as follows on dense finite
coefficient vectors. Two compressions close to the same actual projection
therefore have a constructed rounded projection path whose whole relative
difference lies in the common larger coordinate corner. Compactness follows
from the original compact difference and CFC factorization. No coordinate
cutoff is asserted compact, and no gap is assumed independently of nearness.
-/

noncomputable section
namespace BC4lean.KKTheory
open unitInterval

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

local notation "StdPair" => HilbertModuleSum B (StandardCountableHilbertModule B)
  (StandardCountableHilbertModule B)
local notation "StdEnd" => AdjointableMap B StdPair StdPair

/-- Genuine coefficient cutoffs are nested; the proof uses the actual dense
finite-support realization of the standard module. -/
theorem standardCountableCutoff_mul_of_le {n m : ℕ} (h : n ≤ m) :
    standardCountableCutoff (B := B) n * standardCountableCutoff m = standardCountableCutoff n := by
  apply standardCountable_adjointable_ext_mk
  intro x
  simp only [AdjointableMap.mul_apply, standardCountableCutoff_mk]
  congr 1
  ext i
  simp only [Finsupp.filter_apply]
  by_cases hi : i < n
  · simp only [hi, lt_of_lt_of_le hi h, if_true]
  · simp only [hi, if_false]

/-- The same exact nesting holds on the actual two-summand module. -/
theorem standardCountablePairedCutoff_mul_of_le {n m : ℕ} (h : n ≤ m) :
    standardCountablePairedCutoff (B := B) n * standardCountablePairedCutoff m =
      standardCountablePairedCutoff n := by
  simp only [standardCountablePairedCutoff, ← sumMap_mul, standardCountableCutoff_mul_of_le h]

/-- Nesting annihilates the entire larger right coordinate tail. -/
theorem standardCountablePairedCutoff_mul_one_sub_of_le {n m : ℕ} (h : n ≤ m) :
    standardCountablePairedCutoff (B := B) n * (1 - standardCountablePairedCutoff m) = 0 := by
  rw [mul_sub, mul_one, standardCountablePairedCutoff_mul_of_le h, sub_self]

/-- The smaller compression retains the exact reference action on every
coordinate outside the larger corner. -/
theorem standardCountableReferenceCompression_right_tail_of_le
    (P : StdEnd) {n m : ℕ} (h : n ≤ m) :
    standardCountableReferenceCompression P n * (1 - standardCountablePairedCutoff m) =
      standardCountablePairedReferenceProjection * (1 - standardCountablePairedCutoff m) := by
  simp only [standardCountableReferenceCompression, add_mul, mul_assoc,
    standardCountablePairedCutoff_mul_one_sub_of_le h, mul_zero, add_zero]

/-- The actual common-nearness argument constructs the rounded comparison
path; its gap is derived from the stated actual norm errors. -/
def standardCountableCutoffComparisonPath
    (P : StdEnd) (hP : IsStarProjection P) (n m : ℕ)
    (hn : ‖standardCountableReferenceCompression P n - P‖ < 1 / 64)
    (hm : ‖standardCountableReferenceCompression P m - P‖ < 1 / 64) :
    Path (spectralGapRoundedProjection (standardCountableReferenceCompression P n))
      (spectralGapRoundedProjection (standardCountableReferenceCompression P m)) :=
  commonNearProjectionRoundedPath P (standardCountableReferenceCompression P n)
    (standardCountableReferenceCompression P m) hP
    (standardCountableReferenceCompression_isSelfAdjoint P hP.isSelfAdjoint n)
    (standardCountableReferenceCompression_isSelfAdjoint P hP.isSelfAdjoint m) hn hm

/-- Every value of the constructed cutoff comparison is a genuine projection. -/
theorem standardCountableCutoffComparisonPath_isStarProjection
    (P : StdEnd) (hP : IsStarProjection P) (n m : ℕ)
    (hn : ‖standardCountableReferenceCompression P n - P‖ < 1 / 64)
    (hm : ‖standardCountableReferenceCompression P m - P‖ < 1 / 64) (t : I) :
    IsStarProjection (standardCountableCutoffComparisonPath P hP n m hn hm t) :=
  commonNearProjectionRoundedPath_isStarProjection P (standardCountableReferenceCompression P n)
    (standardCountableReferenceCompression P m) hP
    (standardCountableReferenceCompression_isSelfAdjoint P hP.isSelfAdjoint n)
    (standardCountableReferenceCompression_isSelfAdjoint P hP.isSelfAdjoint m) hn hm t

/-- Genuine compactness of the original relative projection supplies
compactness throughout the constructed comparison path. -/
theorem standardCountableCutoffComparisonPath_sub_reference_isModuleCompact
    (P : StdEnd) (hP : IsStarProjection P)
    (hc : IsModuleCompact (P - standardCountablePairedReferenceProjection)) (n m : ℕ)
    (hn : ‖standardCountableReferenceCompression P n - P‖ < 1 / 64)
    (hm : ‖standardCountableReferenceCompression P m - P‖ < 1 / 64) (t : I) :
    IsModuleCompact (standardCountableCutoffComparisonPath P hP n m hn hm t -
      standardCountablePairedReferenceProjection) := by
  let a₀ := standardCountableReferenceCompression P n
  let a₁ := standardCountableReferenceCompression P m
  have h₀ : IsModuleCompact (a₀ - standardCountablePairedReferenceProjection) :=
    standardCountableReferenceCompression_sub_isModuleCompact P hc n
  have h₁ : IsModuleCompact (a₁ - standardCountablePairedReferenceProjection) :=
    standardCountableReferenceCompression_sub_isModuleCompact P hc m
  have hDifference : IsModuleCompact (a₁ - a₀) := by
    have h := h₁.sub h₀
    have heq : (a₁ - standardCountablePairedReferenceProjection) -
        (a₀ - standardCountablePairedReferenceProjection) = a₁ - a₀ := by abel
    rwa [heq] at h
  have hAffine : IsModuleCompact (nearProjectionAffine a₀ a₁ t -
      standardCountablePairedReferenceProjection) := by
    have heq : nearProjectionAffine a₀ a₁ t - standardCountablePairedReferenceProjection =
        (a₀ - standardCountablePairedReferenceProjection) + (t : ℝ) • (a₁ - a₀) := by
      dsimp only [nearProjectionAffine]
      abel
    rw [heq, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact h₀.add (hDifference.smul ((t : ℝ) : ℂ))
  exact spectralGapRoundedProjection_sub_reference_isModuleCompact _
    (nearProjectionAffine_isSelfAdjoint_of_selfAdjoint a₀ a₁
      (standardCountableReferenceCompression_isSelfAdjoint P hP.isSelfAdjoint n)
      (standardCountableReferenceCompression_isSelfAdjoint P hP.isSelfAdjoint m) t) hAffine

/-- The full comparison path has the same exact reference action on the
right tail of the actual larger coordinate corner. -/
theorem standardCountableCutoffComparisonPath_right_tail
    (P : StdEnd) (hP : IsStarProjection P) (n m : ℕ)
    (hn : ‖standardCountableReferenceCompression P n - P‖ < 1 / 64)
    (hm : ‖standardCountableReferenceCompression P m - P‖ < 1 / 64) (t : I) :
    standardCountableCutoffComparisonPath P hP n m hn hm t *
        (1 - standardCountablePairedCutoff (max n m)) =
      standardCountablePairedReferenceProjection * (1 - standardCountablePairedCutoff (max n m)) := by
  apply commonNearProjectionRoundedPath_reference_right_tail
    P (standardCountableReferenceCompression P n) (standardCountableReferenceCompression P m)
    standardCountablePairedReferenceProjection (1 - standardCountablePairedCutoff (max n m)) hP
    (standardCountableReferenceCompression_isSelfAdjoint P hP.isSelfAdjoint n)
    (standardCountableReferenceCompression_isSelfAdjoint P hP.isSelfAdjoint m) hn hm
    standardCountablePairedReferenceProjection_isStarProjection
    (standardCountableReferenceCompression_right_tail_of_le P (le_max_left n m))
    (standardCountableReferenceCompression_right_tail_of_le P (le_max_right n m))
  simp only [mul_sub, sub_mul, mul_one, one_mul,
    standardCountablePairedCutoff_commutes_reference]

/-- Selfadjointness gives the corresponding exact left tail. -/
theorem standardCountableCutoffComparisonPath_left_tail
    (P : StdEnd) (hP : IsStarProjection P) (n m : ℕ)
    (hn : ‖standardCountableReferenceCompression P n - P‖ < 1 / 64)
    (hm : ‖standardCountableReferenceCompression P m - P‖ < 1 / 64) (t : I) :
    (1 - standardCountablePairedCutoff (max n m)) *
        standardCountableCutoffComparisonPath P hP n m hn hm t =
      (1 - standardCountablePairedCutoff (max n m)) * standardCountablePairedReferenceProjection := by
  have h := congrArg star (standardCountableCutoffComparisonPath_right_tail P hP n m hn hm t)
  have hR := (standardCountableCutoffComparisonPath_isStarProjection P hP n m hn hm t).isSelfAdjoint.star_eq
  have hQ := (standardCountablePairedReferenceProjection_isStarProjection (B := B)).isSelfAdjoint.star_eq
  have hC : star (standardCountablePairedCutoff (B := B) (max n m)) =
      standardCountablePairedCutoff (max n m) := standardCountablePairedCutoff_adjoint _
  simpa only [star_mul, star_sub, star_one, hR, hQ, hC] using h

/-- The entire relative difference lies in the genuine common coordinate
corner throughout the comparison, as follows from both proved zero tails. -/
theorem standardCountableCutoffComparisonPath_sub_eq_common_cutoff
    (P : StdEnd) (hP : IsStarProjection P) (n m : ℕ)
    (hn : ‖standardCountableReferenceCompression P n - P‖ < 1 / 64)
    (hm : ‖standardCountableReferenceCompression P m - P‖ < 1 / 64) (t : I) :
    standardCountableCutoffComparisonPath P hP n m hn hm t - standardCountablePairedReferenceProjection =
      standardCountablePairedCutoff (max n m) *
        (standardCountableCutoffComparisonPath P hP n m hn hm t -
          standardCountablePairedReferenceProjection) * standardCountablePairedCutoff (max n m) := by
  have hLeft : (1 - standardCountablePairedCutoff (max n m)) *
      (standardCountableCutoffComparisonPath P hP n m hn hm t -
        standardCountablePairedReferenceProjection) = 0 := by
    rw [mul_sub, standardCountableCutoffComparisonPath_left_tail P hP n m hn hm t, sub_self]
  have hRight : (standardCountableCutoffComparisonPath P hP n m hn hm t -
      standardCountablePairedReferenceProjection) * (1 - standardCountablePairedCutoff (max n m)) = 0 := by
    rw [sub_mul, standardCountableCutoffComparisonPath_right_tail P hP n m hn hm t, sub_self]
  rw [sub_mul, one_mul] at hLeft
  rw [mul_sub, mul_one] at hRight
  rw [← sub_eq_zero.mp hLeft, ← sub_eq_zero.mp hRight]

end BC4lean.KKTheory
