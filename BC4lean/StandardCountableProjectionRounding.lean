import BC4lean.StandardCountablePairedCutoff
import BC4lean.NearProjectionSpectralRounding

/-! # Actual projection homotopy from compact reference-tail compression

The genuine compact operator-norm cutoff theorem chooses a finite coordinate
compression of an actual projection with error below 1/64. The proved spectral
rounding construction gives a genuine continuous projection path from the
original projection to its rounded compression. The continuous zero/identity
factorizations prove its compact reference difference and exact reference tail.
No gap or finite normal form is supplied as extra data. Identifying the rounded
endpoint with a finite unitization matrix is a further obligation.
-/

noncomputable section
namespace BC4lean.KKTheory

open Filter
open unitInterval
open scoped Topology

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Rounding a genuine compact difference from the reference preserves genuine
module compactness, by explicit factorization through that difference. -/
theorem spectralGapRoundedProjection_sub_reference_isModuleCompact
    (A : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)))
    (hA : IsSelfAdjoint A) (hCompact : IsModuleCompact (A - standardCountablePairedReferenceProjection)) :
    IsModuleCompact (spectralGapRoundedProjection A - standardCountablePairedReferenceProjection) := by
  rw [spectralGapRoundedProjection_sub_projection A standardCountablePairedReferenceProjection hA
    standardCountablePairedReferenceProjection_isStarProjection]
  exact ((hCompact.comp_left (cfc projectionRoundZeroFactor A)).comp_right
    (1 - standardCountablePairedReferenceProjection)).add
      ((hCompact.comp_left (cfc projectionRoundOneFactor A)).comp_right
        standardCountablePairedReferenceProjection)

/-- The rounded compression has precisely the original reference action on
its whole right coordinate tail. -/
theorem spectralGapRoundedReferenceCompression_right_tail
    (P : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)))
    (hP : IsSelfAdjoint P) (n : ℕ) :
    spectralGapRoundedProjection (standardCountableReferenceCompression P n) *
        (1 - standardCountablePairedCutoff n) =
      standardCountablePairedReferenceProjection * (1 - standardCountablePairedCutoff n) := by
  apply spectralGapRoundedProjection_reference_right_tail _ _ _
    (standardCountableReferenceCompression_isSelfAdjoint P hP n)
    standardCountablePairedReferenceProjection_isStarProjection
    (standardCountableReferenceCompression_right_tail P n)
  have hc := standardCountablePairedCutoff_commutes_reference (B := B) n
  simp only [mul_sub, sub_mul, mul_one, one_mul]
  rw [hc]

/-- Selfadjointness gives the same exact reference action on the left tail. -/
theorem spectralGapRoundedReferenceCompression_left_tail
    (P : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)))
    (hP : IsSelfAdjoint P) (n : ℕ) :
    (1 - standardCountablePairedCutoff n) *
        spectralGapRoundedProjection (standardCountableReferenceCompression P n) =
      (1 - standardCountablePairedCutoff n) * standardCountablePairedReferenceProjection := by
  have hh := congrArg star (spectralGapRoundedReferenceCompression_right_tail P hP n)
  have hC : star (standardCountablePairedCutoff (B := B) n) = standardCountablePairedCutoff n :=
    standardCountablePairedCutoff_adjoint n
  have hQ := (standardCountablePairedReferenceProjection_isStarProjection (B := B)).isSelfAdjoint.star_eq
  have hR : star (spectralGapRoundedProjection (standardCountableReferenceCompression P n)) =
      spectralGapRoundedProjection (standardCountableReferenceCompression P n) :=
    (cfc_predicate projectionRoundCutoff (standardCountableReferenceCompression P n)).star_eq
  simpa only [star_mul, star_sub, star_one, hC, hQ, hR] using hh

/-- The entire rounded reference difference is genuinely supported in the
finite coordinate corner, by its proved zero tails on both sides. -/
theorem spectralGapRoundedReferenceCompression_sub_eq_cutoff
    (P : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)))
    (hP : IsSelfAdjoint P) (n : ℕ) :
    spectralGapRoundedProjection (standardCountableReferenceCompression P n) -
        standardCountablePairedReferenceProjection =
      standardCountablePairedCutoff n *
        (spectralGapRoundedProjection (standardCountableReferenceCompression P n) -
          standardCountablePairedReferenceProjection) * standardCountablePairedCutoff n := by
  have hleft : (1 - standardCountablePairedCutoff n) *
      (spectralGapRoundedProjection (standardCountableReferenceCompression P n) -
        standardCountablePairedReferenceProjection) = 0 := by
    rw [mul_sub, spectralGapRoundedReferenceCompression_left_tail P hP n, sub_self]
  have hright : (spectralGapRoundedProjection (standardCountableReferenceCompression P n) -
      standardCountablePairedReferenceProjection) * (1 - standardCountablePairedCutoff n) = 0 := by
    rw [sub_mul, spectralGapRoundedReferenceCompression_right_tail P hP n, sub_self]
  rw [sub_mul, one_mul] at hleft
  rw [mul_sub, mul_one] at hright
  rw [← sub_eq_zero.mp hleft, ← sub_eq_zero.mp hright]

/-- A genuine compact projection difference admits an actual finite coordinate
compression and a constructed path consisting entirely of projections. -/
theorem exists_standardCountableReferenceProjectionPath
    (P : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)))
    (hP : IsStarProjection P)
    (hCompact : IsModuleCompact (P - standardCountablePairedReferenceProjection)) :
    ∃ n : ℕ, ∃ γ : Path P (spectralGapRoundedProjection (standardCountableReferenceCompression P n)),
      ∀ t : I, IsStarProjection (γ t) := by
  have hNorm := tendsto_iff_norm_sub_tendsto_zero.mp
    (standardCountableReferenceCompression_tendsto P hCompact)
  obtain ⟨n, hn⟩ := (hNorm.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 64))).exists
  refine ⟨n, nearProjectionRoundedPath P (standardCountableReferenceCompression P n) hP
    (standardCountableReferenceCompression_isSelfAdjoint P hP.isSelfAdjoint n) hn, ?_⟩
  intro t
  exact nearProjectionRoundedPath_isStarProjection P (standardCountableReferenceCompression P n) hP
    (standardCountableReferenceCompression_isSelfAdjoint P hP.isSelfAdjoint n) hn t

/-- The actual rounded path consists of relative projections: every projection
on the path retains a genuine compact difference from the fixed reference. -/
theorem exists_standardCountableRelativeProjectionPath
    (P : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)))
    (hP : IsStarProjection P)
    (hCompact : IsModuleCompact (P - standardCountablePairedReferenceProjection)) :
    ∃ n : ℕ, ∃ γ : Path P (spectralGapRoundedProjection (standardCountableReferenceCompression P n)),
      ∀ t : I, IsStarProjection (γ t) ∧
        IsModuleCompact (γ t - standardCountablePairedReferenceProjection) := by
  have hNorm := tendsto_iff_norm_sub_tendsto_zero.mp
    (standardCountableReferenceCompression_tendsto P hCompact)
  obtain ⟨n, hn⟩ := (hNorm.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 64))).exists
  let γ := nearProjectionRoundedPath P (standardCountableReferenceCompression P n) hP
    (standardCountableReferenceCompression_isSelfAdjoint P hP.isSelfAdjoint n) hn
  refine ⟨n, γ, ?_⟩
  intro t
  refine ⟨nearProjectionRoundedPath_isStarProjection P (standardCountableReferenceCompression P n) hP
    (standardCountableReferenceCompression_isSelfAdjoint P hP.isSelfAdjoint n) hn t, ?_⟩
  have hAP : IsModuleCompact (standardCountableReferenceCompression P n - P) := by
    have hh := (standardCountableReferenceCompression_sub_isModuleCompact P hCompact n).sub hCompact
    have heq : (standardCountableReferenceCompression P n - standardCountablePairedReferenceProjection) -
        (P - standardCountablePairedReferenceProjection) = standardCountableReferenceCompression P n - P := by
      abel
    rwa [heq] at hh
  have hAffine : IsModuleCompact (nearProjectionAffine P (standardCountableReferenceCompression P n) t -
      standardCountablePairedReferenceProjection) := by
    have heq : nearProjectionAffine P (standardCountableReferenceCompression P n) t -
        standardCountablePairedReferenceProjection = (P - standardCountablePairedReferenceProjection) +
          (t : ℝ) • (standardCountableReferenceCompression P n - P) := by
      dsimp only [nearProjectionAffine]
      abel
    rw [heq, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact hCompact.add (hAP.smul ((t : ℝ) : ℂ))
  exact spectralGapRoundedProjection_sub_reference_isModuleCompact _
    (nearProjectionAffine_isSelfAdjoint P (standardCountableReferenceCompression P n) hP
      (standardCountableReferenceCompression_isSelfAdjoint P hP.isSelfAdjoint n) t) hAffine

end BC4lean.KKTheory
