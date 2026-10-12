import BC4lean.StandardCountableProjectionCutoffIndex

/-! # Actual norm-path invariance of the standard relative-projection index

The actual compact image of a continuous relative projection family supplies
one uniform coordinate cutoff. Continuous CFC produces a genuine projection
path in that one corner. Its proved finite matrix path gives equality of the
existing K₀ endpoint classes, and actual cutoff independence identifies these
with the previously constructed scalar-kernel index.
-/

noncomputable section
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory
open unitInterval

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

local notation "StdPair" => HilbertModuleSum B (StandardCountableHilbertModule B)
  (StandardCountableHilbertModule B)
local notation "StdEnd" => AdjointableMap B StdPair StdPair

/-- An actual continuous relative-projection path preserves the actual index. -/
theorem standardCountableRelativeProjectionIndex_path
    (P : C(I, StdEnd)) (hP : ∀ t, IsStarProjection (P t))
    (hc : ∀ t, IsModuleCompact (P t - standardCountablePairedReferenceProjection)) :
    standardCountableRelativeProjectionIndex (P 0) (hP 0) (hc 0) =
      standardCountableRelativeProjectionIndex (P 1) (hP 1) (hc 1) := by
  obtain ⟨n, hn⟩ := exists_uniform_standardCountableReferenceCompression P hc
    (by norm_num : (0 : ℝ) < 1 / 64)
  let R : C(I, StdEnd) :=
    ⟨fun t => spectralGapRoundedProjection (standardCountableReferenceCompression (P t) n),
      continuous_spectralGapRoundedReferenceCompression P hP n hn⟩
  have hR (t : I) : IsStarProjection (R t) :=
    standardCountableRoundedProjection_isStarProjection (P t) (hP t) n (hn t)
  have hRc (t : I) : IsModuleCompact (R t - standardCountablePairedReferenceProjection) :=
    standardCountableRoundedProjection_compact (P t) (hP t) (hc t) n
  have hCorner (t : I) : R t - standardCountablePairedReferenceProjection =
      standardCountablePairedCutoff n * (R t - standardCountablePairedReferenceProjection) *
        standardCountablePairedCutoff n :=
    spectralGapRoundedReferenceCompression_sub_eq_cutoff (P t) (hP t).isSelfAdjoint n
  rw [standardCountableRelativeProjectionIndex_eq_admissible (P 0) (hP 0) (hc 0) n (hn 0),
    standardCountableRelativeProjectionIndex_eq_admissible (P 1) (hP 1) (hc 1) n (hn 1)]
  exact standardCountableSupportedProjectionIndex_path n R hR hRc hCorner

/-- On a projection already supported in the actual corner, compression and
rounding retain that whole projection exactly. -/
theorem standardCountableRelativeProjectionIndex_supported (R : StdEnd) (hR : IsStarProjection R)
    (hc : IsModuleCompact (R - standardCountablePairedReferenceProjection)) (n : ℕ)
    (hCorner : R - standardCountablePairedReferenceProjection =
      standardCountablePairedCutoff n * (R - standardCountablePairedReferenceProjection) *
        standardCountablePairedCutoff n) :
    standardCountableRelativeProjectionIndex R hR hc =
      standardCountableSupportedProjectionIndex R hR hc n hCorner := by
  have hCompression : standardCountableReferenceCompression R n = R := by
    dsimp only [standardCountableReferenceCompression]
    rw [← hCorner]
    abel
  have hn : ‖standardCountableReferenceCompression R n - R‖ < 1 / 64 := by
    rw [hCompression, sub_self, norm_zero]
    norm_num
  rw [standardCountableRelativeProjectionIndex_eq_admissible R hR hc n hn]
  unfold standardCountableRoundedProjectionIndex
  simp only [hCompression, spectralGapRoundedProjection_projection R hR]

/-- The exact reference projection has zero index without any compactness
assumption on the reference projection itself. -/
@[simp] theorem standardCountableRelativeProjectionIndex_reference :
    standardCountableRelativeProjectionIndex
      (standardCountablePairedReferenceProjection (B := B))
      standardCountablePairedReferenceProjection_isStarProjection
      (by rw [sub_self]; exact IsModuleCompact.zero) = 0 := by
  have hCorner : standardCountablePairedReferenceProjection (B := B) -
      standardCountablePairedReferenceProjection =
      standardCountablePairedCutoff 0 *
        (standardCountablePairedReferenceProjection - standardCountablePairedReferenceProjection) *
          standardCountablePairedCutoff 0 := by rw [sub_self, mul_zero, zero_mul]
  rw [standardCountableRelativeProjectionIndex_supported _ _ _ 0 hCorner]
  apply operatorK0Inclusion_injective
  have hMatrix : standardCountableRelativeFiniteMatrix
      (standardCountablePairedReferenceProjection (B := B))
      (by rw [sub_self]; exact IsModuleCompact.zero) 0 = pairedStandardFiniteReferenceMatrix 0 := by
    apply unitizationMatrix_eq_of_scalar_and_operator_eq
    · exact standardCountableRelativeFiniteMatrix_scalar _ _ _
    · rw [standardCountableRelativeFiniteMatrix_operator, pairedStandardFiniteCompression_reference]
  change k0Projection (unitizationFiniteProjection _ _) -
    k0Projection (unitizationFiniteProjection _ _) = 0
  have hEndpointClass
      (P Q : CStarMatrix (PairedStandardFiniteIndex 0) (PairedStandardFiniteIndex 0) (Unitization ℂ B))
      (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hPQ : P = Q) :
      k0Projection (unitizationFiniteProjection P hP) =
        k0Projection (unitizationFiniteProjection Q hQ) := by
    subst Q
    rfl
  have hClass := hEndpointClass
    (standardCountableRelativeFiniteMatrix (standardCountablePairedReferenceProjection (B := B))
      (by rw [sub_self]; exact IsModuleCompact.zero) 0)
    (pairedStandardFiniteReferenceMatrix (B := B) 0)
    (standardCountableRelativeFiniteMatrix_isStarProjection
      (standardCountablePairedReferenceProjection (B := B))
      standardCountablePairedReferenceProjection_isStarProjection
      (by rw [sub_self]; exact IsModuleCompact.zero) 0
      (standardCountableRelativeCorner_commutes_cutoff 0 _ hCorner))
    (pairedStandardFiniteReferenceMatrix_isStarProjection 0) hMatrix
  exact sub_eq_zero.mpr hClass

end BC4lean.KKTheory
