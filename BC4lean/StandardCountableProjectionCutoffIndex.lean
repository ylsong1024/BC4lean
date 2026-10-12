import BC4lean.StandardCountableSupportedProjectionPadding

/-! # Genuine cutoff independence of the standard relative-projection index

The rounded projections for two admissible actual cutoffs are joined by the
constructed common-nearness path in the larger coordinate corner. Its actual
finite matrix path has equal existing K₀ endpoint classes. The proved exact
reference padding removes the larger corner on each end. This gives a real
scalar-kernel index independent of the admissible coordinate number.
-/

noncomputable section
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory
open unitInterval
open Filter
open scoped Topology

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

local notation "StdPair" => HilbertModuleSum B (StandardCountableHilbertModule B)
  (StandardCountableHilbertModule B)
local notation "StdEnd" => AdjointableMap B StdPair StdPair

theorem standardCountableRelativeCorner_of_le (R : StdEnd) {n m : ℕ} (hnm : n ≤ m)
    (hCorner : R - standardCountablePairedReferenceProjection =
      standardCountablePairedCutoff n * (R - standardCountablePairedReferenceProjection) *
        standardCountablePairedCutoff n) :
    R - standardCountablePairedReferenceProjection =
      standardCountablePairedCutoff m * (R - standardCountablePairedReferenceProjection) *
        standardCountablePairedCutoff m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  exact standardCountableRelativeCorner_enlarge R n k hCorner

theorem standardCountableSupportedProjectionIndex_of_le (R : StdEnd) (hR : IsStarProjection R)
    (hc : IsModuleCompact (R - standardCountablePairedReferenceProjection))
    {n m : ℕ} (hnm : n ≤ m)
    (hCorner : R - standardCountablePairedReferenceProjection =
      standardCountablePairedCutoff n * (R - standardCountablePairedReferenceProjection) *
        standardCountablePairedCutoff n) :
    standardCountableSupportedProjectionIndex R hR hc m
      (standardCountableRelativeCorner_of_le R hnm hCorner) =
        standardCountableSupportedProjectionIndex R hR hc n hCorner := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  exact standardCountableSupportedProjectionIndex_padding R hR hc n k hCorner

/-- The actual rounded endpoint of an admissible cutoff is a genuine projection. -/
theorem standardCountableRoundedProjection_isStarProjection (P : StdEnd)
    (hP : IsStarProjection P) (n : ℕ)
    (hn : ‖standardCountableReferenceCompression P n - P‖ < 1 / 64) :
    IsStarProjection (spectralGapRoundedProjection (standardCountableReferenceCompression P n)) :=
  spectralGapRoundedProjection_isStarProjection P (standardCountableReferenceCompression P n)
    hP (standardCountableReferenceCompression_isSelfAdjoint P hP.isSelfAdjoint n) hn

/-- The compact reference difference is inherited by the actual rounded endpoint. -/
theorem standardCountableRoundedProjection_compact (P : StdEnd) (hP : IsStarProjection P)
    (hc : IsModuleCompact (P - standardCountablePairedReferenceProjection)) (n : ℕ) :
    IsModuleCompact (spectralGapRoundedProjection (standardCountableReferenceCompression P n) -
      standardCountablePairedReferenceProjection) :=
  spectralGapRoundedProjection_sub_reference_isModuleCompact _
    (standardCountableReferenceCompression_isSelfAdjoint P hP.isSelfAdjoint n)
    (standardCountableReferenceCompression_sub_isModuleCompact P hc n)

/-- The real scalar-kernel index of one admissible actual cutoff. -/
def standardCountableRoundedProjectionIndex (P : StdEnd) (hP : IsStarProjection P)
    (hc : IsModuleCompact (P - standardCountablePairedReferenceProjection)) (n : ℕ)
    (hn : ‖standardCountableReferenceCompression P n - P‖ < 1 / 64) : OperatorK0 B :=
  standardCountableSupportedProjectionIndex
    (spectralGapRoundedProjection (standardCountableReferenceCompression P n))
    (standardCountableRoundedProjection_isStarProjection P hP n hn)
    (standardCountableRoundedProjection_compact P hP hc n) n
    (spectralGapRoundedReferenceCompression_sub_eq_cutoff P hP.isSelfAdjoint n)

/-- A true finite projection path gives equality of supported relative indices
in its one actual common corner. -/
theorem standardCountableSupportedProjectionIndex_path
    (n : ℕ) (R : C(I, StdEnd)) (hR : ∀ t, IsStarProjection (R t))
    (hc : ∀ t, IsModuleCompact (R t - standardCountablePairedReferenceProjection))
    (hCorner : ∀ t, R t - standardCountablePairedReferenceProjection =
      standardCountablePairedCutoff n * (R t - standardCountablePairedReferenceProjection) *
        standardCountablePairedCutoff n) :
    standardCountableSupportedProjectionIndex (R 0) (hR 0) (hc 0) n (hCorner 0) =
      standardCountableSupportedProjectionIndex (R 1) (hR 1) (hc 1) n (hCorner 1) := by
  obtain ⟨M, hM, hs, ho⟩ := exists_standardCountableFixedCornerProjectionFamily n R hR hc hCorner
  have hUnique (t : I) : M t = standardCountableRelativeFiniteMatrix (R t) (hc t) n :=
    standardCountableRelativeFiniteMatrix_unique _ _ _ _ (hs t) (ho t)
  let δ : Path (⟨M 0, hM 0⟩ : MatrixProjection (Unitization ℂ B) (PairedStandardFiniteIndex n))
      ⟨M 1, hM 1⟩ :=
    { toFun := fun t => ⟨M t, hM t⟩
      continuous_toFun := M.continuous.subtype_mk _
      source' := rfl
      target' := rfl }
  have hEqual : k0Projection (unitizationFiniteProjection (M 0) (hM 0)) =
      k0Projection (unitizationFiniteProjection (M 1) (hM 1)) := by
    apply k0Projection_eq_of_equivalent
    apply (rectEquivalent_iff_equivalent _ _).mpr
    exact Projection.equivalent_of_path δ
  have hEndpointClass
      (P Q : CStarMatrix (PairedStandardFiniteIndex n) (PairedStandardFiniteIndex n) (Unitization ℂ B))
      (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hPQ : P = Q) :
      k0Projection (unitizationFiniteProjection P hP) =
        k0Projection (unitizationFiniteProjection Q hQ) := by
    subst Q
    rfl
  have h0 := hEndpointClass (M 0) (standardCountableRelativeFiniteMatrix (R 0) (hc 0) n)
    (hM 0) (standardCountableRelativeFiniteMatrix_isStarProjection (R 0) (hR 0) (hc 0) n
      (standardCountableRelativeCorner_commutes_cutoff n (R 0) (hCorner 0))) (hUnique 0)
  have h1 := hEndpointClass (M 1) (standardCountableRelativeFiniteMatrix (R 1) (hc 1) n)
    (hM 1) (standardCountableRelativeFiniteMatrix_isStarProjection (R 1) (hR 1) (hc 1) n
      (standardCountableRelativeCorner_commutes_cutoff n (R 1) (hCorner 1))) (hUnique 1)
  apply operatorK0Inclusion_injective
  change k0Projection (unitizationFiniteProjection _ _) - k0Projection (unitizationFiniteProjection _ _) =
    k0Projection (unitizationFiniteProjection _ _) - k0Projection (unitizationFiniteProjection _ _)
  exact congrArg (fun z => z - k0Projection (unitizationFiniteProjection
    (pairedStandardFiniteReferenceMatrix (B := B) n)
    (pairedStandardFiniteReferenceMatrix_isStarProjection n))) (h0.symm.trans (hEqual.trans h1))

/-- The index is independent of both actually admissible finite coordinate cutoffs. -/
theorem standardCountableRoundedProjectionIndex_independent (P : StdEnd) (hP : IsStarProjection P)
    (hc : IsModuleCompact (P - standardCountablePairedReferenceProjection)) (n m : ℕ)
    (hn : ‖standardCountableReferenceCompression P n - P‖ < 1 / 64)
    (hm : ‖standardCountableReferenceCompression P m - P‖ < 1 / 64) :
    standardCountableRoundedProjectionIndex P hP hc n hn =
      standardCountableRoundedProjectionIndex P hP hc m hm := by
  let γ := standardCountableCutoffComparisonPath P hP n m hn hm
  have hEq := standardCountableSupportedProjectionIndex_path (max n m)
    (⟨γ, γ.continuous⟩ : C(I, StdEnd))
    (standardCountableCutoffComparisonPath_isStarProjection P hP n m hn hm)
    (standardCountableCutoffComparisonPath_sub_reference_isModuleCompact P hP hc n m hn hm)
    (standardCountableCutoffComparisonPath_sub_eq_common_cutoff P hP n m hn hm)
  have hLeft := standardCountableSupportedProjectionIndex_of_le
    (spectralGapRoundedProjection (standardCountableReferenceCompression P n))
    (standardCountableRoundedProjection_isStarProjection P hP n hn)
    (standardCountableRoundedProjection_compact P hP hc n)
    (le_max_left n m) (spectralGapRoundedReferenceCompression_sub_eq_cutoff P hP.isSelfAdjoint n)
  have hRight := standardCountableSupportedProjectionIndex_of_le
    (spectralGapRoundedProjection (standardCountableReferenceCompression P m))
    (standardCountableRoundedProjection_isStarProjection P hP m hm)
    (standardCountableRoundedProjection_compact P hP hc m)
    (le_max_right n m) (spectralGapRoundedReferenceCompression_sub_eq_cutoff P hP.isSelfAdjoint m)
  have hSource : γ 0 = spectralGapRoundedProjection (standardCountableReferenceCompression P n) := γ.source
  have hTarget : γ 1 = spectralGapRoundedProjection (standardCountableReferenceCompression P m) := γ.target
  simp only [ContinuousMap.coe_mk, hSource, hTarget] at hEq
  exact hLeft.symm.trans (hEq.trans hRight)

/-- Genuine compact convergence supplies an actually admissible cutoff. -/
theorem exists_standardCountableAdmissibleProjectionCutoff (P : StdEnd)
    (hc : IsModuleCompact (P - standardCountablePairedReferenceProjection)) :
    ∃ n : ℕ, ‖standardCountableReferenceCompression P n - P‖ < 1 / 64 :=
  ((tendsto_iff_norm_sub_tendsto_zero.mp (standardCountableReferenceCompression_tendsto P hc)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 64))).exists

/-- The actual coordinate-independent scalar-kernel relative-projection index. -/
def standardCountableRelativeProjectionIndex (P : StdEnd) (hP : IsStarProjection P)
    (hc : IsModuleCompact (P - standardCountablePairedReferenceProjection)) : OperatorK0 B :=
  standardCountableRoundedProjectionIndex P hP hc
    (exists_standardCountableAdmissibleProjectionCutoff P hc).choose
    (exists_standardCountableAdmissibleProjectionCutoff P hc).choose_spec

theorem standardCountableRelativeProjectionIndex_eq_admissible (P : StdEnd) (hP : IsStarProjection P)
    (hc : IsModuleCompact (P - standardCountablePairedReferenceProjection)) (n : ℕ)
    (hn : ‖standardCountableReferenceCompression P n - P‖ < 1 / 64) :
    standardCountableRelativeProjectionIndex P hP hc =
      standardCountableRoundedProjectionIndex P hP hc n hn :=
  standardCountableRoundedProjectionIndex_independent P hP hc _ n _ hn

end BC4lean.KKTheory
