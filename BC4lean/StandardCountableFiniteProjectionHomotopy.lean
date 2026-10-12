import BC4lean.StandardCountableFiniteProjection
import BC4lean.CompactModuleUniformCutoff
import BC4lean.UnitizationRelativeProjectionK0
import BC4lean.ProjectionHomotopy

/-! # Uniform genuine finite projections from a continuous relative path

A norm-continuous family of actual standard projections with compact reference
difference admits one uniform coordinate cutoff. The spectral gap follows from
the proved norm estimate at every parameter. Continuous CFC rounding and the
isometric actual compact coefficient extraction produce a continuous family
of genuine finite unitization projections with the entire fixed scalar matrix.
The resulting finite projection path has equal existing K0 endpoint classes.
-/

noncomputable section
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory
open Filter
open unitInterval
open scoped Topology

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

local notation "StdPair" => HilbertModuleSum B (StandardCountableHilbertModule B)
  (StandardCountableHilbertModule B)
local notation "StdEnd" => AdjointableMap B StdPair StdPair

/-- One actual coordinate bound approximates the entire continuous compact-relative family. -/
theorem exists_uniform_standardCountableReferenceCompression
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (P : C(X, StdEnd)) (hc : ∀ x, IsModuleCompact (P x - standardCountablePairedReferenceProjection))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ x, ‖standardCountableReferenceCompression (P x) n - P x‖ < ε := by
  have h := continuous_eventually_uniform_moduleSandwich standardCountablePairedCutoff
    norm_standardCountablePairedCutoff_le standardCountablePairedCutoff_adjoint
    standardCountablePairedCutoff_tendsto
    (fun x => P x - standardCountablePairedReferenceProjection)
    (P.continuous.sub continuous_const) hc hε
  obtain ⟨n, hn⟩ := h.exists
  refine ⟨n, ?_⟩
  intro x
  have hEq : standardCountableReferenceCompression (P x) n - P x =
      standardCountablePairedCutoff n * (P x - standardCountablePairedReferenceProjection) *
        standardCountablePairedCutoff n - (P x - standardCountablePairedReferenceProjection) := by
    dsimp only [standardCountableReferenceCompression]
    abel
  rw [hEq]
  exact hn x

/-- Actual finite coordinate compression is a continuous linear operation. -/
theorem continuous_pairedStandardFiniteCompression (n : ℕ) :
    Continuous (pairedStandardFiniteCompression (B := B) n) := by
  let L : StdEnd →L[ℂ]
      AdjointableMap B StdPair (FiniteStandardModule B (PairedStandardFiniteIndex n)) :=
    AdjointableMap.compLeftContinuousLinearMap
    (pairedStandardFiniteInclusion (B := B) n).adjoint
  let R : AdjointableMap B StdPair (FiniteStandardModule B (PairedStandardFiniteIndex n)) →L[ℂ]
      AdjointableMap B (FiniteStandardModule B (PairedStandardFiniteIndex n))
        (FiniteStandardModule B (PairedStandardFiniteIndex n)) :=
    AdjointableMap.compRightContinuousLinearMap
    (pairedStandardFiniteInclusion (B := B) n)
  change Continuous (fun T : StdEnd => R (L T))
  exact R.continuous.comp L.continuous

/-- The fixed continuous rounding function is continuous on the entire
uniformly derived spectral gap family. -/
theorem continuous_spectralGapRoundedReferenceCompression
    {X : Type*} [TopologicalSpace X]
    (P : C(X, StdEnd)) (hP : ∀ x, IsStarProjection (P x)) (n : ℕ)
    (hclose : ∀ x, ‖standardCountableReferenceCompression (P x) n - P x‖ < 1 / 64) :
    Continuous (fun x => spectralGapRoundedProjection (standardCountableReferenceCompression (P x) n)) := by
  have hA : Continuous (fun x => standardCountableReferenceCompression (P x) n) := by
    exact continuous_const.add
      (((continuous_const.mul (P.continuous.sub continuous_const)).mul continuous_const))
  apply (continuousOn_cfc StdEnd (isCompact_Icc : IsCompact (Set.Icc (-2 : ℝ) 2))
    projectionRoundCutoff continuous_projectionRoundCutoff.continuousOn).comp_continuous hA
  intro x
  refine ⟨standardCountableReferenceCompression_isSelfAdjoint (P x) (hP x).isSelfAdjoint n, ?_⟩
  simpa only [nearProjectionAffine_one] using nearProjectionAffine_spectrum_subset
    (P x) (standardCountableReferenceCompression (P x) n) (hP x)
    (standardCountableReferenceCompression_isSelfAdjoint (P x) (hP x).isSelfAdjoint n)
    (hclose x) (1 : I)

set_option maxHeartbeats 800000 in
/-- Genuine continuous finite unitization projections are constructed from the
actual path. Their full scalar matrix is fixed, and their represented action
is exactly the finite compression of the constructed rounded projection. -/
theorem exists_uniform_standardCountableFiniteUnitizationProjection
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (P : C(X, StdEnd)) (hP : ∀ x, IsStarProjection (P x))
    (hc : ∀ x, IsModuleCompact (P x - standardCountablePairedReferenceProjection)) :
    ∃ n : ℕ, ∃ M : C(X, CStarMatrix (PairedStandardFiniteIndex n)
        (PairedStandardFiniteIndex n) (Unitization ℂ B)),
      (∀ x, IsStarProjection (M x)) ∧
      (∀ x, unitizationScalarMatrix (M x) =
        unitizationScalarMatrix (pairedStandardFiniteReferenceMatrix (B := B) n)) ∧
      (∀ x, unitizedModuleMatrixRepresentation (M x) = pairedStandardFiniteCompression n
        (spectralGapRoundedProjection (standardCountableReferenceCompression (P x) n))) := by
  obtain ⟨n, hn⟩ := exists_uniform_standardCountableReferenceCompression P hc
    (by norm_num : (0 : ℝ) < 1 / 64)
  let R : X → StdEnd := fun x =>
    spectralGapRoundedProjection (standardCountableReferenceCompression (P x) n)
  have hR : ∀ x, IsStarProjection (R x) := fun x =>
    spectralGapRoundedProjection_isStarProjection (P x)
      (standardCountableReferenceCompression (P x) n) (hP x)
      (standardCountableReferenceCompression_isSelfAdjoint (P x) (hP x).isSelfAdjoint n) (hn x)
  have hRc : ∀ x, IsModuleCompact (R x - standardCountablePairedReferenceProjection) := fun x =>
    spectralGapRoundedProjection_sub_reference_isModuleCompact _
      (standardCountableReferenceCompression_isSelfAdjoint (P x) (hP x).isSelfAdjoint n)
      (standardCountableReferenceCompression_sub_isModuleCompact (P x) (hc x) n)
  have hContinuousR : Continuous R := continuous_spectralGapRoundedReferenceCompression P hP n hn
  let K : X → AdjointableMap B (FiniteStandardModule B (PairedStandardFiniteIndex n))
      (FiniteStandardModule B (PairedStandardFiniteIndex n)) :=
    fun x => pairedStandardFiniteCompression (B := B) n
      (R x - standardCountablePairedReferenceProjection)
  have hK : ∀ x, IsModuleCompact (K x) := fun x =>
    ((hRc x).comp_left (pairedStandardFiniteInclusion (B := B) n).adjoint).comp_right
      (pairedStandardFiniteInclusion (B := B) n)
  have hContinuousK : Continuous K := (continuous_pairedStandardFiniteCompression n).comp
    (hContinuousR.sub continuous_const)
  let coefficients : X → CStarMatrix (PairedStandardFiniteIndex n)
      (PairedStandardFiniteIndex n) B := fun x =>
    finiteModuleCompactMatrix (B := B) (ι := PairedStandardFiniteIndex n) (K x) (hK x)
  have hContinuousCoefficients : Continuous coefficients :=
    continuous_finiteModuleCompactMatrix K hK hContinuousK
  let M : C(X, CStarMatrix (PairedStandardFiniteIndex n)
      (PairedStandardFiniteIndex n) (Unitization ℂ B)) :=
    ⟨fun x => pairedStandardFiniteReferenceMatrix n + unitizationCoefficientMatrix (coefficients x),
      continuous_const.add (continuous_unitizationCoefficientMatrix.comp hContinuousCoefficients)⟩
  have hScalar (x : X) : unitizationScalarMatrix (M x) =
      unitizationScalarMatrix (pairedStandardFiniteReferenceMatrix (B := B) n) := by
    simp only [M, ContinuousMap.coe_mk, unitizationScalarMatrix_add,
      unitizationScalarMatrix_coefficient, add_zero]
  have hOperator (x : X) :
      unitizedModuleMatrixRepresentation (B := B) (ι := PairedStandardFiniteIndex n) (M x) =
        pairedStandardFiniteCompression (B := B) n (R x) := by
    have hMx : M x = pairedStandardFiniteReferenceMatrix (B := B) n +
        unitizationCoefficientMatrix (B := B) (ι := PairedStandardFiniteIndex n) (coefficients x) := rfl
    rw [hMx]
    rw [map_add, unitizedModuleMatrixRepresentation_coefficient,
      moduleMatrixRepresentation_finiteModuleCompactMatrix, ← pairedStandardFiniteCompression_reference]
    apply AdjointableMap.ext
    intro v
    simp only [K, pairedStandardFiniteCompression, AdjointableMap.comp_apply,
      AdjointableMap.coe_add_apply, AdjointableMap.coe_sub_apply, map_sub]
    abel
  have hM (x : X) : IsStarProjection (M x) := by
    have hScalarProjection : IsStarProjection (unitizationScalarMatrix (M x)) :=
      (hScalar x).symm ▸ pairedStandardFiniteReferenceScalarMatrix_isStarProjection (B := B) n
    have hFiniteProjection : IsStarProjection (pairedStandardFiniteCompression (B := B) n (R x)) :=
      pairedStandardFiniteCompression_isStarProjection (B := B) n (R x) (hR x)
        (spectralGapRoundedReferenceCompression_commutes_cutoff (P x) (hP x).isSelfAdjoint n)
    have hOperatorProjection : IsStarProjection
        (unitizedModuleMatrixRepresentation (B := B) (ι := PairedStandardFiniteIndex n) (M x)) :=
      (hOperator x).symm ▸ hFiniteProjection
    exact unitizationMatrix_isStarProjection_of_scalar_and_operator
      (B := B) (ι := PairedStandardFiniteIndex n) (M x) hScalarProjection hOperatorProjection
  exact ⟨n, M, hM, hScalar, hOperator⟩

/-- The derived finite matrix family gives a true finite projection path and
therefore equality of the existing K0 endpoint classes. -/
theorem exists_uniform_standardCountableFiniteProjectionPath
    (P : C(I, StdEnd)) (hP : ∀ t, IsStarProjection (P t))
    (hc : ∀ t, IsModuleCompact (P t - standardCountablePairedReferenceProjection)) :
    ∃ n : ℕ, ∃ M : C(I, CStarMatrix (PairedStandardFiniteIndex n)
        (PairedStandardFiniteIndex n) (Unitization ℂ B)),
    ∃ hM : ∀ t, IsStarProjection (M t),
      (∀ t, unitizationScalarMatrix (M t) =
        unitizationScalarMatrix (pairedStandardFiniteReferenceMatrix (B := B) n)) ∧
      k0Projection (unitizationFiniteProjection (M 0) (hM 0)) =
        k0Projection (unitizationFiniteProjection (M 1) (hM 1)) := by
  obtain ⟨n, M, hM, hScalar, _⟩ :=
    exists_uniform_standardCountableFiniteUnitizationProjection P hP hc
  refine ⟨n, M, hM, hScalar, ?_⟩
  let γ : Path (⟨M 0, hM 0⟩ : MatrixProjection (Unitization ℂ B) (PairedStandardFiniteIndex n))
      ⟨M 1, hM 1⟩ :=
    { toFun := fun t => ⟨M t, hM t⟩
      continuous_toFun := M.continuous.subtype_mk _
      source' := rfl
      target' := rfl }
  apply k0Projection_eq_of_equivalent
  apply (rectEquivalent_iff_equivalent _ _).mpr
  exact Projection.equivalent_of_path γ

end BC4lean.KKTheory
