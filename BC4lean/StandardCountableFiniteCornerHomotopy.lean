import BC4lean.StandardCountableFiniteProjectionHomotopy
import BC4lean.StandardCountableCutoffComparison

/-! # Genuine finite matrix paths from an actual fixed coordinate corner

An actual projection family whose compact reference difference is supported
in one coordinate corner compresses to a continuous finite unitization
projection family. Commutation is derived from the corner equation. Both the
represented operator and the full scalar matrix are retained, so reflection
does not require faithful unitization action. Applied to the constructed
two-cutoff comparison, this gives an actual finite projection path in the
common larger corner and equality of its existing K0 endpoint classes.
-/

noncomputable section
namespace BC4lean.KKTheory
open unitInterval
open BC4lean.OperatorKTheory

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
local notation "StdPair" => HilbertModuleSum B (StandardCountableHilbertModule B)
  (StandardCountableHilbertModule B)
local notation "StdEnd" => AdjointableMap B StdPair StdPair

/-- The actual relative corner equation forces cutoff commutation. -/
theorem standardCountableRelativeCorner_commutes_cutoff (n : ℕ) (R : StdEnd)
    (hCorner : R - standardCountablePairedReferenceProjection = standardCountablePairedCutoff n *
      (R - standardCountablePairedReferenceProjection) * standardCountablePairedCutoff n) :
    standardCountablePairedCutoff n * R = R * standardCountablePairedCutoff n := by
  let C := standardCountablePairedCutoff (B := B) n
  let K := R - standardCountablePairedReferenceProjection
  have hC : C * C = C := standardCountablePairedCutoff_mul_self n
  have hK : K = C * K * C := hCorner
  have hLeft : C * K = K := by
    calc
      C * K = C * (C * K * C) := congrArg (fun x => C * x) hK
      _ = (C * C) * K * C := by simp only [mul_assoc]
      _ = C * K * C := by rw [hC]
      _ = K := hK.symm
  have hRight : K * C = K := by
    calc
      K * C = (C * K * C) * C := congrArg (fun x => x * C) hK
      _ = C * K * (C * C) := by rw [mul_assoc]
      _ = C * K * C := by rw [hC]
      _ = K := hK.symm
  have hR : R = standardCountablePairedReferenceProjection + K := by dsimp only [K]; abel
  change C * R = R * C
  rw [hR, mul_add, add_mul, hLeft, hRight]
  exact congrArg (fun x => x + K) (standardCountablePairedCutoff_commutes_reference n)

/-- Pointwise reconstruction from the same actual compact corner coefficients.
The scalar reference and genuine coefficient extraction are both retained. -/
private theorem pairedStandardFixedCornerCoefficients_reconstruct
    (n : ℕ) (R : StdEnd)
    (hK : IsModuleCompact (pairedStandardFiniteCompression (B := B) n
      (R - standardCountablePairedReferenceProjection))) :
    unitizedModuleMatrixRepresentation (B := B) (ι := PairedStandardFiniteIndex n)
      (pairedStandardFiniteReferenceMatrix (B := B) n +
        unitizationCoefficientMatrix (B := B) (ι := PairedStandardFiniteIndex n)
          (finiteModuleCompactMatrix (B := B) (ι := PairedStandardFiniteIndex n)
            (pairedStandardFiniteCompression (B := B) n
              (R - standardCountablePairedReferenceProjection)) hK)) =
      pairedStandardFiniteCompression (B := B) n R := by
  rw [map_add (unitizedModuleMatrixRepresentation (B := B) (ι := PairedStandardFiniteIndex n)),
    unitizedModuleMatrixRepresentation_coefficient (B := B) (ι := PairedStandardFiniteIndex n),
    moduleMatrixRepresentation_finiteModuleCompactMatrix (B := B) (ι := PairedStandardFiniteIndex n),
    ← pairedStandardFiniteCompression_reference (B := B) n]
  apply AdjointableMap.ext
  intro v
  simp only [pairedStandardFiniteCompression, AdjointableMap.comp_apply,
    AdjointableMap.coe_add_apply, AdjointableMap.coe_sub_apply, map_sub]
  abel

/-- Actual continuous compact coefficient extraction constructs genuine
unitization projections in the fixed corner, with the whole scalar reference. -/
theorem exists_standardCountableFixedCornerProjectionFamily
    {X : Type*} [TopologicalSpace X] (n : ℕ)
    (R : C(X, StdEnd)) (hR : ∀ x, IsStarProjection (R x))
    (hc : ∀ x, IsModuleCompact (R x - standardCountablePairedReferenceProjection))
    (hCorner : ∀ x, R x - standardCountablePairedReferenceProjection =
      standardCountablePairedCutoff n * (R x - standardCountablePairedReferenceProjection) *
        standardCountablePairedCutoff n) :
    ∃ M : C(X, CStarMatrix (PairedStandardFiniteIndex n) (PairedStandardFiniteIndex n) (Unitization ℂ B)),
      (∀ x, IsStarProjection (M x)) ∧
      (∀ x, unitizationScalarMatrix (M x) = unitizationScalarMatrix (pairedStandardFiniteReferenceMatrix (B := B) n)) ∧
      (∀ x, unitizedModuleMatrixRepresentation (M x) = pairedStandardFiniteCompression n (R x)) := by
  let K : X → AdjointableMap B (FiniteStandardModule B (PairedStandardFiniteIndex n))
      (FiniteStandardModule B (PairedStandardFiniteIndex n)) := fun x =>
    pairedStandardFiniteCompression (B := B) n (R x - standardCountablePairedReferenceProjection)
  have hK : ∀ x, IsModuleCompact (K x) := fun x =>
    ((hc x).comp_left (pairedStandardFiniteInclusion n).adjoint).comp_right (pairedStandardFiniteInclusion n)
  have hContinuousK : Continuous K := (continuous_pairedStandardFiniteCompression n).comp
    (R.continuous.sub continuous_const)
  let coefficients : X → CStarMatrix (PairedStandardFiniteIndex n)
      (PairedStandardFiniteIndex n) B := fun x =>
    finiteModuleCompactMatrix (B := B) (ι := PairedStandardFiniteIndex n) (K x) (hK x)
  have hContinuousCoefficients : Continuous coefficients :=
    continuous_finiteModuleCompactMatrix K hK hContinuousK
  let M : C(X, CStarMatrix (PairedStandardFiniteIndex n) (PairedStandardFiniteIndex n) (Unitization ℂ B)) :=
    ⟨fun x => pairedStandardFiniteReferenceMatrix n + unitizationCoefficientMatrix (coefficients x),
      continuous_const.add (continuous_unitizationCoefficientMatrix.comp hContinuousCoefficients)⟩
  have hScalar (x : X) : unitizationScalarMatrix (M x) =
      unitizationScalarMatrix (pairedStandardFiniteReferenceMatrix (B := B) n) := by
    simp only [M, ContinuousMap.coe_mk, unitizationScalarMatrix_add, unitizationScalarMatrix_coefficient, add_zero]
  have hOperator (x : X) :
      unitizedModuleMatrixRepresentation (B := B) (ι := PairedStandardFiniteIndex n) (M x) =
        pairedStandardFiniteCompression (B := B) n (R x) := by
    exact pairedStandardFixedCornerCoefficients_reconstruct n (R x) (hK x)
  refine ⟨M, ?_, hScalar, hOperator⟩
  intro x
  apply unitizationMatrix_isStarProjection_of_scalar_and_operator
  · rw [hScalar x]
    exact pairedStandardFiniteReferenceScalarMatrix_isStarProjection n
  · rw [hOperator x]
    exact pairedStandardFiniteCompression_isStarProjection n (R x) (hR x)
      (standardCountableRelativeCorner_commutes_cutoff n (R x) (hCorner x))

/-- The constructed two-cutoff comparison has a genuine finite unitization
projection path in its actual common corner, with equal K0 endpoint classes. -/
theorem exists_standardCountableCutoffComparisonFiniteProjectionPath
    (P : StdEnd) (hP : IsStarProjection P)
    (hc : IsModuleCompact (P - standardCountablePairedReferenceProjection)) (n m : ℕ)
    (hn : ‖standardCountableReferenceCompression P n - P‖ < 1 / 64)
    (hm : ‖standardCountableReferenceCompression P m - P‖ < 1 / 64) :
    ∃ M : C(I, CStarMatrix (PairedStandardFiniteIndex (max n m))
        (PairedStandardFiniteIndex (max n m)) (Unitization ℂ B)),
    ∃ hM : ∀ t, IsStarProjection (M t),
      (∀ t, unitizationScalarMatrix (M t) = unitizationScalarMatrix (pairedStandardFiniteReferenceMatrix (B := B) (max n m))) ∧
      (∀ t, unitizedModuleMatrixRepresentation (M t) = pairedStandardFiniteCompression (max n m)
        (standardCountableCutoffComparisonPath P hP n m hn hm t)) ∧
      k0Projection (unitizationFiniteProjection (M 0) (hM 0)) =
        k0Projection (unitizationFiniteProjection (M 1) (hM 1)) := by
  let γ := standardCountableCutoffComparisonPath P hP n m hn hm
  obtain ⟨M, hM, hs, ho⟩ := exists_standardCountableFixedCornerProjectionFamily (max n m)
    (⟨γ, γ.continuous⟩ : C(I, StdEnd))
    (standardCountableCutoffComparisonPath_isStarProjection P hP n m hn hm)
    (standardCountableCutoffComparisonPath_sub_reference_isModuleCompact P hP hc n m hn hm)
    (standardCountableCutoffComparisonPath_sub_eq_common_cutoff P hP n m hn hm)
  refine ⟨M, hM, hs, ho, ?_⟩
  let δ : Path (⟨M 0, hM 0⟩ : MatrixProjection (Unitization ℂ B) (PairedStandardFiniteIndex (max n m)))
      ⟨M 1, hM 1⟩ :=
    { toFun := fun t => ⟨M t, hM t⟩
      continuous_toFun := M.continuous.subtype_mk _
      source' := rfl
      target' := rfl }
  apply k0Projection_eq_of_equivalent
  apply (rectEquivalent_iff_equivalent _ _).mpr
  exact Projection.equivalent_of_path δ

end BC4lean.KKTheory
