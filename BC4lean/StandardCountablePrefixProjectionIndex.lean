import BC4lean.StandardCountableRelativeProjectionPathIndex

/-! # The actual index of an exactly supported finite projection

The prescribed paired coordinate inclusion is an adjointable isometry with
range equal to the actual paired cutoff. A whole corner identity determines
the compressed operator. The full scalar matrix and actual operator then
identify the canonical finite coefficient matrix uniquely.
-/

noncomputable section
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
local notation "StdPair" => HilbertModuleSum B (StandardCountableHilbertModule B)
  (StandardCountableHilbertModule B)
local notation "StdEnd" => AdjointableMap B StdPair StdPair

/-- Exact finite support recovers precisely the supplied actual scalar-kernel class. -/
theorem standardCountableRelativeProjectionIndex_prefix_matrix
    (R : StdEnd) (hR : IsStarProjection R)
    (hc : IsModuleCompact (R - standardCountablePairedReferenceProjection)) (n : ℕ)
    (M : CStarMatrix (PairedStandardFiniteIndex n) (PairedStandardFiniteIndex n) (Unitization ℂ B))
    (hM : IsStarProjection M)
    (hs : unitizationScalarMatrix M = unitizationScalarMatrix (pairedStandardFiniteReferenceMatrix (B := B) n))
    (hCornerMatrix : R - standardCountablePairedReferenceProjection =
      ((pairedStandardFiniteInclusion (B := B) n).comp
        (unitizedModuleMatrixRepresentation (B := B) (M - pairedStandardFiniteReferenceMatrix (B := B) n))).comp
          (pairedStandardFiniteInclusion (B := B) n).adjoint) :
    standardCountableRelativeProjectionIndex R hR hc =
      unitizationRelativeProjectionK0 M (pairedStandardFiniteReferenceMatrix n) hM
        (pairedStandardFiniteReferenceMatrix_isStarProjection n) hs := by
  let I := pairedStandardFiniteInclusion (B := B) n
  have hI : I.adjoint.comp I = AdjointableMap.id :=
    pairedStandardFiniteInclusion_adjoint_comp_self n
  have hIf (x : FiniteStandardModule B (PairedStandardFiniteIndex n)) : I.adjoint (I x) = x :=
    congrArg (fun T => T x) hI
  have hCorner : R - standardCountablePairedReferenceProjection =
      standardCountablePairedCutoff n * (R - standardCountablePairedReferenceProjection) *
        standardCountablePairedCutoff n := by
    rw [hCornerMatrix, ← pairedStandardFiniteInclusion_comp_adjoint]
    ext x
    change I (unitizedModuleMatrixRepresentation (M - pairedStandardFiniteReferenceMatrix n)
      (I.adjoint x)) = I (I.adjoint (I
        (unitizedModuleMatrixRepresentation (M - pairedStandardFiniteReferenceMatrix n)
          (I.adjoint (I (I.adjoint x))))))
    rw [hIf, hIf]
  have ho : unitizedModuleMatrixRepresentation M = pairedStandardFiniteCompression n R := by
    apply AdjointableMap.ext
    intro x
    have h := congrArg (fun T => I.adjoint (T (I x))) hCornerMatrix
    simp only [AdjointableMap.coe_sub_apply, AdjointableMap.comp_apply] at h
    change I.adjoint (R (I x) - standardCountablePairedReferenceProjection (I x)) =
      I.adjoint (I (unitizedModuleMatrixRepresentation (M - pairedStandardFiniteReferenceMatrix n)
        (I.adjoint (I x)))) at h
    rw [I.adjoint.toCLM.map_sub, hIf, hIf, map_sub, AdjointableMap.coe_sub_apply] at h
    have hQ := congrArg (fun T => T x) (pairedStandardFiniteCompression_reference (B := B) n)
    change I.adjoint (standardCountablePairedReferenceProjection (I x)) =
      unitizedModuleMatrixRepresentation (pairedStandardFiniteReferenceMatrix n) x at hQ
    change unitizedModuleMatrixRepresentation M x = I.adjoint (R (I x))
    rw [hQ] at h
    exact (sub_left_inj.mp h).symm
  rw [standardCountableRelativeProjectionIndex_supported R hR hc n hCorner]
  have hUnique := standardCountableRelativeFiniteMatrix_unique R hc n M hs ho
  apply operatorK0Inclusion_injective
  change k0Projection (unitizationFiniteProjection _ _) -
      k0Projection (unitizationFiniteProjection _ _) =
    k0Projection (unitizationFiniteProjection M hM) -
      k0Projection (unitizationFiniteProjection (pairedStandardFiniteReferenceMatrix n) _)
  simp only [← hUnique]

end BC4lean.KKTheory
