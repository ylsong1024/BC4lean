import BC4lean.FiniteModuleCompactMatrix
import BC4lean.NearProjectionSpectralRounding
import BC4lean.UnitizationRelativeProjectionK0
import BC4lean.ProjectionHomotopy
import BC4lean.FiniteMatrixProjectionIndex

/-! # Genuine relative matrix norm and close-projection K0 agreement

On matrices with zero scalar part, the actual action on B^n is isometric:
the matrix is an actual embedded B-matrix, both the coefficient inclusion and
its standard compact representation are proved isometric. Thus two matrices
with equal full scalar matrices have precisely the norm distance of their
actual represented operators. Nearness gives an actual rounded projection
path and the existing Murray--von Neumann theorem gives their K0 equality.
The unitization action itself is never assumed faithful.
-/

noncomputable section
namespace BC4lean.KKTheory
open unitInterval
open BC4lean.OperatorKTheory

variable {B ι : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype ι] [DecidableEq ι]

omit [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [Fintype ι] [DecidableEq ι] in
/-- The genuine coefficient inclusion on actual matrices is injective. -/
theorem unitizationCoefficientMatrix_injective :
    Function.Injective (unitizationCoefficientMatrix (B := B) (ι := ι)) := by
  intro M N h
  apply CStarMatrix.ext
  intro i j
  have hh := congrArg (fun K : CStarMatrix ι ι (Unitization ℂ B) => K i j) h
  exact congrArg (fun u : Unitization ℂ B => u.snd) hh

/-- The coefficient matrix inclusion is an isometry of actual C*-norms. -/
theorem unitizationCoefficientMatrix_isometry :
    Isometry (unitizationCoefficientMatrix (B := B) (ι := ι)) := by
  change Isometry (CStarMatrix.mapₙₐ (Unitization.inrNonUnitalStarAlgHom ℂ B))
  exact NonUnitalStarAlgHom.isometry _ unitizationCoefficientMatrix_injective

omit [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [Fintype ι] [DecidableEq ι] in
/-- Zero full scalar matrix gives an actual coefficient-matrix lift. -/
theorem unitizationMatrix_exists_coefficient_of_scalar_zero
    (M : CStarMatrix ι ι (Unitization ℂ B)) (hScalar : unitizationScalarMatrix M = 0) :
    ∃ K : CStarMatrix ι ι B, M = unitizationCoefficientMatrix K := by
  let K : CStarMatrix ι ι B := M.map fun a => a.snd
  refine ⟨K, ?_⟩
  apply CStarMatrix.ext
  intro i j
  apply Unitization.ext
  · have h := congrArg (fun N : CStarMatrix ι ι ℂ => N i j) hScalar
    simpa only [unitizationScalarMatrix_apply, CStarMatrix.zero_apply,
      unitizationCoefficientMatrix_apply, Unitization.fst_inr] using h
  · rfl

/-- The represented operator and matrix have the same actual norm on the
zero-scalar ideal, including unital B, B=0 and an empty coordinate set. -/
theorem unitizationMatrix_norm_of_scalar_zero
    (M : CStarMatrix ι ι (Unitization ℂ B)) (hScalar : unitizationScalarMatrix M = 0) :
    ‖unitizedModuleMatrixRepresentation M‖ = ‖M‖ := by
  obtain ⟨K, rfl⟩ := unitizationMatrix_exists_coefficient_of_scalar_zero M hScalar
  rw [unitizedModuleMatrixRepresentation_coefficient]
  have hCoeffZero : unitizationCoefficientMatrix (0 : CStarMatrix ι ι B) = 0 := by
    apply CStarMatrix.ext
    intro i j
    simp only [unitizationCoefficientMatrix_apply, CStarMatrix.zero_apply, Unitization.inr_zero]
  rw [moduleMatrixRepresentation_isometry.norm_map_of_map_zero (map_zero _) K,
    unitizationCoefficientMatrix_isometry.norm_map_of_map_zero hCoeffZero K]

/-- Equal full scalar matrix parts make represented operator distance exact. -/
theorem unitizationMatrix_difference_norm
    (M N : CStarMatrix ι ι (Unitization ℂ B))
    (hScalar : unitizationScalarMatrix M = unitizationScalarMatrix N) :
    ‖unitizedModuleMatrixRepresentation M - unitizedModuleMatrixRepresentation N‖ = ‖M - N‖ := by
  rw [← map_sub]
  apply unitizationMatrix_norm_of_scalar_zero
  rw [unitizationScalarMatrix_sub, hScalar, sub_self]

local instance relativeMatrixNormOrder : PartialOrder (CStarMatrix ι ι (Unitization ℂ B)) :=
  CStarAlgebra.spectralOrder _
local instance relativeMatrixNormStarOrderedRing : StarOrderedRing (CStarMatrix ι ι (Unitization ℂ B)) :=
  CStarAlgebra.spectralOrderedRing _

/-- Actual represented closeness, with full scalar equality, gives a genuine
projection path in the finite unitization matrix algebra. -/
def unitizedCloseProjectionPath
    (p q : MatrixProjection (Unitization ℂ B) ι)
    (hScalar : unitizationScalarMatrix p.val = unitizationScalarMatrix q.val)
    (hclose : ‖unitizedModuleMatrixRepresentation q.val - unitizedModuleMatrixRepresentation p.val‖ < 1 / 64) :
    Path p q := by
  have hNorm : ‖q.val - p.val‖ < 1 / 64 := by
    rwa [unitizationMatrix_difference_norm q.val p.val hScalar.symm] at hclose
  let γ := nearProjectionRoundedPath p.val q.val p.property q.property.isSelfAdjoint hNorm
  refine
    { toFun := fun t => ⟨γ t,
        nearProjectionRoundedPath_isStarProjection p.val q.val p.property q.property.isSelfAdjoint hNorm t⟩
      continuous_toFun := γ.continuous.subtype_mk _
      source' := ?_
      target' := ?_ }
  · apply Subtype.ext
    exact γ.source
  · apply Subtype.ext
    exact γ.target.trans (spectralGapRoundedProjection_projection q.val q.property)

/-- The existing genuine Murray--von Neumann theorem yields actual unital K0
agreement for the proved finite projection path. -/
theorem unitizedCloseProjection_k0_eq
    (p q : MatrixProjection (Unitization ℂ B) ι)
    (hScalar : unitizationScalarMatrix p.val = unitizationScalarMatrix q.val)
    (hclose : ‖unitizedModuleMatrixRepresentation q.val - unitizedModuleMatrixRepresentation p.val‖ < 1 / 64) :
    k0Projection (finiteProjectionOfMatrix p) = k0Projection (finiteProjectionOfMatrix q) := by
  apply k0Projection_eq_of_equivalent
  change RectEquivalent (matrixProjectionToFin p) (matrixProjectionToFin q)
  apply (rectEquivalent_iff_equivalent _ _).mpr
  exact Projection.equivalent_map
    (CStarMatrix.reindexₐ ℂ (Unitization ℂ B) (Fintype.equivFin ι)).toStarAlgHom
    (Projection.equivalent_of_path (unitizedCloseProjectionPath p q hScalar hclose))

/-- On the constructor's original index universe, the same agreement uses the
original finite projection records. -/
theorem unitizedCloseProjection_k0_eq_ofProjection {ι : Type} [Fintype ι] [DecidableEq ι]
    (p q : MatrixProjection (Unitization ℂ B) ι)
    (hScalar : unitizationScalarMatrix p.val = unitizationScalarMatrix q.val)
    (hclose : ‖unitizedModuleMatrixRepresentation q.val - unitizedModuleMatrixRepresentation p.val‖ < 1 / 64) :
    k0Projection (FiniteProjection.ofProjection p) = k0Projection (FiniteProjection.ofProjection q) := by
  simpa only [k0Projection_finiteProjectionOfMatrix] using
    unitizedCloseProjection_k0_eq p q hScalar hclose

end BC4lean.KKTheory
