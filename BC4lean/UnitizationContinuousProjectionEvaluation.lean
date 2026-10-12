import BC4lean.UnitizationRelativeProjectionK0
import BC4lean.ProjectionHomotopy
import Mathlib.Analysis.CStarAlgebra.ContinuousMap

/-! # Actual finite projection paths by interval coefficient evaluation

Evaluating the coefficient functions in a genuine matrix over the forced
unitization of C(I,B) gives a norm-continuous matrix path over Unitization(B).
Genuine matrix projections remain projections, so the existing norm-homotopy
theorem gives actual Murray--von Neumann equivalence and K0 endpoint equality.
The scalar matrix part is constant along the path. This theorem does not
identify fibres of arbitrary interval Hilbert modules with standard modules.
-/

noncomputable section
namespace BC4lean.KKTheory

open BC4lean.OperatorKTheory
open unitInterval
open scoped Topology CStarAlgebra

local instance continuousProjectionSpectralOrder (A : Type*) [CStarAlgebra A] : PartialOrder A :=
  CStarAlgebra.spectralOrder A
local instance continuousProjectionSpectralOrderedRing (A : Type*) [CStarAlgebra A] : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

variable {B X : Type*} {ι : Type} [NonUnitalCStarAlgebra B]
  [TopologicalSpace X] [CompactSpace X] [Fintype ι] [DecidableEq ι]

/-- Actual nonunital coefficient evaluation, including nonunital B. -/
def continuousCoefficientEvaluation (t : X) : C(X, B) →⋆ₙₐ[ℂ] B where
  toFun f := f t
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

/-- The actual unital evaluation map on forced unitizations. -/
def unitizationContinuousEvaluation (t : X) : Unitization ℂ C(X, B) →⋆ₐ[ℂ] Unitization ℂ B :=
  Unitization.starMap (continuousCoefficientEvaluation t)

@[simp] theorem unitizationContinuousEvaluation_apply (t : X) (a : Unitization ℂ C(X, B)) :
    unitizationContinuousEvaluation t a =
      algebraMap ℂ (Unitization ℂ B) a.fst + (a.snd t : Unitization ℂ B) := rfl

/-- Actual coefficient evaluation is norm-continuous in the interval parameter. -/
theorem continuous_unitizationContinuousEvaluation (a : Unitization ℂ C(X, B)) :
    Continuous (fun t : X => unitizationContinuousEvaluation t a) := by
  simp only [unitizationContinuousEvaluation_apply]
  exact continuous_const.add
    ((map_continuous (Unitization.inrNonUnitalStarAlgHom ℂ B)).comp a.snd.continuous)

/-- The genuine matrix obtained by entrywise coefficient evaluation. -/
def unitizationContinuousMatrixEvaluation (t : X)
    (M : CStarMatrix ι ι (Unitization ℂ C(X, B))) : CStarMatrix ι ι (Unitization ℂ B) :=
  matrixMap (unitizationContinuousEvaluation t) M

@[simp] theorem unitizationContinuousMatrixEvaluation_apply (t : X)
    (M : CStarMatrix ι ι (Unitization ℂ C(X, B))) (i j : ι) :
    unitizationContinuousMatrixEvaluation t M i j = unitizationContinuousEvaluation t (M i j) := rfl

theorem continuous_unitizationContinuousMatrixEvaluation
    (M : CStarMatrix ι ι (Unitization ℂ C(X, B))) :
    Continuous (fun t : X => unitizationContinuousMatrixEvaluation t M) := by
  change Continuous (fun t : X => CStarMatrix.ofMatrix fun i j => unitizationContinuousEvaluation t (M i j))
  exact CStarMatrix.ofMatrixL.continuous.comp
    (continuous_pi fun i => continuous_pi fun j => continuous_unitizationContinuousEvaluation (M i j))

set_option maxHeartbeats 1000000 in
theorem unitizationContinuousMatrixEvaluation_isStarProjection (t : X)
    (M : CStarMatrix ι ι (Unitization ℂ C(X, B))) (hM : IsStarProjection M) :
    IsStarProjection (unitizationContinuousMatrixEvaluation t M) := by
  let φ : CStarMatrix ι ι (Unitization ℂ C(X, B)) →⋆ₐ[ℂ]
      CStarMatrix ι ι (Unitization ℂ B) :=
    matrixMap (A := Unitization ℂ C(X, B)) (B := Unitization ℂ B) (ι := ι)
      (unitizationContinuousEvaluation (B := B) (X := X) t)
  change IsStarProjection (φ M)
  exact IsStarProjection.map
    (A := CStarMatrix ι ι (Unitization ℂ C(X, B)))
    (B := CStarMatrix ι ι (Unitization ℂ B))
    (F := CStarMatrix ι ι (Unitization ℂ C(X, B)) →⋆ₐ[ℂ]
      CStarMatrix ι ι (Unitization ℂ B))
    (x := M) hM φ

/-- The entire scalar matrix is unchanged by coefficient evaluation. -/
@[simp] theorem unitizationScalarMatrix_continuousEvaluation (t : X)
    (M : CStarMatrix ι ι (Unitization ℂ C(X, B))) :
    unitizationScalarMatrix (unitizationContinuousMatrixEvaluation t M) = unitizationScalarMatrix M := by
  ext i j
  simp only [unitizationScalarMatrix_apply, unitizationContinuousMatrixEvaluation_apply,
    unitizationContinuousEvaluation_apply, Unitization.fst_add, Unitization.fst_inr,
    Unitization.algebraMap_eq_inl, Unitization.fst_inl, add_zero]

/-- Every genuine interval coefficient projection gives its actual finite
projection path over Unitization(B), with no spectral-gap assumption. -/
def unitizationProjectionEvaluationPath
    (M : CStarMatrix ι ι (Unitization ℂ C(I, B))) (hM : IsStarProjection M) :
    Path
      (⟨unitizationContinuousMatrixEvaluation (0 : I) M,
        unitizationContinuousMatrixEvaluation_isStarProjection 0 M hM⟩ : MatrixProjection (Unitization ℂ B) ι)
      (⟨unitizationContinuousMatrixEvaluation (1 : I) M,
        unitizationContinuousMatrixEvaluation_isStarProjection 1 M hM⟩ : MatrixProjection (Unitization ℂ B) ι) where
  toFun t := ⟨unitizationContinuousMatrixEvaluation t M,
    unitizationContinuousMatrixEvaluation_isStarProjection t M hM⟩
  continuous_toFun := (continuous_unitizationContinuousMatrixEvaluation M).subtype_mk _
  source' := rfl
  target' := rfl

/-- Genuine interval coefficient projection endpoints have equal unital K0
classes, by the existing actual Murray--von Neumann homotopy theorem. -/
theorem unitizationProjectionEvaluation_k0_endpoints_eq
    (M : CStarMatrix ι ι (Unitization ℂ C(I, B))) (hM : IsStarProjection M) :
    k0Projection (unitizationFiniteProjection (unitizationContinuousMatrixEvaluation (0 : I) M)
      (unitizationContinuousMatrixEvaluation_isStarProjection 0 M hM)) =
    k0Projection (unitizationFiniteProjection (unitizationContinuousMatrixEvaluation (1 : I) M)
      (unitizationContinuousMatrixEvaluation_isStarProjection 1 M hM)) := by
  apply k0Projection_eq_of_equivalent
  apply (rectEquivalent_iff_equivalent _ _).mpr
  exact Projection.equivalent_of_path (unitizationProjectionEvaluationPath M hM)

/-- Evaluate a genuine interval relative pair into the actual nonunital K0
kernel. Its whole scalar matrix equality is preserved by evaluation. -/
def unitizationRelativeProjectionEvaluationK0 (t : X)
    (M N : CStarMatrix ι ι (Unitization ℂ C(X, B)))
    (hM : IsStarProjection M) (hN : IsStarProjection N)
    (hs : unitizationScalarMatrix M = unitizationScalarMatrix N) : OperatorK0 B :=
  unitizationRelativeProjectionK0 (unitizationContinuousMatrixEvaluation t M)
    (unitizationContinuousMatrixEvaluation t N)
    (unitizationContinuousMatrixEvaluation_isStarProjection t M hM)
    (unitizationContinuousMatrixEvaluation_isStarProjection t N hN)
    (by simpa only [unitizationScalarMatrix_continuousEvaluation] using hs)

/-- The actual kernel classes of a genuine finite interval relative pair
agree at both endpoints, by its two constructed finite projection paths. -/
theorem unitizationRelativeProjectionEvaluation_k0_endpoints_eq
    (M N : CStarMatrix ι ι (Unitization ℂ C(I, B)))
    (hM : IsStarProjection M) (hN : IsStarProjection N)
    (hs : unitizationScalarMatrix M = unitizationScalarMatrix N) :
    unitizationRelativeProjectionEvaluationK0 (0 : I) M N hM hN hs =
      unitizationRelativeProjectionEvaluationK0 (1 : I) M N hM hN hs := by
  apply operatorK0Inclusion_injective B
  simp only [unitizationRelativeProjectionEvaluationK0,
    operatorK0Inclusion_unitizationRelativeProjectionK0]
  rw [unitizationProjectionEvaluation_k0_endpoints_eq M hM,
    unitizationProjectionEvaluation_k0_endpoints_eq N hN]

end BC4lean.KKTheory
