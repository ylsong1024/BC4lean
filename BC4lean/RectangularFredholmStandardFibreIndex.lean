import BC4lean.RectangularFredholmProjectionIndex
import BC4lean.StandardCountableRelativeProjectionFibreIndex
import BC4lean.StandardCountableHilbertModuleFibre

/-! # Actual standard rectangular index on completed coefficient fibres

The genuine standard fibre homomorphism preserves the rectangular adjoint
square and the defined normalization weight. Positive defect square roots
and whole Julia projections evaluate through the actual paired unitary.
The one global finite corner therefore proves equality of the genuine
standard rectangular indices on interval endpoints.
-/

noncomputable section
namespace BC4lean.KKTheory
open unitInterval
open scoped CStarAlgebra

variable {B X : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X]
local instance rectangularFibreSpectralOrder (A : Type*) [CStarAlgebra A] : PartialOrder A :=
  CStarAlgebra.spectralOrder A
local instance rectangularFibreSpectralOrderedRing (A : Type*) [CStarAlgebra A] : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

local notation "Std" B => StandardCountableHilbertModule B
local notation "StdOp" B => AdjointableMap B (Std B) (Std B)

/-- Functional calculus of the actual adjoint square evaluates exactly. -/
theorem standardCountableFibreOperatorHom_fredholmNormalizer (t : X) (T : StdOp C(X, B)) :
    standardCountableFibreOperatorHom t (globalFredholmNormalizer T) =
      globalFredholmNormalizer (standardCountableFibreOperatorHom t T) := by
  have hEval : Continuous (standardCountableFibreOperatorHom (B := B) t) :=
    AddMonoidHomClass.continuous_of_bound (standardCountableFibreOperatorHom (B := B) t) 1
      (fun S => by simpa only [one_mul] using standardCountableFibreOperatorHom_norm_le t S)
  unfold globalFredholmNormalizer
  rw [(standardCountableFibreOperatorHom t).map_cfc fredholmNormWeight _
    continuous_fredholmNormWeight.continuousOn
    hEval
    (rectangular_adjoint_squares_nonneg T).2.isSelfAdjoint
    ((rectangular_adjoint_squares_nonneg T).2.isSelfAdjoint.map (standardCountableFibreOperatorHom t))]
  change cfc fredholmNormWeight
    (standardCountableFibreOperatorHom t (star T * T)) = _
  rw [map_mul, map_star]
  rfl

/-- The actual globally defined contraction evaluates exactly. -/
theorem standardCountableFibreOperatorHom_fredholmNormalization (t : X) (T : StdOp C(X, B)) :
    standardCountableFibreOperatorHom t (globalFredholmNormalization T) =
      globalFredholmNormalization (standardCountableFibreOperatorHom t T) := by
  change standardCountableFibreOperatorHom t (T * globalFredholmNormalizer T) = _
  rw [map_mul, standardCountableFibreOperatorHom_fredholmNormalizer]
  rfl

/-- The actual positive source defect root evaluates under the genuine unital hom. -/
theorem standardCountableFibreOperatorHom_juliaSourceDefect (t : X)
    (T : StdOp C(X, B)) (hT : ‖T‖ ≤ 1) :
    standardCountableFibreOperatorHom t (juliaSourceDefect T) =
      juliaSourceDefect (standardCountableFibreOperatorHom t T) := by
  have hEval : Continuous (standardCountableFibreOperatorHom (B := B) t) :=
    AddMonoidHomClass.continuous_of_bound (standardCountableFibreOperatorHom (B := B) t) 1
      (fun S => by simpa only [one_mul] using standardCountableFibreOperatorHom_norm_le t S)
  have hLocal : ‖standardCountableFibreOperatorHom t T‖ ≤ 1 :=
    (standardCountableFibreOperatorHom_norm_le t T).trans hT
  unfold juliaSourceDefect
  rw [CFC.sqrt_eq_cfc, CFC.sqrt_eq_cfc]
  rw [(standardCountableFibreOperatorHom t).map_cfc (R := NNReal) NNReal.sqrt _
    NNReal.continuous_sqrt.continuousOn
    hEval
    (one_sub_adjoint_comp_self_nonneg T hT)
    (by
      change 0 ≤ standardCountableFibreOperatorHom t (1 - star T * T)
      rw [map_sub, map_one, map_mul, map_star]
      exact one_sub_adjoint_comp_self_nonneg _ hLocal)]
  change cfc NNReal.sqrt (standardCountableFibreOperatorHom t (1 - star T * T)) = _
  rw [map_sub, map_one, map_mul, map_star]
  rfl

set_option maxHeartbeats 600000 in
/-- Evaluate every whole Julia projection vector through the paired evaluation. -/
theorem pairedStandardCoefficientEvaluation_juliaProjection (t : X)
    (T : StdOp C(X, B)) (hT : ‖T‖ ≤ 1) (x : PairedStandardModule C(X, B)) :
    pairedStandardCoefficientEvaluation t (juliaFredholmProjection T x) =
      juliaFredholmProjection (standardCountableFibreOperatorHom t T)
        (pairedStandardCoefficientEvaluation t x) := by
  have hDefect : standardCountableFibreOperatorHom (B := B) (X := X) t (juliaSourceDefect T) =
      juliaSourceDefect (standardCountableFibreOperatorHom (B := B) (X := X) t T) :=
    standardCountableFibreOperatorHom_juliaSourceDefect (B := B) (X := X) t T hT
  simp only [juliaFredholmProjection, AdjointableMap.comp_apply, juliaFredholmColumn_apply,
    juliaFredholmColumn_adjoint_apply, pairedStandardCoefficientEvaluation_apply,
    sumMk_fst, sumMk_snd]
  rw [← standardCountableFibreOperatorHom_evaluation t T,
    ← standardCountableFibreOperatorHom_evaluation t (juliaSourceDefect T),
    standardCountableFibreOperatorHom_juliaSourceDefect t T hT]
  have hAdjoint : standardCountableFibreOperatorHom (B := B) t T.adjoint =
      (standardCountableFibreOperatorHom (B := B) t T).adjoint := by
    simpa only [AdjointableMap.star_eq_adjoint] using
      map_star (standardCountableFibreOperatorHom (B := B) t) T
  congr 1
  all_goals
    rw [map_add,
      ← standardCountableFibreOperatorHom_evaluation (B := B) (X := X) t (juliaSourceDefect T),
      ← standardCountableFibreOperatorHom_evaluation (B := B) (X := X) t T.adjoint,
      hDefect, hAdjoint]

/-- The actual paired endomorphism hom evaluates the whole Julia projection. -/
theorem pairedStandardFibreOperatorHom_juliaProjection (t : X)
    (T : StdOp C(X, B)) (hT : ‖T‖ ≤ 1) :
    pairedStandardFibreOperatorHom t (juliaFredholmProjection T) =
      juliaFredholmProjection (standardCountableFibreOperatorHom t T) := by
  apply AdjointableMap.ext
  intro x
  rw [← pairedStandardCoefficientEvaluation_constant t x,
    pairedStandardFibreOperatorHom_evaluation, pairedStandardCoefficientEvaluation_juliaProjection t T hT]

@[simp] theorem pairedStandardFibreOperatorHom_normalizedJuliaProjection (t : X)
    (T : StdOp C(X, B)) :
    pairedStandardFibreOperatorHom t (standardNormalizedFredholmJuliaProjection T) =
      standardNormalizedFredholmJuliaProjection (standardCountableFibreOperatorHom t T) := by
  unfold standardNormalizedFredholmJuliaProjection
  rw [pairedStandardFibreOperatorHom_juliaProjection t _ (norm_globalFredholmNormalization_le T),
    standardCountableFibreOperatorHom_fredholmNormalization]

theorem standardCountableFibreFredholm_source_defect (t : X) (T : StdOp C(X, B))
    (hs : IsModuleCompact (1 - T.adjoint.comp T)) :
    IsModuleCompact (1 - (standardCountableFibreOperatorHom t T).adjoint.comp
      (standardCountableFibreOperatorHom t T)) := by
  change IsModuleCompact (1 - star (standardCountableFibreOperatorHom t T) *
    standardCountableFibreOperatorHom t T)
  have h := standardCountableFibreOperatorHom_isModuleCompact t hs
  change IsModuleCompact (standardCountableFibreOperatorHom t (1 - star T * T)) at h
  simpa only [map_sub, map_one, map_mul, map_star] using h

theorem standardCountableFibreFredholm_target_defect (t : X) (T : StdOp C(X, B))
    (ht : IsModuleCompact (T.comp T.adjoint - 1)) :
    IsModuleCompact ((standardCountableFibreOperatorHom t T).comp
      (standardCountableFibreOperatorHom t T).adjoint - 1) := by
  change IsModuleCompact (standardCountableFibreOperatorHom t T *
    star (standardCountableFibreOperatorHom t T) - 1)
  have h := standardCountableFibreOperatorHom_isModuleCompact t ht
  change IsModuleCompact (standardCountableFibreOperatorHom t (T * star T - 1)) at h
  simpa only [map_sub, map_one, map_mul, map_star] using h

/-- The genuine rectangular indices of an actual standard interval Fredholm
operator agree at the two completed fibres. No operator-family assumption. -/
theorem standardNormalizedRectangularFredholmIndex_fibre_endpoints
    (T : StdOp C(I, B)) (hs : IsModuleCompact (1 - T.adjoint.comp T))
    (ht : IsModuleCompact (T.comp T.adjoint - 1)) :
    standardNormalizedRectangularFredholmIndex (standardCountableFibreOperatorHom (0 : I) T)
        (standardCountableFibreFredholm_source_defect 0 T hs)
        (standardCountableFibreFredholm_target_defect 0 T ht) =
      standardNormalizedRectangularFredholmIndex (standardCountableFibreOperatorHom (1 : I) T)
        (standardCountableFibreFredholm_source_defect 1 T hs)
        (standardCountableFibreFredholm_target_defect 1 T ht) := by
  have h := standardCountableRelativeProjectionIndex_fibre_endpoints
    (standardNormalizedFredholmJuliaProjection T)
    (standardNormalizedFredholmJuliaProjection_isStarProjection T)
    (standardNormalizedFredholmJuliaProjection_compact T hs ht)
  simp only [pairedStandardFibreOperatorHom_normalizedJuliaProjection] at h
  exact h

end BC4lean.KKTheory
