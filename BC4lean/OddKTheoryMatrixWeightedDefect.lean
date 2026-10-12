import BC4lean.OddKTheoryWeightedCircleEntries
import BC4lean.OddFredholmWeightedFunctionalCalculus

/-! # Actual bounded weighted defect map for the matrix pullback

The four actual descended weighted circle coefficient maps are evaluated by
circle CFC and the genuine countable finite-row matrix action. Their finite
sum is bundled as a complex continuous linear map with an explicit bound.
Its value on the constant function 1 is the actual infinite operator's square
defect. No existence of this coefficient map is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped Topology CStarAlgebra

variable {B ι : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype ι] [DecidableEq ι]

/-- Bundle the actual common-circle CFC matrix coefficient action. -/
def oddKTheoryMatrixCircleCoefficientHom
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B))) :
    C(Circle, ℂ) →⋆ₐ[ℂ] OddKTheoryMatrixRowOperator B ι :=
  oddKTheoryCountableRowMatrixHom.comp (oddKTheoryCircleCFC u)

@[simp] theorem oddKTheoryMatrixCircleCoefficientHom_apply
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B))) (f : C(Circle, ℂ)) :
    oddKTheoryMatrixCircleCoefficientHom u f = oddKTheoryMatrixCircleCoefficient u f := rfl

section WeightedMap

variable (K : Set ℂ) [CompactSpace K]
  (hsegment : Set.range oddKTheoryLoopEigenvalue ⊆ K)
  (u : unitary (CStarMatrix ι ι (Unitization ℂ B)))

/-- The actual finite sum of four weighted matrix-CFC row entries. -/
def oddKTheoryMatrixWeightedDefectLinear : C(K, ℂ) →ₗ[ℂ] OddKTheoryMatrixRowOperator B ι where
  toFun f := ∑ i : Fin 4,
    oddKTheoryMatrixCircleCoefficientHom u (oddKTheoryLoopWeightedCircleEntryCLM K hsegment i f) *
      oddKTheoryRowLoopFixedFiniteOperator i
  map_add' f g := by
    simp only [map_add, add_mul, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [map_smul, smul_mul_assoc, Finset.smul_sum, RingHom.id_apply]

/-- An explicit finite norm bound for the genuine infinite weighted operator
map; the fixed finite operators need not be compact themselves. -/
def oddKTheoryMatrixWeightedDefectBound : ℝ :=
  ∑ i : Fin 4, ‖oddKTheoryLoopDefectCircleEntry i‖ *
    ‖oddKTheoryRowLoopFixedFiniteOperator (B := B) (E := FiniteStandardModule B ι) i‖

theorem oddKTheoryMatrixWeightedDefectLinear_norm_le (f : C(K, ℂ)) :
    ‖oddKTheoryMatrixWeightedDefectLinear K hsegment u f‖ ≤
      oddKTheoryMatrixWeightedDefectBound (B := B) (ι := ι) * ‖f‖ := by
  change ‖∑ i : Fin 4,
    oddKTheoryMatrixCircleCoefficientHom u (oddKTheoryLoopWeightedCircleEntryCLM K hsegment i f) *
      oddKTheoryRowLoopFixedFiniteOperator i‖ ≤ _
  calc
    _ ≤ ∑ i : Fin 4,
        ‖oddKTheoryMatrixCircleCoefficientHom u
          (oddKTheoryLoopWeightedCircleEntryCLM K hsegment i f) *
            oddKTheoryRowLoopFixedFiniteOperator i‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 4, (‖oddKTheoryLoopDefectCircleEntry i‖ * ‖f‖) *
        ‖oddKTheoryRowLoopFixedFiniteOperator (B := B) (E := FiniteStandardModule B ι) i‖ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ‖oddKTheoryMatrixCircleCoefficientHom u
            (oddKTheoryLoopWeightedCircleEntryCLM K hsegment i f)‖ *
              ‖oddKTheoryRowLoopFixedFiniteOperator i‖ := norm_mul_le _ _
        _ ≤ (‖oddKTheoryLoopDefectCircleEntry i‖ * ‖f‖) *
              ‖oddKTheoryRowLoopFixedFiniteOperator i‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact (NonUnitalStarAlgHom.norm_apply_le (oddKTheoryMatrixCircleCoefficientHom u) _).trans
            (oddKTheoryLoopWeightedCircleEntry_norm_le K hsegment f i)
    _ = oddKTheoryMatrixWeightedDefectBound (B := B) (ι := ι) * ‖f‖ := by
      unfold oddKTheoryMatrixWeightedDefectBound
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The actual bounded complex continuous linear weighted defect operator map. -/
def oddKTheoryMatrixWeightedDefectCLM : C(K, ℂ) →L[ℂ] OddKTheoryMatrixRowOperator B ι :=
  (oddKTheoryMatrixWeightedDefectLinear K hsegment u).mkContinuous
    (oddKTheoryMatrixWeightedDefectBound (B := B) (ι := ι))
    (oddKTheoryMatrixWeightedDefectLinear_norm_le K hsegment u)

@[simp] theorem oddKTheoryMatrixWeightedDefectCLM_apply (f : C(K, ℂ)) :
    oddKTheoryMatrixWeightedDefectCLM K hsegment u f =
      ∑ i : Fin 4, oddKTheoryMatrixCircleCoefficient u (oddKTheoryLoopWeightedCircleEntry K hsegment f i) *
        oddKTheoryRowLoopFixedFiniteOperator i := rfl

/-- The constant-one value is the genuine compact square defect, proved by
its actual matrix-unitary finite-entry identity. -/
theorem oddKTheoryMatrixWeightedDefectCLM_one :
    oddKTheoryMatrixWeightedDefectCLM K hsegment u (1 : C(K, ℂ)) =
      oddKTheoryMatrixLoopPullback u * oddKTheoryMatrixLoopPullback u - 1 := by
  rw [oddKTheoryMatrixWeightedDefectCLM_apply]
  simp only [oddKTheoryLoopWeightedCircleEntry_one_function]
  exact (oddKTheoryMatrixLoopPullback_square_defect u).symm

end WeightedMap
end BC4lean.KKTheory
