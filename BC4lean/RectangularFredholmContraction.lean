import BC4lean.RectangularFredholmStandardStabilization
import BC4lean.RelativeProjectionKasparovCycle
import Mathlib.Analysis.CStarAlgebra.Hom

/-! # Actual contractivity of projection cross maps and identity augmentation -/

noncomputable section
namespace BC4lean.KKTheory

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

local instance standardRectangularFredholmContractionLocalInstance01 {M N : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Bᵐᵒᵖ M]
    [CStarModule Bᵐᵒᵖ M] [CompleteSpace M] [NormedAddCommGroup N] [NormedSpace ℂ N]
    [SMul Bᵐᵒᵖ N] [CStarModule Bᵐᵒᵖ N] [CompleteSpace N] :
    CompleteSpace (HilbertModuleSum B M N) := hilbertModuleSum_complete

omit [CompleteSpace F] in
theorem projectionCrossMap_norm_le_one (P Q : AdjointableMap B E E)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    ‖projectionCrossMap P Q hP hQ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖Q (x : E)‖ ≤ 1 * ‖x‖
  calc
    _ ≤ ‖Q‖ * ‖(x : E)‖ := Q.toCLM.le_opNorm (x : E)
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (IsStarProjection.norm_le Q hQ) (norm_nonneg x)

omit [CompleteSpace F] in
theorem augmentedRectangularFredholm_norm_le_one [CompleteSpace F]
    (T : AdjointableMap B E F) (hT : ‖T‖ ≤ 1) :
    ‖augmentedRectangularFredholm T‖ ≤ 1 := by
  let A := augmentedRectangularFredholm T
  let S : AdjointableMap B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B) := 1
  have hOne : (1 : AdjointableMap B (StandardCountableHilbertModule B)
      (StandardCountableHilbertModule B)).adjoint = 1 := rfl
  have hsq : A.adjoint.comp A = sumMap (T.adjoint.comp T) S := by
    apply AdjointableMap.ext
    intro x
    simp only [A, S, augmentedRectangularFredholm, sumMap_adjoint,
      AdjointableMap.comp_apply, sumMap_apply, sumMk_fst, sumMk_snd,
      hOne, AdjointableMap.one_apply]
  have hnS : ‖S‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖x‖ ≤ 1 * ‖x‖
    exact (one_mul ‖x‖).symm.le
  have hnT : ‖T.adjoint.comp T‖ ≤ 1 := by
    change ‖(T.adjoint.comp T).toCLM‖ ≤ 1
    rw [AdjointableMap.norm_toCLM_adjoint_comp_self]
    change ‖T‖ ^ 2 ≤ 1
    nlinarith [norm_nonneg T]
  have hnA : ‖A.adjoint.comp A‖ ≤ 1 := by
    rw [hsq]
    change ‖sumMapStarAlgHom (T.adjoint.comp T, S)‖ ≤ 1
    rw [NonUnitalStarAlgHom.norm_map
      (sumMapStarAlgHom (B := B) (E := E) (F := StandardCountableHilbertModule B))
      sumMapStarAlgHom_injective]
    change max ‖T.adjoint.comp T‖ ‖S‖ ≤ 1
    exact max_le hnT hnS
  change ‖(A.adjoint.comp A).toCLM‖ ≤ 1 at hnA
  rw [AdjointableMap.norm_toCLM_adjoint_comp_self] at hnA
  change ‖A‖ ^ 2 ≤ 1 at hnA
  change ‖A‖ ≤ 1
  nlinarith [norm_nonneg A]

end BC4lean.KKTheory
