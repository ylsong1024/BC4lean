import BC4lean.GlobalFredholmNormalization

/-! # The defined normalization fixes actual contractions

The actual adjoint square has spectrum bounded above by one. The normalization
weight is therefore constantly one on that spectrum, so the defined continuous
functional calculus introduces no change to a contractive Fredholm map.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

local instance standardGlobalFredholmNormalizationFixedLocalInstance01 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance standardGlobalFredholmNormalizationFixedLocalInstance02 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _
local instance standardGlobalFredholmNormalizationFixedLocalInstance03 : PartialOrder (AdjointableMap B F F) := CStarAlgebra.spectralOrder _
local instance standardGlobalFredholmNormalizationFixedLocalInstance04 : StarOrderedRing (AdjointableMap B F F) := CStarAlgebra.spectralOrderedRing _

theorem globalFredholmNormalizer_eq_one_of_contractive
    (T : AdjointableMap B E F) (hT : ‖T‖ ≤ 1) : globalFredholmNormalizer T = 1 := by
  have hn : ‖T.adjoint.comp T‖ ≤ 1 := by
    change ‖(T.adjoint.comp T).toCLM‖ ≤ 1
    rw [AdjointableMap.norm_toCLM_adjoint_comp_self]
    change ‖T‖ ^ 2 ≤ 1
    nlinarith [norm_nonneg T]
  have hw : cfc fredholmNormWeight (T.adjoint.comp T) =
      cfc (fun _ : ℝ => (1 : ℝ)) (T.adjoint.comp T) := by
    apply cfc_congr
    intro s hs
    have hOne : ‖(1 : AdjointableMap B E E)‖ ≤ 1 := by
      change ‖ContinuousLinearMap.id ℂ E‖ ≤ 1
      exact ContinuousLinearMap.norm_id_le
    have hsNorm : ‖s‖ ≤ 1 := by
      calc
        ‖s‖ ≤ ‖T.adjoint.comp T‖ * ‖(1 : AdjointableMap B E E)‖ :=
          spectrum.norm_le_norm_mul_of_mem hs
        _ ≤ 1 := by
          simpa only [one_mul] using
            mul_le_mul hn hOne (norm_nonneg (1 : AdjointableMap B E E)) zero_le_one
    have hs1 : s ≤ 1 := (Real.le_norm_self s).trans hsNorm
    simp only [fredholmNormWeight, max_eq_left hs1, Real.sqrt_one, inv_one]
  unfold globalFredholmNormalizer
  rw [hw, cfc_const _ _ (rectangular_adjoint_squares_nonneg T).2.isSelfAdjoint]
  exact map_one _

theorem globalFredholmNormalization_eq_of_contractive
    (T : AdjointableMap B E F) (hT : ‖T‖ ≤ 1) : globalFredholmNormalization T = T := by
  rw [globalFredholmNormalization, globalFredholmNormalizer_eq_one_of_contractive T hT]
  ext x
  rfl

end BC4lean.KKTheory
