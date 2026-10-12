import BC4lean.ModuleCreationLocalCompact
import BC4lean.ModuleCompactCFCIntertwining
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

/-! # Genuine real CFC of a selfadjoint zero connection

Rectangular intertwining with the zero operator proves creation-local
compactness for continuous f with f(0)=0. In particular the positive part
and the residual T−T⁺ retain both actual zero-connection tests. This is the
CFC step in Skandalis's associativity partition, not a compact restriction.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B C E F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

namespace IsCreationLocallyCompact
variable {φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F}
  {T : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ)}

theorem realCFC (hT : IsCreationLocallyCompact φ T) (hTSA : IsSelfAdjoint T)
    (f : ℝ → ℝ) (hf : Continuous f) (hfzero : f 0 = 0) :
    IsCreationLocallyCompact φ (cfc f T) := by
  apply IsCreationLocallyCompact.of_selfadjoint (IsSelfAdjoint.cfc)
  intro x
  have hzero : (moduleCreationMap φ x).comp (0 : AdjointableMap C F F) = 0 := by
    apply AdjointableMap.ext
    intro y
    simp only [AdjointableMap.comp_apply, AdjointableMap.coe_zero_apply, map_zero]
  have hX : IsModuleCompact (T.comp (moduleCreationMap φ x) -
      (moduleCreationMap φ x).comp (0 : AdjointableMap C F F)) := by
    simpa only [hzero, sub_zero] using (hT x).1
  have h := cfc_intertwining_isModuleCompact T (0 : AdjointableMap C F F)
    hTSA (IsSelfAdjoint.zero _) (moduleCreationMap φ x) hX f hf
  simpa only [cfc_apply_zero, hfzero, map_zero, hzero, sub_zero] using h

theorem posPart (hT : IsCreationLocallyCompact φ T) (hTSA : IsSelfAdjoint T) :
    IsCreationLocallyCompact φ T⁺ := by
  have heq : cfc (fun s : ℝ => max s 0) T = T⁺ := by
    rw [CFC.posPart_def]
    simp only [_root_.posPart_def]
    exact (cfcₙ_eq_cfc (a := T) (f := fun s : ℝ => max s 0)
      (hf := (continuous_id.max continuous_const).continuousOn) (hf0 := by simp)).symm
  rw [← heq]
  exact hT.realCFC hTSA (fun s : ℝ => max s 0)
    (continuous_id.max continuous_const) (by simp)

theorem sub_posPart (hT : IsCreationLocallyCompact φ T) (hTSA : IsSelfAdjoint T) :
    IsCreationLocallyCompact φ (T - T⁺) := by
  have h := hT.add ((hT.posPart hTSA).smul (-1 : ℂ))
  simpa only [neg_one_smul, sub_eq_add_neg] using h

end IsCreationLocallyCompact
end BC4lean.KKTheory
