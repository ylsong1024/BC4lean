import BC4lean.GlobalModuleContractiveNormalization
import BC4lean.ModuleCompactPositivePart

/-! # Actual contractive normalization of a global Fredholm module map

For a=T*T set k=f(a), f(s)=1/√max(1,s), and replace T by Tk.
The scalar bound sf(s)²≤1 proves actual contractivity. The continuous
factorization f(s)−1=−(s−1)⁺/(√max(1,s)(√max(1,s)+1)) proves k−1 compact
from the actual compact positive part of a−1. Hence Tk−T is compact.
This normalization preserves the global Fredholm defects; arbitrary scalar
cycle support reduction and the eventual finite index comparison are separate.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

local instance standardGlobalFredholmNormalizationLocalInstance01 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance standardGlobalFredholmNormalizationLocalInstance02 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _
local instance standardGlobalFredholmNormalizationLocalInstance03 : PartialOrder (AdjointableMap B F F) := CStarAlgebra.spectralOrder _
local instance standardGlobalFredholmNormalizationLocalInstance04 : StarOrderedRing (AdjointableMap B F F) := CStarAlgebra.spectralOrderedRing _

private theorem cfc_positivePart_sub_one (T : AdjointableMap B E F) :
    (T.adjoint.comp T - 1)⁺ = cfc (fun s : ℝ => max (s - 1) 0) (T.adjoint.comp T) := by
  have ha := (rectangular_adjoint_squares_nonneg T).2.isSelfAdjoint
  have hh : cfc (fun s : ℝ => s - 1) (T.adjoint.comp T) = T.adjoint.comp T - 1 := by
    rw [cfc_sub (fun s : ℝ => s) (fun _ => (1 : ℝ)) _
      continuous_id.continuousOn continuous_const.continuousOn,
      cfc_id' ℝ _ ha, cfc_const 1 _ ha]
    simp only [map_one]
  rw [CFC.posPart_def, cfcₙ_eq_cfc, ← hh]
  simpa only [_root_.posPart_def] using
    (cfc_comp' (fun s : ℝ => max s 0) (fun s : ℝ => s - 1) (T.adjoint.comp T)
      (continuous_id.max continuous_const).continuousOn
      (continuous_id.sub continuous_const).continuousOn ha).symm

/-- The actual operator factorization makes the normalizer difference compact. -/
theorem globalFredholmNormalizer_sub_one (T : AdjointableMap B E F) :
    globalFredholmNormalizer T - 1 =
      -(T.adjoint.comp T - 1)⁺ * cfc fredholmNormRemainder (T.adjoint.comp T) := by
  have ha := (rectangular_adjoint_squares_nonneg T).2.isSelfAdjoint
  have hc : cfc (fun s : ℝ => fredholmNormWeight s - 1) (T.adjoint.comp T) =
      globalFredholmNormalizer T - 1 := by
    rw [cfc_sub fredholmNormWeight (fun _ => (1 : ℝ)) _
      continuous_fredholmNormWeight.continuousOn continuous_const.continuousOn, cfc_const _ _ ha]
    simp only [map_one, globalFredholmNormalizer]
  rw [← hc, cfc_positivePart_sub_one]
  calc
    _ = cfc (fun s : ℝ => -(max (s - 1) 0) * fredholmNormRemainder s) (T.adjoint.comp T) :=
      cfc_congr (fun s _ => fredholmNormWeight_sub_one s)
    _ = _ := by
      rw [cfc_mul (fun s : ℝ => -(max (s - 1) 0)) fredholmNormRemainder _
        ((continuous_id.sub continuous_const).max continuous_const).neg.continuousOn
          continuous_fredholmNormRemainder.continuousOn,
        cfc_neg (fun s : ℝ => max (s - 1) 0) (T.adjoint.comp T)]

theorem globalFredholmNormalization_sub_isModuleCompact (T : AdjointableMap B E F)
    (h : IsModuleCompact (1 - T.adjoint.comp T)) :
    IsModuleCompact (globalFredholmNormalization T - T) := by
  have hh : IsModuleCompact (T.adjoint.comp T - 1) := by
    simpa only [neg_sub] using h.neg
  have hp := hh.posPart ((rectangular_adjoint_squares_nonneg T).2.isSelfAdjoint.sub
    (IsSelfAdjoint.one (AdjointableMap B E E)))
  have hk : IsModuleCompact (globalFredholmNormalizer T - 1) := by
    rw [globalFredholmNormalizer_sub_one]
    exact hp.neg.comp_right (cfc fredholmNormRemainder (T.adjoint.comp T))
  have he : globalFredholmNormalization T - T = T.comp (globalFredholmNormalizer T - 1) := by
    ext x
    simp only [globalFredholmNormalization, AdjointableMap.coe_sub_apply,
      AdjointableMap.comp_apply, AdjointableMap.one_apply]
    exact (T.toCLM.map_sub (globalFredholmNormalizer T x) x).symm
  rw [he]
  exact hk.comp_left T

omit [StarOrderedRing B] [CompleteSpace E] [CompleteSpace F] in
theorem rectangular_adjoint_sub (U T : AdjointableMap B E F) :
    (U - T).adjoint = U.adjoint - T.adjoint := by
  apply AdjointableMap.toCLM_injective
  rw [AdjointableMap.toCLM_sub]
  change (U - T).adjointCLM = U.adjointCLM - T.adjointCLM
  exact AdjointableMap.adjointCLM_sub U T

omit [CompleteSpace E] [CompleteSpace F] in
theorem adjointSquare_sub_isModuleCompact (U T : AdjointableMap B E F)
    (h : IsModuleCompact (U - T)) : IsModuleCompact (U.adjoint.comp U - T.adjoint.comp T) := by
  have hadj : IsModuleCompact (U.adjoint - T.adjoint) := by
    simpa only [rectangular_adjoint_sub] using h.adjoint
  have he : U.adjoint.comp U - T.adjoint.comp T =
      (U.adjoint - T.adjoint).comp U + T.adjoint.comp (U - T) := by
    ext x
    simp only [AdjointableMap.coe_sub_apply, AdjointableMap.coe_add_apply,
      AdjointableMap.comp_apply]
    rw [T.adjoint.toCLM.map_sub]
    abel
  rw [he]
  exact (hadj.comp_right U).add (h.comp_left T.adjoint)

omit [CompleteSpace E] [CompleteSpace F] in
theorem reversedAdjointSquare_sub_isModuleCompact (U T : AdjointableMap B E F)
    (h : IsModuleCompact (U - T)) : IsModuleCompact (U.comp U.adjoint - T.comp T.adjoint) := by
  have hadj : IsModuleCompact (U.adjoint - T.adjoint) := by
    simpa only [rectangular_adjoint_sub] using h.adjoint
  have he : U.comp U.adjoint - T.comp T.adjoint =
      (U - T).comp U.adjoint + T.comp (U.adjoint - T.adjoint) := by
    ext x
    simp only [AdjointableMap.coe_sub_apply, AdjointableMap.coe_add_apply,
      AdjointableMap.comp_apply]
    rw [T.toCLM.map_sub]
    abel
  rw [he]
  exact (h.comp_right U.adjoint).add (hadj.comp_left T)

/-- The normalized source Fredholm defect is proved compact. -/
theorem globalFredholmNormalization_sourceDefect_isModuleCompact (T : AdjointableMap B E F)
    (hSource : IsModuleCompact (1 - T.adjoint.comp T)) :
    IsModuleCompact (1 - (globalFredholmNormalization T).adjoint.comp (globalFredholmNormalization T)) := by
  have hh := adjointSquare_sub_isModuleCompact (globalFredholmNormalization T) T
    (globalFredholmNormalization_sub_isModuleCompact T hSource)
  have he : 1 - (globalFredholmNormalization T).adjoint.comp (globalFredholmNormalization T) =
      (1 - T.adjoint.comp T) -
        ((globalFredholmNormalization T).adjoint.comp (globalFredholmNormalization T) - T.adjoint.comp T) := by abel
  rw [he]
  exact hSource.sub hh

/-- The normalized target Fredholm defect is proved compact as well. -/
theorem globalFredholmNormalization_targetDefect_isModuleCompact (T : AdjointableMap B E F)
    (hSource : IsModuleCompact (1 - T.adjoint.comp T))
    (hTarget : IsModuleCompact (T.comp T.adjoint - 1)) :
    IsModuleCompact ((globalFredholmNormalization T).comp (globalFredholmNormalization T).adjoint - 1) := by
  have hh := reversedAdjointSquare_sub_isModuleCompact (globalFredholmNormalization T) T
    (globalFredholmNormalization_sub_isModuleCompact T hSource)
  have he : (globalFredholmNormalization T).comp (globalFredholmNormalization T).adjoint - 1 =
      (T.comp T.adjoint - 1) +
        ((globalFredholmNormalization T).comp (globalFredholmNormalization T).adjoint - T.comp T.adjoint) := by abel
  rw [he]
  exact hTarget.add hh

end BC4lean.KKTheory
