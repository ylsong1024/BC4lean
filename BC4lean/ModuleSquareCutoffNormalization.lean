import BC4lean.ModuleCompactCFCIntertwining
import BC4lean.LocalizedModuleFunctionalCalculus
import BC4lean.GlobalModuleContractiveNormalization
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-! # Actual continuous square-cutoff normalization

The genuine continuous weight 1/sqrt(max(k,s)), for k>0, normalizes an
actual module map contractively. Its square defect is exactly CFC of a
continuous scalar function vanishing on [k,infinity). Compactness of that
defect is left to the genuine localized spectral estimate.
-/

noncomputable section
namespace BC4lean.KKTheory

def moduleSquareCutoffWeight (k s : ℝ) : ℝ := (Real.sqrt (max k s))⁻¹
def moduleSquareCutoffDefect (k s : ℝ) : ℝ := s / max k s - 1

theorem continuous_moduleSquareCutoffWeight {k : ℝ} (hk : 0 < k) :
    Continuous (moduleSquareCutoffWeight k) :=
  (Real.continuous_sqrt.comp (continuous_const.max continuous_id)).inv₀
    (fun s => ne_of_gt (Real.sqrt_pos.mpr (hk.trans_le (le_max_left k s))))

theorem continuous_moduleSquareCutoffDefect {k : ℝ} (hk : 0 < k) :
    Continuous (moduleSquareCutoffDefect k) :=
  (continuous_id.div (continuous_const.max continuous_id)
    (fun s => ne_of_gt (hk.trans_le (le_max_left k s)))).sub continuous_const

theorem moduleSquareCutoffWeight_square_eq {k : ℝ} (hk : 0 < k) (s : ℝ) :
    moduleSquareCutoffWeight k s * s * moduleSquareCutoffWeight k s = s / max k s := by
  have hm : 0 < max k s := hk.trans_le (le_max_left _ _)
  have hroot : Real.sqrt (max k s) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hm)
  have hsq := Real.sq_sqrt hm.le
  unfold moduleSquareCutoffWeight
  field_simp [hroot, ne_of_gt hm]
  rw [hsq]
  ring

theorem moduleSquareCutoffWeight_square_bounds {k s : ℝ} (hk : 0 < k) (hs : 0 ≤ s) :
    0 ≤ moduleSquareCutoffWeight k s * s * moduleSquareCutoffWeight k s ∧
      moduleSquareCutoffWeight k s * s * moduleSquareCutoffWeight k s ≤ 1 := by
  rw [moduleSquareCutoffWeight_square_eq hk]
  have hm : 0 < max k s := hk.trans_le (le_max_left _ _)
  exact ⟨div_nonneg hs hm.le, (div_le_one hm).mpr (le_max_right _ _)⟩

theorem moduleSquareCutoffDefect_eq_zero {k s : ℝ} (hk : 0 < k) (hs : k ≤ s) :
    moduleSquareCutoffDefect k s = 0 := by
  rw [moduleSquareCutoffDefect, max_eq_right hs, div_self (ne_of_gt (hk.trans_le hs)), sub_self]

theorem moduleSquareCutoffWeight_one {k : ℝ} (hk : k ≤ 1) :
    moduleSquareCutoffWeight k 1 = 1 := by
  simp only [moduleSquareCutoffWeight, max_eq_right hk, Real.sqrt_one, inv_one]

section ActualOperators
variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

local instance moduleSquareCutoffDomainPartialOrder :
    PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance moduleSquareCutoffDomainStarOrderedRing :
    StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _
local instance moduleSquareCutoffCodomainPartialOrder :
    PartialOrder (AdjointableMap B F F) := CStarAlgebra.spectralOrder _
local instance moduleSquareCutoffCodomainStarOrderedRing :
    StarOrderedRing (AdjointableMap B F F) := CStarAlgebra.spectralOrderedRing _

def moduleSquareCutoffNormalizer (k : ℝ) (T : AdjointableMap B E F) : AdjointableMap B E E :=
  cfc (moduleSquareCutoffWeight k) (T.adjoint.comp T)

def moduleSquareCutoffNormalization (k : ℝ) (T : AdjointableMap B E F) : AdjointableMap B E F :=
  T.comp (moduleSquareCutoffNormalizer k T)

omit [CompleteSpace F] in
@[simp] theorem moduleSquareCutoffNormalizer_adjoint (k : ℝ) (T : AdjointableMap B E F) :
    (moduleSquareCutoffNormalizer k T).adjoint = moduleSquareCutoffNormalizer k T :=
  (cfc_predicate (moduleSquareCutoffWeight k) (T.adjoint.comp T)).star_eq

theorem moduleSquareCutoffNormalization_adjoint_square {k : ℝ} (hk : 0 < k)
    (T : AdjointableMap B E F) :
    (moduleSquareCutoffNormalization k T).adjoint.comp (moduleSquareCutoffNormalization k T) =
      cfc (fun s : ℝ => s / max k s) (T.adjoint.comp T) := by
  have ha := (rectangular_adjoint_squares_nonneg T).2.isSelfAdjoint
  have hf := continuous_moduleSquareCutoffWeight hk
  have hc : cfc (fun s : ℝ => moduleSquareCutoffWeight k s * s * moduleSquareCutoffWeight k s)
      (T.adjoint.comp T) = moduleSquareCutoffNormalizer k T * (T.adjoint.comp T) *
        moduleSquareCutoffNormalizer k T := by
    rw [cfc_mul (fun s : ℝ => moduleSquareCutoffWeight k s * s) (moduleSquareCutoffWeight k) _
      (hf.mul continuous_id).continuousOn hf.continuousOn,
      cfc_mul (moduleSquareCutoffWeight k) (fun s : ℝ => s) _ hf.continuousOn
        continuous_id.continuousOn, cfc_id' ℝ _ ha]
    rfl
  have heq : (fun s : ℝ => s / max k s) =
      (fun s : ℝ => moduleSquareCutoffWeight k s * s * moduleSquareCutoffWeight k s) := by
    funext s
    exact (moduleSquareCutoffWeight_square_eq hk s).symm
  rw [heq, hc]
  ext x
  simp only [moduleSquareCutoffNormalization, AdjointableMap.adjoint_comp,
    moduleSquareCutoffNormalizer_adjoint, AdjointableMap.comp_apply, AdjointableMap.mul_apply]

theorem norm_moduleSquareCutoffNormalization_le {k : ℝ} (hk : 0 < k)
    (T : AdjointableMap B E F) : ‖moduleSquareCutoffNormalization k T‖ ≤ 1 := by
  have hnorm : ‖(moduleSquareCutoffNormalization k T).adjoint.comp
      (moduleSquareCutoffNormalization k T)‖ ≤ 1 := by
    rw [moduleSquareCutoffNormalization_adjoint_square hk]
    apply norm_cfc_le zero_le_one
    intro s hs
    have hb := moduleSquareCutoffWeight_square_bounds hk
      (spectrum_nonneg_of_nonneg (rectangular_adjoint_squares_nonneg T).2 hs)
    rw [moduleSquareCutoffWeight_square_eq hk] at hb
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2
  change ‖((moduleSquareCutoffNormalization k T).adjoint.comp
    (moduleSquareCutoffNormalization k T)).toCLM‖ ≤ 1 at hnorm
  rw [AdjointableMap.norm_toCLM_adjoint_comp_self] at hnorm
  change ‖moduleSquareCutoffNormalization k T‖ ^ 2 ≤ 1 at hnorm
  nlinarith [norm_nonneg (moduleSquareCutoffNormalization k T)]

/-- The construction is continuous on the actual normed space of module
maps. The positive adjoint square automatically supplies the CFC predicate. -/
theorem continuous_moduleSquareCutoffNormalization {k : ℝ} (hk : 0 < k) :
    Continuous (moduleSquareCutoffNormalization k : AdjointableMap B E F → AdjointableMap B E F) := by
  have hQ : Continuous (fun T : AdjointableMap B E F => T.adjoint.comp T) := by
    apply AdjointableMap.toCLM_isometry.comp_continuous_iff.mp
    change Continuous (fun T : AdjointableMap B E F => T.adjoint.toCLM.comp T.toCLM)
    exact ((ContinuousLinearMap.compL ℂ E F E).continuous.comp
      (AdjointableMap.toCLM_isometry.continuous.comp
        AdjointableMap.adjointContinuousLinearMap.continuous)).clm_apply
      AdjointableMap.toCLM_isometry.continuous
  have hN : Continuous (moduleSquareCutoffNormalizer k : AdjointableMap B E F → AdjointableMap B E E) :=
    Continuous.cfc_of_mem_nhdsSet (s := Set.univ) (moduleSquareCutoffWeight k) (by simp) hQ
      (fun T => (rectangular_adjoint_squares_nonneg T).2.isSelfAdjoint)
      (continuous_moduleSquareCutoffWeight hk).continuousOn
  apply AdjointableMap.toCLM_isometry.comp_continuous_iff.mp
  change Continuous (fun T : AdjointableMap B E F =>
    T.toCLM.comp (moduleSquareCutoffNormalizer k T).toCLM)
  exact ((ContinuousLinearMap.compL ℂ E E F).continuous.comp
    AdjointableMap.toCLM_isometry.continuous).clm_apply
      (AdjointableMap.toCLM_isometry.continuous.comp hN)

end ActualOperators

section SelfadjointOperators
variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

local instance moduleSquareCutoffSelfPartialOrder :
    PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance moduleSquareCutoffSelfStarOrderedRing :
    StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _

theorem moduleSquareCutoffNormalization_selfadjoint (k : ℝ)
    (T : AdjointableMap B E E) (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (moduleSquareCutoffNormalization k T) := by
  have hcomm : Commute (T.adjoint.comp T) T := by
    change Commute (star T * T) T
    rw [hT.star_eq]
    exact mul_assoc T T T
  have hNcomm := hcomm.cfc_real (moduleSquareCutoffWeight k)
  change star (T * moduleSquareCutoffNormalizer k T) = T * moduleSquareCutoffNormalizer k T
  rw [star_mul, show star (moduleSquareCutoffNormalizer k T) = moduleSquareCutoffNormalizer k T from
    moduleSquareCutoffNormalizer_adjoint k T, hT.star_eq]
  exact hNcomm.eq

theorem moduleSquareCutoffNormalization_square_defect {k : ℝ} (hk : 0 < k)
    (T : AdjointableMap B E E) (hT : IsSelfAdjoint T) :
    moduleSquareCutoffNormalization k T * moduleSquareCutoffNormalization k T - 1 =
      cfc (moduleSquareCutoffDefect k) (T * T) := by
  have hS := moduleSquareCutoffNormalization_selfadjoint k T hT
  have hsq := moduleSquareCutoffNormalization_adjoint_square hk T
  change star (moduleSquareCutoffNormalization k T) * moduleSquareCutoffNormalization k T = _ at hsq
  rw [hS.star_eq, show T.adjoint.comp T = T * T from by
    change star T * T = T * T
    rw [hT.star_eq]] at hsq
  rw [hsq]
  change cfc (fun s : ℝ => s / max k s) (T * T) - 1 =
    cfc (fun s : ℝ => s / max k s - 1) (T * T)
  have hf : Continuous (fun s : ℝ => s / max k s) :=
    continuous_id.div (continuous_const.max continuous_id)
      (fun s => ne_of_gt (hk.trans_le (le_max_left k s)))
  have hTT : IsSelfAdjoint (T * T) := by
    change star (T * T) = T * T
    simp only [star_mul, hT.star_eq]
  rw [cfc_sub (fun s : ℝ => s / max k s) (fun _ : ℝ => 1) (T * T)
    hf.continuousOn continuous_const.continuousOn, cfc_const_one ℝ (T * T) hTT]

/-- At a genuine locally unitary endpoint, cutoff normalization differs
from the endpoint only after actual localization by a compact map. -/
theorem moduleSquareCutoffNormalization_sub_mul_isModuleCompact
    {k : ℝ} (hk : 0 < k) (hkone : k ≤ 1)
    (T X : AdjointableMap B E E) (hT : IsSelfAdjoint T)
    (hlocal : IsModuleCompact ((T * T - 1) * X)) :
    IsModuleCompact ((moduleSquareCutoffNormalization k T - T) * X) := by
  have hQ := (rectangular_adjoint_squares_nonneg T).2.isSelfAdjoint
  have hlocal' : IsModuleCompact ((T.adjoint.comp T - algebraMap ℝ _ 1) * X) := by
    rw [map_one]
    change IsModuleCompact ((star T * T - 1) * X)
    rw [hT.star_eq]
    exact hlocal
  have hN := cfc_sub_value_mul_isModuleCompact (T.adjoint.comp T) X hQ 1 hlocal'
    (moduleSquareCutoffWeight k) (continuous_moduleSquareCutoffWeight hk)
  rw [moduleSquareCutoffWeight_one hkone, map_one] at hN
  have heq : (moduleSquareCutoffNormalization k T - T) * X =
      T * ((moduleSquareCutoffNormalizer k T - 1) * X) := by
    change (T * moduleSquareCutoffNormalizer k T - T) * X = _
    noncomm_ring
  rw [heq]
  exact mul_mem_moduleCompact_left T hN

end SelfadjointOperators
end BC4lean.KKTheory
