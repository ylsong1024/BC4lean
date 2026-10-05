import BC4lean.CompactModuleOperator
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit

/-! # A rectangular compactness criterion for Hilbert-module maps

An adjointable map is compact precisely when its adjoint followed by the map
is compact. The converse is proved using the actual approximate-unit filter
of the compact endomorphism C⋆-algebra of the source module and the rectangular
C⋆-norm identity. No approximate-unit action on module vectors is assumed.

This supplies the compactness criterion needed for creation maps once an actual
interior tensor product and its adjoint formula have been constructed. It does
not assume an interior tensor product or a creation map into existence.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped Topology
open Filter

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

namespace AdjointableMap

/-- The squared error after right composition is controlled by the corresponding
error of `T* T`. This estimate does not require the multiplier to be selfadjoint. -/
theorem norm_sub_comp_sq_le (T : AdjointableMap B E F) (e : AdjointableMap B E E) :
    ‖T - T.comp e‖ ^ 2 ≤
      (1 + ‖e‖) * ‖T.adjoint.comp T - (T.adjoint.comp T) * e‖ := by
  let a : AdjointableMap B E E := T.adjoint.comp T
  have hclm : (T - T.comp e).adjoint.toCLM =
      T.adjoint.toCLM - e.adjoint.toCLM.comp T.adjoint.toCLM := by
    change (T - T.comp e).adjointCLM =
      T.adjointCLM - e.adjointCLM.comp T.adjointCLM
    rw [adjointCLM_sub]
    rfl
  have hexp : (T - T.comp e).adjoint.comp (T - T.comp e) =
      (a - a * e) - e.adjoint * (a - a * e) := by
    apply toCLM_injective
    ext x
    change (T - T.comp e).adjoint.toCLM ((T - T.comp e).toCLM x) = _
    rw [hclm, toCLM_sub]
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      coe_sub_apply, mul_apply]
    change T.adjointCLM (T.toCLM x - T.toCLM (e.toCLM x)) -
      e.adjointCLM (T.adjointCLM (T.toCLM x - T.toCLM (e.toCLM x))) =
        (T.adjointCLM (T.toCLM x) - T.adjointCLM (T.toCLM (e.toCLM x))) -
          e.adjointCLM (T.adjointCLM (T.toCLM x) -
            T.adjointCLM (T.toCLM (e.toCLM x)))
    simp only [map_sub]
  have hnorm : ‖e.adjoint‖ = ‖e‖ := norm_adjoint_toCLM e
  calc
    ‖T - T.comp e‖ ^ 2 = ‖(T - T.comp e).adjoint.comp (T - T.comp e)‖ :=
      (norm_toCLM_adjoint_comp_self (T - T.comp e)).symm
    _ = ‖(a - a * e) - e.adjoint * (a - a * e)‖ := by rw [hexp]
    _ ≤ ‖a - a * e‖ + ‖e.adjoint * (a - a * e)‖ := norm_sub_le _ _
    _ ≤ ‖a - a * e‖ + ‖e.adjoint‖ * ‖a - a * e‖ :=
      add_le_add le_rfl (norm_mul_le _ _)
    _ = (1 + ‖e‖) * ‖T.adjoint.comp T - (T.adjoint.comp T) * e‖ := by
      rw [hnorm]
      dsimp only [a]
      ring

end AdjointableMap

/-- Rectangular compactness is equivalent to compactness of `T* T`. Only the
source module needs to be complete for this proof. -/
theorem isModuleCompact_iff_adjoint_comp_self [CompleteSpace E]
    (T : AdjointableMap B E F) :
    IsModuleCompact T ↔ IsModuleCompact (T.adjoint.comp T) := by
  constructor
  · intro hT
    exact hT.comp_left T.adjoint
  · intro hT
    let a : CompactModuleOperator B E := ⟨T.adjoint.comp T, hT⟩
    let : PartialOrder (CompactModuleOperator B E) :=
      CStarAlgebra.spectralOrder (CompactModuleOperator B E)
    let : StarOrderedRing (CompactModuleOperator B E) :=
      CStarAlgebra.spectralOrderedRing (CompactModuleOperator B E)
    have hau := CStarAlgebra.increasingApproximateUnit (CompactModuleOperator B E)
    have hconst : Tendsto (fun _ : CompactModuleOperator B E => a)
        (CStarAlgebra.approximateUnit (CompactModuleOperator B E)) (𝓝 a) :=
      tendsto_const_nhds
    have hlim : Tendsto (fun e : CompactModuleOperator B E => ‖a - a * e‖)
        (CStarAlgebra.approximateUnit (CompactModuleOperator B E)) (𝓝 (0 : ℝ)) := by
      simpa only [sub_self, norm_zero] using
        (hconst.sub (hau.tendsto_mul_left a)).norm
    change T ∈ (moduleCompact B E F : Set (AdjointableMap B E F))
    rw [← (moduleCompact_isClosed (B := B) (E := E) (F := F)).closure_eq]
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    have hδ : 0 < ε ^ 2 / 2 := by positivity
    obtain ⟨e, he, hsmall⟩ :=
      (hau.eventually_norm.and (hlim.eventually (gt_mem_nhds hδ))).exists
    change ‖(e : AdjointableMap B E E)‖ ≤ 1 at he
    change ‖T.adjoint.comp T - (T.adjoint.comp T) * (e : AdjointableMap B E E)‖ <
      ε ^ 2 / 2 at hsmall
    refine ⟨T.comp e.val, comp_mem_moduleCompact T e.property, ?_⟩
    rw [dist_eq_norm]
    have hbound := AdjointableMap.norm_sub_comp_sq_le T e.val
    have hbound' : ‖T - T.comp e.val‖ ^ 2 ≤
        2 * ‖T.adjoint.comp T - (T.adjoint.comp T) * e.val‖ :=
      hbound.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
    have hsq : ‖T - T.comp e.val‖ ^ 2 < ε ^ 2 := by
      nlinarith
    nlinarith [norm_nonneg (T - T.comp e.val)]

namespace IsModuleCompact

/-- Recover rectangular compactness from compactness of `T* T`. -/
theorem of_adjoint_comp_self [CompleteSpace E] {T : AdjointableMap B E F}
    (hT : IsModuleCompact (T.adjoint.comp T)) : IsModuleCompact T :=
  (isModuleCompact_iff_adjoint_comp_self T).mpr hT

end IsModuleCompact
end BC4lean.KKTheory
