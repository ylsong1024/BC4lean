import BC4lean.EquivariantMaps
import BC4lean.ProperActions

/-! # Properness transferred along an equivariant map -/

open Filter Topology

namespace BC4lean.ProperActions

variable {Γ A X : Type*} [Group Γ] [TopologicalSpace Γ]
variable [TopologicalSpace A] [TopologicalSpace X] [MulAction Γ A] [MulAction Γ X]

/-- A Hausdorff continuous Γ-space mapping equivariantly to a proper Γ-space is proper. -/
theorem EquivariantMap.properSMul [T2Space A] [ContinuousSMul Γ A] [ProperSMul Γ X]
    (f : EquivariantMap Γ A X) : ProperSMul Γ A := by
  apply properSMul_iff_continuousSMul_ultrafilter_tendsto_t2.mpr
  refine ⟨inferInstance, fun U a b hab => ?_⟩
  let m : Γ × A → Γ × X := fun p => (p.1, f p.2)
  let V := U.map m
  have hv : Tendsto (fun p : Γ × X => (p.1 • p.2,p.2)) V (𝓝 (f a,f b)) := by
    rw [show (V : Filter (Γ × X)) = Filter.map m U from Ultrafilter.coe_map m U,
      tendsto_map'_iff]
    have ht := ((f.continuous.prodMap f.continuous).tendsto (a,b)).comp hab
    simpa only [Function.comp_def, Prod.map_apply, m, f.map_smul] using ht
  obtain ⟨g, _, hg⟩ :=
    (properSMul_iff_continuousSMul_ultrafilter_tendsto.mp (inferInstance : ProperSMul Γ X)).2
      V (f a) (f b) hv
  refine ⟨g, ?_⟩
  simpa only [V, Ultrafilter.coe_map, tendsto_map'_iff, Function.comp_def, m] using hg

end BC4lean.ProperActions
