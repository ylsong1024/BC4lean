import BC4lean.LabeledTelescopeAction
import BC4lean.TelescopeHeightBound
import BC4lean.CompactLabeledSupport
import BC4lean.JoinFixedContraction
import BC4lean.FixedPointCriterion
import Mathlib.Topology.Compactness.SigmaCompact

/-! # Contractibility of the finite-subgroup fixed telescope
Compact images give local stage control; bump functions choose continuous
height bounds. Vertical raising, the lifted join contraction, and vertical
lowering then contract the actual fixed-point space.
-/
noncomputable section
open Set Topology
open scoped unitInterval
namespace BC4lean.ProperActions.LabeledOrbitTelescope
variable (Γ : Type*) [Group Γ] [Countable Γ]

/-- Every finite-subgroup fixed telescope is genuinely contractible. -/
theorem fixed_contractible (H : Subgroup Γ) [Finite H] :
    ContractibleSpace (FixedPointSpace H (Model Γ)) := by
  let X := FixedPointSpace H (LabeledOrbitRealization Γ)
  let E (n : ℕ) : Set X := {x | x.val ∈ stage Γ n}
  let T := ClosedStageTelescope.Telescope E
  have hm : Monotone E := fun _ _ h _ hx => stage_mono Γ h hx
  let e : FixedPointSpace H (Model Γ) ≃ₜ T := fixedHomeomorph Γ H
  let : LocallyCompactSpace (FixedPointSpace H (Model Γ)) :=
    fixedPointSpace_locallyCompact H
  let : LocallyCompactSpace T := e.symm.isInducing.locallyCompactSpace (by
    rw [e.symm.range_coe]
    exact isClosed_univ.isLocallyClosed)
  let : SecondCountableTopology T := e.symm.isEmbedding.secondCountableTopology
  let x₀ : X := LabeledOrbitRealization.fixedZeroPoint H
  obtain ⟨n₀, hn₀⟩ := LabeledOrbitSimplex.mem_exhaustion
    (LabeledOrbitRealization.supportSimplex x₀.val)
  have hx₀ : x₀ ∈ E n₀ := hn₀
  let C₀ := (LabeledOrbitRealization.fixedGlobalShiftHomotopy H).trans
    (LabeledOrbitRealization.fixedConeHomotopy H)
  let C : ContinuousMap.Homotopy (ClosedStageTelescope.projectionMap E)
      (ContinuousMap.const _ x₀) := C₀.compContinuousMap
        (ClosedStageTelescope.projectionMap E)
  have hcompact : ∀ K : Set T, IsCompact K →
      ∃ N, ∀ t p, p ∈ K → C (t,p) ∈ E N := by
    intro K hK
    let f : I × T → LabeledOrbitRealization Γ := fun p => (C p).val
    have hf : Continuous f := continuous_subtype_val.comp C.continuous
    have himage : IsCompact (f '' (univ ×ˢ K)) := (isCompact_univ.prod hK).image hf
    obtain ⟨N, hN⟩ := LabeledOrbitRealization.exists_exhaustion_stage himage
    refine ⟨N, fun t p hp => ?_⟩
    exact hN (f (t,p)) ⟨(t,p), ⟨mem_univ t,hp⟩,rfl⟩
  obtain ⟨q, hq, hnq, hb⟩ := ClosedStageTelescope.exists_height_bound_of_compact_control
    E hm n₀ C hcompact
  let : ContractibleSpace T := ClosedStageTelescope.contractible_of_controlled
    E hm x₀ n₀ hx₀ C q hq hnq hb
  exact e.contractibleSpace

/-- The locally compact telescope satisfies the full subgroup fixed-point criterion. -/
theorem fixedPointCriterion [TopologicalSpace Γ] [DiscreteTopology Γ] :
    FixedPointCriterion Γ (Model Γ) := by
  constructor
  · intro H hH
    let : Finite H := hH
    exact fixed_contractible Γ H
  · intro H hH
    let : Infinite H := hH
    exact infinite_fixedPoints_empty Γ H

end BC4lean.ProperActions.LabeledOrbitTelescope
