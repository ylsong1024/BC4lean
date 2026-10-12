import BC4lean.GlobalFredholmNormalization
import BC4lean.GlobalFredholmScalarCycle
import BC4lean.KasparovCompactPerturbation

/-! # Actual affine homotopy to the normalized scalar Fredholm cycle

The actual global compact rectangular perturbation gives a compact difference
of the two selfadjoint off-diagonal operators. Both endpoint cycles are proved
admissible, so the existing compact-perturbation theorem constructs the actual
affine operator homotopy to the contractive Fredholm representative.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ B E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [completeE : CompleteSpace E] [completeF : CompleteSpace F]

omit completeE completeF in
theorem offDiagonalAdjointable_sub [CompleteSpace E] [CompleteSpace F]
    (U T : AdjointableMap B E F) :
    offDiagonalAdjointable U - offDiagonalAdjointable T = offDiagonalAdjointable (U - T) := by
  ext x
  apply Prod.ext
  · simp only [AdjointableMap.coe_sub_apply, offDiagonalAdjointable_apply,
      rectangular_adjoint_sub, WithCStarModule.sub_fst, sumMk_fst]
  · simp only [AdjointableMap.coe_sub_apply, offDiagonalAdjointable_apply,
      WithCStarModule.sub_snd, sumMk_snd]

include completeE completeF in
theorem offDiagonalAdjointable_sub_isModuleCompact (U T : AdjointableMap B E F)
    (h : IsModuleCompact (U - T)) :
    IsModuleCompact (offDiagonalAdjointable U - offDiagonalAdjointable T) := by
  rw [offDiagonalAdjointable_sub, offDiagonalAdjointable]
  exact ((h.adjoint.comp_left sumInl).comp_right sumSnd).add
    ((h.comp_left sumInr).comp_right sumFst)

/-- The actual affine operator homotopy from a global Fredholm map to its
proved contractive compact perturbation. -/
def globalFredholmNormalizationHomotopy (T : AdjointableMap B E F)
    (hSource : IsModuleCompact (1 - T.adjoint.comp T))
    (hTarget : IsModuleCompact (T.comp T.adjoint - 1))
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F) :
    KasparovOperatorHomotopy (globalFredholmScalarCycle (Γ := Γ) T hSource hTarget hE hF)
      (offDiagonalAdjointable T) (offDiagonalAdjointable (globalFredholmNormalization T)) := by
  let normalizedCycle := globalFredholmScalarCycle (Γ := Γ) (globalFredholmNormalization T)
    (globalFredholmNormalization_sourceDefect_isModuleCompact T hSource)
    (globalFredholmNormalization_targetDefect_isModuleCompact T hSource hTarget) hE hF
  have hNew : (globalFredholmScalarCycle (Γ := Γ) T hSource hTarget hE hF).OperatorConditions
      (offDiagonalAdjointable (globalFredholmNormalization T)) :=
    { operator_odd := normalizedCycle.operator_odd
      selfadjoint_mod_compact := normalizedCycle.selfadjoint_mod_compact
      square_mod_compact := normalizedCycle.square_mod_compact
      commutator_compact := normalizedCycle.commutator_compact
      equivariance_mod_compact := normalizedCycle.equivariance_mod_compact }
  have hδ := offDiagonalAdjointable_sub_isModuleCompact (globalFredholmNormalization T) T
    (globalFredholmNormalization_sub_isModuleCompact T hSource)
  exact KasparovOperatorHomotopy.compactPerturbation
    (globalFredholmScalarCycle (Γ := Γ) T hSource hTarget hE hF)
    (offDiagonalAdjointable (globalFredholmNormalization T)) hNew
    (fun c => hδ.comp_right (scalarModuleRepresentation c))

end BC4lean.KKTheory
