import BC4lean.OddKTheoryCountableRowEquiv
import BC4lean.OddFredholmFullNormalization

/-! # Genuine module-unitary naturality of the infinite odd pullback

The coordinatewise module unitary preserves every fixed signed-coordinate
operator. It conjugates coefficient diagonals and their actual circle CFC.
Consequently the entire finite periodic formula and its whole odd cycle are
transported by an actual unitary of completed row modules.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped CStarAlgebra

variable {Γ B E N : Type*} [Group Γ] [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup N] [NormedSpace ℂ N] [SMul Bᵐᵒᵖ N] [CStarModule Bᵐᵒᵖ N] [CompleteSpace N]

@[simp] theorem oddKTheoryCountableRowEquiv_integerInclusion (u : HilbertModuleEquiv B E N)
    (i : ℤ) (x : E) : oddKTheoryCountableRowEquiv u (oddKTheoryRowIntegerInclusion i x) =
      oddKTheoryRowIntegerInclusion i (u x) := oddKTheoryCountableRowEquiv_inclusion u _ x

@[simp] theorem oddKTheoryCountableRowEquiv_symm_integerInclusion (u : HilbertModuleEquiv B E N)
    (i : ℤ) (x : N) : (oddKTheoryCountableRowEquiv u).symm (oddKTheoryRowIntegerInclusion i x) =
      oddKTheoryRowIntegerInclusion i (u.symm x) :=
  oddKTheoryCountableRowEquiv_inclusion u.symm _ x

theorem oddKTheoryCountableRowEquiv_transport_fixed (u : HilbertModuleEquiv B E N)
    (i : OddKTheoryLoopTerm) :
    (oddKTheoryCountableRowEquiv u).transport (oddKTheoryRowLoopTermOperator i) =
      (oddKTheoryRowLoopTermOperator (B := B) (E := N) i) := by
  apply oddKTheoryRowOperator_ext_integerCoordinates
  intro n x
  rw [HilbertModuleEquiv.transport_apply, oddKTheoryCountableRowEquiv_symm_integerInclusion,
    oddKTheoryRowLoopTermOperator_coordinateRule, oddKTheoryCountableRowEquiv_integerInclusion,
    u.map_smul, u.apply_symm_apply, oddKTheoryRowLoopTermOperator_coordinateRule]

theorem oddKTheoryCountableRowEquiv_transport_diagonal (u : HilbertModuleEquiv B E N)
    (T : AdjointableMap B E E) :
    (oddKTheoryCountableRowEquiv u).transport (countableModuleDiagonal T) =
      countableModuleDiagonal (u.transport T) := by
  apply oddKTheoryRowOperator_ext_integerCoordinates
  intro n x
  rw [HilbertModuleEquiv.transport_apply, oddKTheoryCountableRowEquiv_symm_integerInclusion,
    oddKTheoryRowDiagonal_integerInclusion, oddKTheoryCountableRowEquiv_integerInclusion,
    oddKTheoryRowDiagonal_integerInclusion, HilbertModuleEquiv.transport_apply]

def oddFredholmEquivUnitary (u : HilbertModuleEquiv B E N)
    (U : unitary (AdjointableMap B E E)) : unitary (AdjointableMap B N N) :=
  ⟨u.transport (U : AdjointableMap B E E), Unitary.map_mem u.transportStarAlgEquiv.toStarAlgHom U.property⟩

omit [CompleteSpace E] [CompleteSpace N] in
theorem oddFredholmEquivUnitary_compact (u : HilbertModuleEquiv B E N)
    (U : unitary (AdjointableMap B E E))
    (hU : IsModuleCompact ((U : AdjointableMap B E E) - 1)) :
    IsModuleCompact ((oddFredholmEquivUnitary u U : AdjointableMap B N N) - 1) := by
  change IsModuleCompact (u.transport (U : AdjointableMap B E E) - 1)
  have h := u.transportMap_isModuleCompact u hU
  change IsModuleCompact (u.transport ((U : AdjointableMap B E E) - 1)) at h
  simpa only [HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_one] using h

set_option maxHeartbeats 2000000 in
theorem oddFredholmRowUnitaryPullback_transport (u : HilbertModuleEquiv B E N)
    (U : unitary (AdjointableMap B E E)) :
    (oddKTheoryCountableRowEquiv u).transport (oddFredholmRowUnitaryPullback U) =
      oddFredholmRowUnitaryPullback (oddFredholmEquivUnitary u U) := by
  change (oddKTheoryCountableRowEquiv u).transportStarAlgEquiv.toStarAlgHom _ = _
  unfold oddFredholmRowUnitaryPullback oddKTheoryFiniteRowFormula
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul]
  change (oddKTheoryCountableRowEquiv u).transport
      (countableModuleDiagonal (oddKTheoryCircleCFC U (oddKTheoryLoopTermCoefficient i))) *
    (oddKTheoryCountableRowEquiv u).transport (oddKTheoryRowLoopTermOperator i) = _
  rw [oddKTheoryCountableRowEquiv_transport_diagonal, oddKTheoryCountableRowEquiv_transport_fixed]
  have h := oddKTheoryCircleCFC_map u.transportStarAlgEquiv.toStarAlgHom (map_continuous _)
    U (oddFredholmEquivUnitary u U) rfl (oddKTheoryLoopTermCoefficient i)
  change u.transport (oddKTheoryCircleCFC U (oddKTheoryLoopTermCoefficient i)) =
    oddKTheoryCircleCFC (oddFredholmEquivUnitary u U) (oddKTheoryLoopTermCoefficient i) at h
  rw [h]

def oddFredholmCompactUnitaryPullbackCycleIso (u : HilbertModuleEquiv B E N)
    (hE : IsCountablyGeneratedModule B E) (hN : IsCountablyGeneratedModule B N)
    (U : unitary (AdjointableMap B E E))
    (hU : IsModuleCompact ((U : AdjointableMap B E E) - 1)) :
    OddKasparovCycleIso (oddFredholmCompactUnitaryPullbackCycle (Γ := Γ) hE U hU)
      (oddFredholmCompactUnitaryPullbackCycle (Γ := Γ) hN (oddFredholmEquivUnitary u U)
        (oddFredholmEquivUnitary_compact u U hU)) where
  moduleEquiv := oddKTheoryCountableRowEquiv u
  action_intertwine _ _ := rfl
  representation_intertwine a x := (oddKTheoryCountableRowEquiv u).map_smul a x
  operator_intertwine x := by
    change oddKTheoryCountableRowEquiv u (oddFredholmRowUnitaryPullback U x) =
      oddFredholmRowUnitaryPullback (oddFredholmEquivUnitary u U) (oddKTheoryCountableRowEquiv u x)
    have h := congrArg (fun T => T (oddKTheoryCountableRowEquiv u x))
      (oddFredholmRowUnitaryPullback_transport u U)
    simpa only [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply] using h

end BC4lean.KKTheory
