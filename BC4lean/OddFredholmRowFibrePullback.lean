import BC4lean.CountableHilbertModuleFibre
import BC4lean.OddFredholmPullbackNaturality
import BC4lean.IntervalModuleCompactFibre
import BC4lean.OddIntervalKasparovFibre
import BC4lean.OddKTheoryCompactUnitaryClass

/-! # Actual completed-fibre naturality of the whole periodic row inverse

The true row-fibre unitary intertwines every fixed signed coordinate rule,
the actual coefficient diagonal and its continuous functional calculus.
Consequently it identifies whole completed fibres of the row inverse cycles.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped CStarAlgebra

variable {B X M : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, B)ᵐᵒᵖ M]
  [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

def oddFredholmRowFibreOperatorHom (t : X) :
    AdjointableMap C(X, B) (CountableHilbertModuleSum C(X, B) M)
      (CountableHilbertModuleSum C(X, B) M) →⋆ₐ[ℂ]
        OddKTheoryCountableOperator B (HilbertModuleFibre B M t) :=
  (countableModuleFibreEquiv t).transportStarAlgEquiv.toStarAlgHom.comp (hilbertModuleFibreOperatorHom t)

theorem oddFredholmRowFibreOperatorHom_inclusion (t : X)
    (T : OddKTheoryCountableOperator C(X, B) M) (z : ℤ) (x : M) :
    oddFredholmRowFibreOperatorHom t T
      (oddKTheoryRowIntegerInclusion z (hilbertModuleFibreMk (B := B) t x)) =
        countableModuleFibreEvaluation t (T (oddKTheoryRowIntegerInclusion z x)) := by
  rw [← countableModuleFibreEquiv_mk_inclusion]
  change (countableModuleFibreEquiv t).transport
    (hilbertModuleFibreOperator (B := B) t T)
      (countableModuleFibreEquiv t (hilbertModuleFibreMk (B := B) t
        (oddKTheoryRowIntegerInclusion z x))) = _
  rw [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply,
    hilbertModuleFibreOperator_mk, countableModuleFibreEquiv_mk]

theorem oddFredholmRowFibreOperatorHom_diagonal (t : X) (T : AdjointableMap C(X, B) M M) :
    oddFredholmRowFibreOperatorHom t (countableModuleDiagonal T) =
      countableModuleDiagonal (hilbertModuleFibreOperator (B := B) t T) := by
  apply oddKTheoryRowOperator_ext_integerCoordinates
  intro z x
  obtain ⟨y, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := M) t x
  rw [oddFredholmRowFibreOperatorHom_inclusion, oddKTheoryRowDiagonal_integerInclusion,
    countableModuleFibreEvaluation_inclusion, oddKTheoryRowDiagonal_integerInclusion,
    hilbertModuleFibreOperator_mk]

theorem oddFredholmRowFibreOperatorHom_fixed (t : X) (i : OddKTheoryLoopTerm) :
    oddFredholmRowFibreOperatorHom t (oddKTheoryRowLoopTermOperator i) =
      (oddKTheoryRowLoopTermOperator (B := B) (E := HilbertModuleFibre B M t) i) := by
  apply oddKTheoryRowOperator_ext_integerCoordinates
  intro z x
  obtain ⟨y, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := M) t x
  rw [oddFredholmRowFibreOperatorHom_inclusion, oddKTheoryRowLoopTermOperator_coordinateRule,
    map_smul, countableModuleFibreEvaluation_inclusion, map_smul,
    oddKTheoryRowLoopTermOperator_coordinateRule]

def oddFredholmModuleFibreUnitary (t : X) (U : unitary (AdjointableMap C(X, B) M M)) :
    unitary (AdjointableMap B (HilbertModuleFibre B M t) (HilbertModuleFibre B M t)) :=
  ⟨hilbertModuleFibreOperator (B := B) t U, Unitary.map_mem (hilbertModuleFibreOperatorHom t) U.property⟩

theorem oddFredholmRowFibreOperatorHom_pullback (t : X)
    (U : unitary (AdjointableMap C(X, B) M M)) :
    oddFredholmRowFibreOperatorHom t (oddFredholmRowUnitaryPullback U) =
      oddFredholmRowUnitaryPullback (oddFredholmModuleFibreUnitary t U) := by
  unfold oddFredholmRowUnitaryPullback oddKTheoryFiniteRowFormula
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, oddFredholmRowFibreOperatorHom_diagonal, oddFredholmRowFibreOperatorHom_fixed]
  rw [oddKTheoryCircleCFC_map (hilbertModuleFibreOperatorHom t) (map_continuous _)
    U (oddFredholmModuleFibreUnitary t U) rfl]

theorem oddFredholmModuleFibreUnitary_compact (t : X)
    (U : unitary (AdjointableMap C(X, B) M M))
    (hU : IsModuleCompact ((U : AdjointableMap C(X, B) M M) - 1)) :
    IsModuleCompact ((oddFredholmModuleFibreUnitary t U : _) - 1) := by
  simpa only [oddFredholmModuleFibreUnitary, hilbertModuleFibreOperator_sub,
    hilbertModuleFibreOperator_one] using hU.fibre t

/-- The fibre of the actual interval row cycle is identified as a whole
cycle, including its scalar representation and action, by the proved
completed row-fibre unitary. -/
def oddFredholmCompactUnitaryPullbackFibreIso [TopologicalSpace.SeparableSpace B]
    [TopologicalSpace.SeparableSpace C(X, B)] (t : X)
    (hM : IsCountablyGeneratedModule C(X, B) M)
    (U : unitary (AdjointableMap C(X, B) M M))
    (hU : IsModuleCompact ((U : AdjointableMap C(X, B) M M) - 1)) :
    OddKasparovCycleIso
      ((oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit) hM U hU).fibre t)
      (oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit) (hM.fibre t)
        (oddFredholmModuleFibreUnitary t U) (oddFredholmModuleFibreUnitary_compact t U hU)) where
  moduleEquiv := countableModuleFibreEquiv t
  action_intertwine g x := by
    have hg : g = 1 := Subsingleton.elim _ _
    subst g
    rw [EquivariantHilbertModule.one_apply, EquivariantHilbertModule.one_apply]
  representation_intertwine a x := by
    obtain ⟨y, rfl⟩ := hilbertModuleFibreMk_surjective (B := B)
      (M := CountableHilbertModuleSum C(X, B) M) t x
    rw [OddKasparovCycle.fibre_representation_mk]
    change countableModuleFibreEquiv t (hilbertModuleFibreMk (B := B) t (a • y)) =
      a • countableModuleFibreEquiv t (hilbertModuleFibreMk (B := B) t y)
    rw [map_smul, (countableModuleFibreEquiv t).map_smul]
  operator_intertwine x := by
    have ht := oddFredholmRowFibreOperatorHom_pullback t U
    have hx := congrArg (fun T => T (countableModuleFibreEquiv t x)) ht
    change countableModuleFibreEquiv t
      (hilbertModuleFibreOperator (B := B) t (oddFredholmRowUnitaryPullback U)
        ((countableModuleFibreEquiv t).symm (countableModuleFibreEquiv t x))) =
      oddFredholmRowUnitaryPullback (oddFredholmModuleFibreUnitary t U)
        (countableModuleFibreEquiv t x) at hx
    rw [HilbertModuleEquiv.symm_apply_apply] at hx
    exact hx

end BC4lean.KKTheory
