import BC4lean.OddKTheoryRowSumFormula
import BC4lean.OddKasparovHomotopyGroup

/-! # The full odd class of an actual compact unitary

Whole completed row unitaries prove invariance under coefficient-module
unitaries and direct sums. Actual norm paths give full operator homotopies.
The identity has an exactly degenerate sign operator.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped CStarAlgebra

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F] [TopologicalSpace.SeparableSpace B]

local instance oddContinuationOddKTheoryCompactUnitaryClassLocalInstance01 : CompleteSpace (HilbertModuleSum B E F) := hilbertModuleSum_complete
local instance oddContinuationOddKTheoryCompactUnitaryClassLocalInstance02 : CompleteSpace (HilbertModuleSum B (CountableHilbertModuleSum B E)
    (CountableHilbertModuleSum B F)) := hilbertModuleSum_complete

def oddKTheorySumOperatorUnitary (U : unitary (AdjointableMap B E E))
    (V : unitary (AdjointableMap B F F)) :
    unitary (AdjointableMap B (HilbertModuleSum B E F) (HilbertModuleSum B E F)) :=
  ⟨sumMap U V, Unitary.mem_iff.mpr (by
    constructor <;> rw [← sumMap_star, ← sumMap_mul]
    · rw [U.property.1, V.property.1, sumMap_one]
    · rw [U.property.2, V.property.2, sumMap_one])⟩

theorem oddKTheorySumOperatorUnitary_compact
    (U : unitary (AdjointableMap B E E)) (V : unitary (AdjointableMap B F F))
    (hU : IsModuleCompact ((U : AdjointableMap B E E) - 1))
    (hV : IsModuleCompact ((V : AdjointableMap B F F) - 1)) :
    IsModuleCompact ((oddKTheorySumOperatorUnitary U V : _) - 1) := by
  simpa only [oddKTheorySumOperatorUnitary, ← sumMap_one, ← sumMap_sub] using hU.sumMap hV

theorem oddKTheoryCircleCFC_sumOperatorUnitary
    (U : unitary (AdjointableMap B E E)) (V : unitary (AdjointableMap B F F)) :
    oddKTheoryCircleCFC (oddKTheorySumOperatorUnitary U V) =
      oddKTheoryCircleSumHom (oddKTheoryCircleCFC U) (oddKTheoryCircleCFC V) := by
  apply ContinuousMap.UniqueHom.eq_of_continuous_of_map_id (Metric.sphere (0 : ℂ) 1)
    _ _ (continuous_oddKTheoryCircleCFC _) (map_continuous _)
  rw [oddKTheoryCircleCFC_coordinate]
  change sumMap (U : AdjointableMap B E E) (V : AdjointableMap B F F) =
    sumMap (oddKTheoryCircleCFC U ((ContinuousMap.id ℂ).restrict (Metric.sphere 0 1)))
      (oddKTheoryCircleCFC V ((ContinuousMap.id ℂ).restrict (Metric.sphere 0 1)))
  rw [oddKTheoryCircleCFC_coordinate, oddKTheoryCircleCFC_coordinate]

def oddKTheoryTransportOperatorUnitary (e : HilbertModuleEquiv B E F)
    (U : unitary (AdjointableMap B E E)) : unitary (AdjointableMap B F F) :=
  ⟨e.transport U, Unitary.map_mem e.transportStarAlgEquiv.toStarAlgHom U.property⟩

theorem oddKTheoryTransportOperatorUnitary_compact (e : HilbertModuleEquiv B E F)
    (U : unitary (AdjointableMap B E E))
    (hU : IsModuleCompact ((U : AdjointableMap B E E) - 1)) :
    IsModuleCompact ((oddKTheoryTransportOperatorUnitary e U : _) - 1) := by
  simpa only [oddKTheoryTransportOperatorUnitary, HilbertModuleEquiv.transport_sub,
    HilbertModuleEquiv.transport_one] using e.transportMap_isModuleCompact e hU

def oddKTheoryCompactUnitaryTransportIso (hE : IsCountablyGeneratedModule B E)
    (hF : IsCountablyGeneratedModule B F) (e : HilbertModuleEquiv B E F)
    (U : unitary (AdjointableMap B E E))
    (hU : IsModuleCompact ((U : AdjointableMap B E E) - 1)) :
    OddKasparovCycleIso (oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit) hE U hU)
      (oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit) hF (oddKTheoryTransportOperatorUnitary e U)
        (oddKTheoryTransportOperatorUnitary_compact e U hU)) where
  moduleEquiv := oddKTheoryCountableRowEquiv e
  action_intertwine _ _ := rfl
  representation_intertwine a x := (oddKTheoryCountableRowEquiv e).map_smul a x
  operator_intertwine x := by
    have ht := oddFredholmRowUnitaryPullback_transport e U
    have hh := congrArg (fun T => T (oddKTheoryCountableRowEquiv e x)) ht
    simpa only [oddFredholmCompactUnitaryPullbackCycle, oddKTheoryScalarFredholmCycle,
      oddFredholmRowUnitaryPullback, HilbertModuleEquiv.transport_apply,
      HilbertModuleEquiv.symm_apply_apply, oddKTheoryTransportOperatorUnitary,
      oddFredholmEquivUnitary] using hh

def oddKTheoryCompactUnitarySumIso (hE : IsCountablyGeneratedModule B E)
    (hF : IsCountablyGeneratedModule B F)
    (U : unitary (AdjointableMap B E E)) (V : unitary (AdjointableMap B F F))
    (hU : IsModuleCompact ((U : AdjointableMap B E E) - 1))
    (hV : IsModuleCompact ((V : AdjointableMap B F F) - 1)) :
    OddKasparovCycleIso
      (oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit) (hE.sum hF)
        (oddKTheorySumOperatorUnitary U V) (oddKTheorySumOperatorUnitary_compact U V hU hV))
      ((oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit) hE U hU).directSum
        (oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit) hF V hV)) where
  moduleEquiv := oddKTheoryCountableSumEquiv
  action_intertwine _ _ := rfl
  representation_intertwine a x := by
    change oddKTheoryCountableSumEquiv (a • x) = a • oddKTheoryCountableSumEquiv x
    exact oddKTheoryCountableSumEquiv.map_smul a x
  operator_intertwine x := by
    have ht := oddKTheoryRowSumSplit_transport_formula (oddKTheoryCircleCFC U) (oddKTheoryCircleCFC V)
    rw [← oddKTheoryCircleCFC_sumOperatorUnitary U V] at ht
    have hh := congrArg (fun T => T (oddKTheoryCountableSumEquiv x)) ht
    simpa only [oddFredholmCompactUnitaryPullbackCycle, oddKTheoryScalarFredholmCycle,
      OddKasparovCycle.directSum, oddFredholmRowUnitaryPullback,
      HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply] using hh

theorem oddKTheoryCompactUnitaryPullbackCycle_one_degenerate (hE : IsCountablyGeneratedModule B E) :
    (oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit) hE (1 : unitary (AdjointableMap B E E))
      (by simpa only [sub_self] using IsModuleCompact.zero)).IsDegenerate := by
  have he : oddFredholmRowUnitaryPullback (1 : unitary (AdjointableMap B E E)) =
      oddKTheoryRowSignOperator := by
    unfold oddFredholmRowUnitaryPullback oddKTheoryFiniteRowFormula
    simp only [Fintype.sum_sum_type, oddKTheoryLoopTermCoefficient,
      oddKTheoryRowLoopTermOperator, Fintype.sum_unique, oddKTheoryCircleCFC_one_algebraMap,
      oddKTheoryLoopResidualCircleCoefficient_one, oddKTheoryLoopSignCircleCoefficient_one,
      oddKTheoryLoopFiniteCircleCoefficient_one, map_zero, map_one,
      Finset.sum_const_zero, zero_mul, one_mul, zero_add, add_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    change (oddFredholmRowUnitaryPullback 1 - star (oddFredholmRowUnitaryPullback 1)) * _ = 0
    rw [he, oddKTheoryRowSignOperator_star, sub_self, zero_mul]
  · intro a
    change (oddFredholmRowUnitaryPullback 1 * oddFredholmRowUnitaryPullback 1 - 1) * _ = 0
    rw [he, oddKTheoryRowSignOperator_square, sub_self, zero_mul]
  · intro a
    rw [scalarModuleRepresentation_eq_smul_one, mul_smul_comm, smul_mul_assoc,
      mul_one, one_mul, sub_self]
  · intro g a
    have hg : g = 1 := Subsingleton.elim g 1
    subst g
    change (EquivariantHilbertModule.trivial.conjugateOperator 1 _ - _) * _ = 0
    have htriv : EquivariantHilbertModule.trivial.conjugateOperator 1
        (oddFredholmRowUnitaryPullback (1 : unitary (AdjointableMap B E E))) =
          oddFredholmRowUnitaryPullback 1 := by ext x; rfl
    rw [htriv, sub_self, zero_mul]

end BC4lean.KKTheory
