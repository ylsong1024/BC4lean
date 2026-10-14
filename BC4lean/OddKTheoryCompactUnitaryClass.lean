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

omit [CompleteSpace E] [CompleteSpace F] [TopologicalSpace.SeparableSpace B] in
theorem oddKTheorySumOperatorUnitary_compact
    (U : unitary (AdjointableMap B E E)) (V : unitary (AdjointableMap B F F))
    (hU : IsModuleCompact ((U : AdjointableMap B E E) - 1))
    (hV : IsModuleCompact ((V : AdjointableMap B F F) - 1)) :
    IsModuleCompact ((oddKTheorySumOperatorUnitary U V :
      AdjointableMap B (HilbertModuleSum B E F) (HilbertModuleSum B E F)) - 1) := by
  change IsModuleCompact (sumMap (U : AdjointableMap B E E) (V : AdjointableMap B F F) - 1)
  simpa only [sumMap_sub, sumMap_one] using hU.sumMap hV

set_option maxHeartbeats 4000000 in
omit [TopologicalSpace.SeparableSpace B] in
theorem oddKTheoryCircleCFC_sumOperatorUnitary
    (U : unitary (AdjointableMap B E E)) (V : unitary (AdjointableMap B F F)) :
    oddKTheoryCircleCFC (A := AdjointableMap B (HilbertModuleSum B E F) (HilbertModuleSum B E F))
      (oddKTheorySumOperatorUnitary (B := B) (E := E) (F := F) U V) =
      oddKTheoryCircleSumHom (B := B) (E := E) (F := F) (oddKTheoryCircleCFC (A := AdjointableMap B E E) U) (oddKTheoryCircleCFC (A := AdjointableMap B F F) V) := by
  apply ContinuousMap.UniqueHom.eq_of_continuous_of_map_id (R := ℂ)
    (A := AdjointableMap B (HilbertModuleSum B E F) (HilbertModuleSum B E F)) (Metric.sphere (0 : ℂ) 1)
    (oddKTheoryCircleCFC (A := AdjointableMap B (HilbertModuleSum B E F) (HilbertModuleSum B E F))
      (oddKTheorySumOperatorUnitary (B := B) (E := E) (F := F) U V))
    (oddKTheoryCircleSumHom (B := B) (E := E) (F := F) (oddKTheoryCircleCFC (A := AdjointableMap B E E) U) (oddKTheoryCircleCFC (A := AdjointableMap B F F) V))
    (continuous_oddKTheoryCircleCFC (A := AdjointableMap B (HilbertModuleSum B E F) (HilbertModuleSum B E F))
      (oddKTheorySumOperatorUnitary (B := B) (E := E) (F := F) U V))
    (map_continuous (oddKTheoryCircleSumHom (B := B) (E := E) (F := F) (oddKTheoryCircleCFC (A := AdjointableMap B E E) U) (oddKTheoryCircleCFC (A := AdjointableMap B F F) V)))
  change oddKTheoryCircleCFC
      (A := AdjointableMap B (HilbertModuleSum B E F) (HilbertModuleSum B E F))
      (oddKTheorySumOperatorUnitary (B := B) (E := E) (F := F) U V)
      ((ContinuousMap.id ℂ).restrict (Metric.sphere 0 1)) =
    sumMap (oddKTheoryCircleCFC (A := AdjointableMap B E E) U
      ((ContinuousMap.id ℂ).restrict (Metric.sphere 0 1)))
      (oddKTheoryCircleCFC (A := AdjointableMap B F F) V
        ((ContinuousMap.id ℂ).restrict (Metric.sphere 0 1)))
  have hsum := oddKTheoryCircleCFC_coordinate
    (A := AdjointableMap B (HilbertModuleSum B E F) (HilbertModuleSum B E F))
    (oddKTheorySumOperatorUnitary (B := B) (E := E) (F := F) U V)
  have hUcoord := oddKTheoryCircleCFC_coordinate (A := AdjointableMap B E E) U
  have hVcoord := oddKTheoryCircleCFC_coordinate (A := AdjointableMap B F F) V
  exact hsum.trans (congrArg₂ (fun (S : AdjointableMap B E E) (T : AdjointableMap B F F) =>
    sumMap S T) hUcoord.symm hVcoord.symm)

def oddKTheoryTransportOperatorUnitary (e : HilbertModuleEquiv B E F)
    (U : unitary (AdjointableMap B E E)) : unitary (AdjointableMap B F F) :=
  ⟨e.transport U, Unitary.map_mem e.transportStarAlgEquiv.toStarAlgHom U.property⟩

omit [CompleteSpace E] [CompleteSpace F] [TopologicalSpace.SeparableSpace B] in
theorem oddKTheoryTransportOperatorUnitary_compact (e : HilbertModuleEquiv B E F)
    (U : unitary (AdjointableMap B E E))
    (hU : IsModuleCompact ((U : AdjointableMap B E E) - 1)) :
    IsModuleCompact ((oddKTheoryTransportOperatorUnitary e U : AdjointableMap B F F) - 1) := by
  change IsModuleCompact (e.transport (U : AdjointableMap B E E) - 1)
  have h := e.transportMap_isModuleCompact e hU
  change IsModuleCompact (e.transport ((U : AdjointableMap B E E) - 1)) at h
  simpa only [HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_one] using h

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
    change oddKTheoryCountableRowEquiv e (oddFredholmRowUnitaryPullback U x) =
      oddFredholmRowUnitaryPullback (oddKTheoryTransportOperatorUnitary e U)
        (oddKTheoryCountableRowEquiv e x)
    have ht := oddFredholmRowUnitaryPullback_transport e U
    have hh := congrArg (fun T => T (oddKTheoryCountableRowEquiv e x)) ht
    change oddKTheoryCountableRowEquiv e (oddFredholmRowUnitaryPullback U x) =
      oddFredholmRowUnitaryPullback (oddFredholmEquivUnitary e U)
        (oddKTheoryCountableRowEquiv e x)
    simpa only [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply] using hh

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
  moduleEquiv := oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)
  action_intertwine _ _ := rfl
  representation_intertwine a x := by
    change (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F))
        (scalarModuleRepresentation (B := B)
          (E := CountableHilbertModuleSum B (HilbertModuleSum B E F)) a x) =
      sumMap (scalarModuleRepresentation (B := B) (E := CountableHilbertModuleSum B E) a)
        (scalarModuleRepresentation (B := B) (E := CountableHilbertModuleSum B F) a)
        ((oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)) x)
    simp only [scalarModuleRepresentation_eq_smul_one, sumMap_smul, sumMap_one]
    change (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)) (a • x) =
      a • (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)) x
    exact (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).map_smul a x
  operator_intertwine x := by
    change (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F))
        (oddFredholmRowUnitaryPullback (oddKTheorySumOperatorUnitary U V) x) =
      sumMap (oddFredholmRowUnitaryPullback U) (oddFredholmRowUnitaryPullback V)
        ((oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)) x)
    have ht := oddKTheoryRowSumSplit_transport_formula (oddKTheoryCircleCFC U) (oddKTheoryCircleCFC V)
    rw [← oddKTheoryCircleCFC_sumOperatorUnitary U V] at ht
    have hh := congrArg (fun T => T ((oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)) x)) ht
    change (oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)).transport
        (oddFredholmRowUnitaryPullback (oddKTheorySumOperatorUnitary U V))
        ((oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)) x) =
      sumMap (oddFredholmRowUnitaryPullback U) (oddFredholmRowUnitaryPullback V)
        ((oddKTheoryCountableSumEquiv (B := B) (E := E) (F := F)) x) at hh
    simpa only [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply] using hh

omit [TopologicalSpace.SeparableSpace B] in
theorem oddKTheoryCompactUnitaryPullbackCycle_one_degenerate (hE : IsCountablyGeneratedModule B E) :
    (oddFredholmCompactUnitaryPullbackCycle (Γ := PUnit) hE (1 : unitary (AdjointableMap B E E))
      (by simpa only [OneMemClass.coe_one, sub_self] using
        (IsModuleCompact.zero : IsModuleCompact (0 : AdjointableMap B E E)))).IsDegenerate := by
  have he : oddFredholmRowUnitaryPullback (1 : unitary (AdjointableMap B E E)) =
      oddKTheoryRowSignOperator := by
    have hdiag0 : countableModuleDiagonal (0 : AdjointableMap B E E) =
        (0 : OddKTheoryCountableOperator B E) :=
      (oddKTheoryCountableDiagonalHom (B := B) (E := E)).map_zero
    unfold oddFredholmRowUnitaryPullback oddKTheoryFiniteRowFormula
    simp only [Fintype.sum_sum_type, oddKTheoryLoopTermCoefficient,
      oddKTheoryRowLoopTermOperator, Fintype.sum_unique, oddKTheoryCircleCFC_one_algebraMap,
      oddKTheoryLoopResidualCircleCoefficient_one, oddKTheoryLoopSignCircleCoefficient_one,
      oddKTheoryLoopFiniteCircleCoefficient_one, map_zero, map_one,
      hdiag0, oddKTheoryCountableDiagonal_one, Finset.sum_const_zero, zero_mul, one_mul, zero_add, add_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    change (oddFredholmRowUnitaryPullback 1 - star (oddFredholmRowUnitaryPullback 1)) * _ = 0
    rw [he, oddKTheoryRowSignOperator_star, sub_self, zero_mul]
  · intro a
    change (oddFredholmRowUnitaryPullback 1 * oddFredholmRowUnitaryPullback 1 - 1) * _ = 0
    rw [he, oddKTheoryRowSignOperator_square, sub_self, zero_mul]
  · intro a
    change oddFredholmRowUnitaryPullback (1 : unitary (AdjointableMap B E E)) *
        scalarModuleRepresentation (B := B) (E := CountableHilbertModuleSum B E) a -
      scalarModuleRepresentation (B := B) (E := CountableHilbertModuleSum B E) a *
        oddFredholmRowUnitaryPullback (1 : unitary (AdjointableMap B E E)) = 0
    rw [scalarModuleRepresentation_eq_smul_one, mul_smul_comm, smul_mul_assoc,
      mul_one, one_mul, sub_self]
  · intro g a
    change (((EquivariantHilbertModule.trivial :
        EquivariantHilbertModule (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B)
          (CountableHilbertModuleSum B E)).conjugateOperator g
            (oddFredholmRowUnitaryPullback (1 : unitary (AdjointableMap B E E))) -
          oddFredholmRowUnitaryPullback (1 : unitary (AdjointableMap B E E))) *
        scalarModuleRepresentation (B := B) (E := CountableHilbertModuleSum B E) a) = 0
    have htriv : (EquivariantHilbertModule.trivial :
        EquivariantHilbertModule (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B)
          (CountableHilbertModuleSum B E)).conjugateOperator g
            (oddFredholmRowUnitaryPullback (1 : unitary (AdjointableMap B E E))) =
          oddFredholmRowUnitaryPullback (1 : unitary (AdjointableMap B E E)) := by
      ext x
      rfl
    rw [htriv, sub_self, zero_mul]

end BC4lean.KKTheory
