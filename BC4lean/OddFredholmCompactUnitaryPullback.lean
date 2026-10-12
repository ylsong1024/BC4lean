import BC4lean.OddFredholmRowEndpoint
import BC4lean.OddFredholmCompactUnitary
import BC4lean.NonunitalOperatorK

/-! # Genuine infinite odd Fredholm cycles from arbitrary compact unitaries

The true compact-operator unitization supplies compact circle coefficients
vanishing at the base point. The actual four-entry square formula then proves
the global compact defect on the genuine completed countable row module.
This works on every complete module, including infinite H_B; no finite odd
cycle or compact coordinate projection is substituted for the inverse.
-/

noncomputable section
namespace BC4lean.KKTheory
open unitInterval
open scoped CStarAlgebra

variable {Γ B E : Type*} [Group Γ] [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

def oddFredholmCompactUnitizationAction :
    Unitization ℂ (CompactModuleOperator B E) →⋆ₐ[ℂ] AdjointableMap B E E :=
  Unitization.starLift (NonUnitalStarSubalgebraClass.subtype
    (compactModuleOperatorAlgebra (B := B) (E := E)))

theorem oddFredholmCompactUnitizationAction_unitary
    (U : unitary (AdjointableMap B E E))
    (hU : IsModuleCompact ((U : AdjointableMap B E E) - 1)) :
    oddFredholmCompactUnitizationAction (compactPerturbationUnitary U hU : _) =
      (U : AdjointableMap B E E) := by
  have hAction (x : Unitization ℂ (CompactModuleOperator B E)) :
      oddFredholmCompactUnitizationAction (B := B) (E := E) x =
        algebraMap ℂ (AdjointableMap B E E) x.fst + (x.snd : AdjointableMap B E E) := rfl
  rw [hAction, compactPerturbationUnitary_fst]
  change algebraMap ℂ (AdjointableMap B E E) 1 +
    ((compactPerturbationUnitaryElement U hU).snd : AdjointableMap B E E) = _
  rw [compactPerturbationUnitaryElement_snd, compactPerturbationUnitaryCoefficient_coe, map_one]
  abel

/-- Every actual circle coefficient vanishing at 1 is compact when evaluated
at an actual compact perturbation unitary, without a quotient identification. -/
theorem oddFredholmCircleCFC_isModuleCompact
    (U : unitary (AdjointableMap B E E))
    (hU : IsModuleCompact ((U : AdjointableMap B E E) - 1))
    (f : C(Circle, ℂ)) (hf : f 1 = 0) : IsModuleCompact (oddKTheoryCircleCFC U f) := by
  let v : unitary (Unitization ℂ (CompactModuleOperator B E)) :=
    compactPerturbationUnitary U hU
  have hm := oddKTheoryCircleCFC_map
    (oddFredholmCompactUnitizationAction (B := B) (E := E))
    (map_continuous _) v U (oddFredholmCompactUnitizationAction_unitary U hU) f
  have hAction (x : Unitization ℂ (CompactModuleOperator B E)) :
      oddFredholmCompactUnitizationAction (B := B) (E := E) x =
        algebraMap ℂ (AdjointableMap B E E) x.fst + (x.snd : AdjointableMap B E E) := rfl
  rw [← hm, oddKTheoryCircleCFC_eq_coefficient (B := CompactModuleOperator B E)
    v (compactPerturbationUnitary_fst U hU) f hf, hAction,
    Unitization.fst_inr, Unitization.snd_inr, map_zero, zero_add]
  exact (oddKTheoryCircleCFCCoefficient (B := CompactModuleOperator B E) v f).property

private theorem oddFredholmPullbackResidual_sum_swap {R : Type*} [AddCommMonoid R]
    (f : Fin 4 × Fin 4 → R) :
    (∑ p : Fin 4 × Fin 4, f p.swap) = ∑ p : Fin 4 × Fin 4, f p :=
  (Equiv.prodComm (Fin 4) (Fin 4)).sum_comp f

private theorem oddFredholmPullbackFinite_sum_adjoint {R : Type*} [AddCommMonoid R]
    (f : Fin 4 → R) :
    (∑ i : Fin 4, f (oddKTheoryFiniteEntryAdjoint i)) = ∑ i : Fin 4, f i :=
  oddKTheoryFiniteEntryAdjoint.sum_comp f

set_option maxHeartbeats 1200000 in
theorem oddFredholmRowUnitaryPullback_isSelfAdjoint (U : unitary (AdjointableMap B E E)) :
    IsSelfAdjoint (oddFredholmRowUnitaryPullback U) := by
  let φ : C(Circle, ℂ) →⋆ₐ[ℂ] OddKTheoryCountableOperator B E :=
    (oddKTheoryCountableDiagonalHom (B := B) (E := E)).comp (oddKTheoryCircleCFC U)
  let residual : Fin 4 × Fin 4 → OddKTheoryCountableOperator B E := fun p =>
    φ (oddKTheoryLoopResidualCircleCoefficient p) *
      oddKTheoryRowLoopFixedOperator (B := B) (E := E) p
  let finite : Fin 4 → OddKTheoryCountableOperator B E := fun i =>
    φ (oddKTheoryLoopFiniteCircleCoefficient i) *
      oddKTheoryRowLoopFixedFiniteOperator (B := B) (E := E) i
  let rowAdd : AddCommMonoid (OddKTheoryCountableOperator B E) := inferInstance
  have hresidualReindex : (∑ p : Fin 4 × Fin 4, residual p.swap) =
      ∑ p : Fin 4 × Fin 4, residual p :=
    @oddFredholmPullbackResidual_sum_swap (OddKTheoryCountableOperator B E) rowAdd residual
  have hfiniteReindex : (∑ i : Fin 4, finite (oddKTheoryFiniteEntryAdjoint i)) =
      ∑ i : Fin 4, finite i :=
    @oddFredholmPullbackFinite_sum_adjoint (OddKTheoryCountableOperator B E) rowAdd finite
  have hresidualStarToSwap : star (∑ p : Fin 4 × Fin 4, residual p) =
      ∑ p : Fin 4 × Fin 4, residual p.swap := by
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro p _
    dsimp only [residual]
    rw [star_mul, ← map_star, oddKTheoryLoopResidualCircleCoefficient_star,
      oddKTheoryRowLoopFixedOperator_star]
    dsimp only [φ, StarAlgHom.comp_apply, oddKTheoryCountableDiagonalHom]
    exact (oddKTheoryRowLoopFixedOperator_diagonal_commute (B := B) (E := E) p.swap
      (oddKTheoryCircleCFC U (oddKTheoryLoopResidualCircleCoefficient p.swap))).eq
  have hr : star (∑ p : Fin 4 × Fin 4, residual p) = ∑ p : Fin 4 × Fin 4, residual p :=
    hresidualStarToSwap.trans hresidualReindex
  have hfiniteStarToAdjoint : star (∑ i : Fin 4, finite i) =
      ∑ i : Fin 4, finite (oddKTheoryFiniteEntryAdjoint i) := by
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [finite]
    rw [star_mul, ← map_star, oddKTheoryLoopFiniteCircleCoefficient_star,
      oddKTheoryRowLoopFixedFiniteOperator_star]
    dsimp only [φ, StarAlgHom.comp_apply, oddKTheoryCountableDiagonalHom]
    exact (oddKTheoryRowLoopFixedFiniteOperator_diagonal_commute (B := B) (E := E)
      (oddKTheoryFiniteEntryAdjoint i) (oddKTheoryCircleCFC U
        (oddKTheoryLoopFiniteCircleCoefficient (oddKTheoryFiniteEntryAdjoint i)))).eq
  have hf : star (∑ i : Fin 4, finite i) = ∑ i : Fin 4, finite i :=
    hfiniteStarToAdjoint.trans hfiniteReindex
  have hs : star (φ oddKTheoryLoopSignCircleCoefficient *
      oddKTheoryRowSignOperator (B := B) (E := E)) =
      φ oddKTheoryLoopSignCircleCoefficient * oddKTheoryRowSignOperator (B := B) (E := E) := by
    rw [star_mul, ← map_star, oddKTheoryLoopSignCircleCoefficient_star, oddKTheoryRowSignOperator_star]
    dsimp only [φ, StarAlgHom.comp_apply, oddKTheoryCountableDiagonalHom]
    exact (oddKTheoryRowSign_diagonal_commute (B := B) (E := E)
      (oddKTheoryCircleCFC U oddKTheoryLoopSignCircleCoefficient)).eq
  have he : oddFredholmRowUnitaryPullback U = (∑ p, residual p) +
      φ oddKTheoryLoopSignCircleCoefficient * oddKTheoryRowSignOperator (B := B) (E := E) +
        ∑ i, finite i := by
    unfold oddFredholmRowUnitaryPullback oddKTheoryFiniteRowFormula
    simp only [Fintype.sum_sum_type, oddKTheoryLoopTermCoefficient,
      oddKTheoryRowLoopTermOperator, Fintype.sum_unique]
    exact (add_assoc _ _ _).symm
  rw [he]
  change star ((∑ p, residual p) + φ oddKTheoryLoopSignCircleCoefficient *
    oddKTheoryRowSignOperator (B := B) (E := E) + ∑ i, finite i) = _
  rw [star_add, star_add, hr, hs, hf]

theorem oddFredholmRowUnitaryPullback_square_defect (U : unitary (AdjointableMap B E E)) :
    oddFredholmRowUnitaryPullback U * oddFredholmRowUnitaryPullback U - 1 =
      ∑ i : Fin 4, countableModuleDiagonal (oddKTheoryCircleCFC U (oddKTheoryLoopDefectCircleEntry i)) *
        oddKTheoryRowLoopFixedFiniteOperator i := by
  rw [oddFredholmRowUnitaryPullback, oddKTheoryFiniteRowFormula_loop_square]
  abel

theorem oddFredholmRowUnitaryPullback_square_isModuleCompact
    (U : unitary (AdjointableMap B E E))
    (hU : IsModuleCompact ((U : AdjointableMap B E E) - 1)) :
    IsModuleCompact (oddFredholmRowUnitaryPullback U * oddFredholmRowUnitaryPullback U - 1) := by
  rw [oddFredholmRowUnitaryPullback_square_defect]
  apply (moduleCompact B (CountableHilbertModuleSum B E) (CountableHilbertModuleSum B E)).sum_mem
  intro i _
  let S : AdjointableMap B E E := oddKTheoryCircleCFC U (oddKTheoryLoopDefectCircleEntry i)
  have hadjoint :
      (oddKTheoryRowIntegerInclusion (B := B) (E := E) (oddKTheoryLoopFiniteSource i)).adjoint =
        oddKTheoryRowIntegerEvaluation (B := B) (E := E) (oddKTheoryLoopFiniteSource i) := rfl
  have hterm : countableModuleDiagonal (B := B) (E := E) S *
      oddKTheoryRowLoopFixedFiniteOperator (B := B) (E := E) i =
      ((oddKTheoryRowIntegerInclusion (B := B) (E := E) (oddKTheoryLoopFiniteTarget i)).comp S).comp
        (oddKTheoryRowIntegerInclusion (B := B) (E := E) (oddKTheoryLoopFiniteSource i)).adjoint := by
    apply oddKTheoryRowOperator_ext_integerCoordinates (B := B) (E := E)
    intro m b
    rw [AdjointableMap.mul_apply,
      oddKTheoryRowLoopFixedFiniteOperator_coordinateRule (B := B) (E := E),
      oddKTheoryRowDiagonal_integerInclusion (B := B) (E := E),
      AdjointableMap.comp_apply, AdjointableMap.comp_apply, hadjoint,
      oddKTheoryRowIntegerEvaluation_inclusion (B := B) (E := E)]
    split_ifs <;> simp only [one_smul, zero_smul, map_zero]
  rw [hterm]
  exact ((oddFredholmCircleCFC_isModuleCompact U hU _
    (oddKTheoryLoopDefectCircleEntry_one i)).comp_left
      (oddKTheoryRowIntegerInclusion (B := B) (E := E) (oddKTheoryLoopFiniteTarget i))).comp_right
        (oddKTheoryRowIntegerInclusion (B := B) (E := E) (oddKTheoryLoopFiniteSource i)).adjoint

theorem continuous_oddFredholmRowUnitaryPullback :
    Continuous (oddFredholmRowUnitaryPullback (B := B) (E := E)) := by
  unfold oddFredholmRowUnitaryPullback oddKTheoryFiniteRowFormula
  apply continuous_finsetSum
  intro i _
  exact ((map_continuous oddKTheoryCountableDiagonalHom).comp
    (continuous_oddKTheoryCircleCFC_unitary (oddKTheoryLoopTermCoefficient i))).mul continuous_const

/-- The actual infinite scalar odd Fredholm cycle associated to any compact
perturbation unitary of a complete countably generated Hilbert B-module. -/
def oddFredholmCompactUnitaryPullbackCycle (hE : IsCountablyGeneratedModule B E)
    (U : unitary (AdjointableMap B E E))
    (hU : IsModuleCompact ((U : AdjointableMap B E E) - 1)) :
    OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B) (CountableHilbertModuleSum B E) :=
  oddKTheoryScalarFredholmCycle (Γ := Γ) (B := B) (E := CountableHilbertModuleSum B E)
    (oddKTheoryCountableModule_countablyGenerated (B := B) (E := E) hE)
    (oddFredholmRowUnitaryPullback U) (oddFredholmRowUnitaryPullback_isSelfAdjoint U)
    (oddFredholmRowUnitaryPullback_square_isModuleCompact U hU)

def oddFredholmCompactUnitaryPullbackOperatorHomotopy (hE : IsCountablyGeneratedModule B E)
    {U V : unitary (AdjointableMap B E E)} (p : Path U V)
    (hU : ∀ t : I, IsModuleCompact ((p t : AdjointableMap B E E) - 1)) :
    OddKasparovOperatorHomotopy
      (oddFredholmCompactUnitaryPullbackCycle (Γ := Γ) hE U (by simpa only [Path.source] using hU 0))
      (oddFredholmRowUnitaryPullback U) (oddFredholmRowUnitaryPullback V) where
  path :=
    { toFun t := oddFredholmRowUnitaryPullback (B := B) (E := E) (p t)
      continuous_toFun := (continuous_oddFredholmRowUnitaryPullback (B := B) (E := E)).comp p.continuous
      source' := congrArg (oddFredholmRowUnitaryPullback (B := B) (E := E)) p.source
      target' := congrArg (oddFredholmRowUnitaryPullback (B := B) (E := E)) p.target }
  conditions t := by
    constructor
    · intro a
      dsimp only [oddFredholmCompactUnitaryPullbackCycle, oddKTheoryScalarFredholmCycle]
      change IsModuleCompact ((oddFredholmRowUnitaryPullback (B := B) (E := E) (p t) -
        star (oddFredholmRowUnitaryPullback (B := B) (E := E) (p t))) *
          scalarModuleRepresentation (B := B) (E := CountableHilbertModuleSum B E) a)
      rw [(oddFredholmRowUnitaryPullback_isSelfAdjoint (B := B) (E := E) (p t)).star_eq,
        sub_self, zero_mul]
      exact IsModuleCompact.zero
    · intro a
      dsimp only [oddFredholmCompactUnitaryPullbackCycle, oddKTheoryScalarFredholmCycle]
      change IsModuleCompact ((oddFredholmRowUnitaryPullback (B := B) (E := E) (p t) *
        oddFredholmRowUnitaryPullback (B := B) (E := E) (p t) - 1) *
          scalarModuleRepresentation (B := B) (E := CountableHilbertModuleSum B E) a)
      exact (oddFredholmRowUnitaryPullback_square_isModuleCompact (B := B) (E := E)
        (p t) (hU t)).comp_right
          (scalarModuleRepresentation (B := B) (E := CountableHilbertModuleSum B E) a)
    · intro a
      dsimp only [oddFredholmCompactUnitaryPullbackCycle, oddKTheoryScalarFredholmCycle]
      change IsModuleCompact (oddFredholmRowUnitaryPullback (B := B) (E := E) (p t) *
        scalarModuleRepresentation (B := B) (E := CountableHilbertModuleSum B E) a -
        scalarModuleRepresentation (B := B) (E := CountableHilbertModuleSum B E) a *
          oddFredholmRowUnitaryPullback (B := B) (E := E) (p t))
      rw [scalarModuleRepresentation_eq_smul_one, mul_smul_comm, smul_mul_assoc,
        mul_one, one_mul, sub_self]
      exact IsModuleCompact.zero
    · intro g a
      dsimp only [oddFredholmCompactUnitaryPullbackCycle, oddKTheoryScalarFredholmCycle]
      change IsModuleCompact (((EquivariantHilbertModule.trivial :
        EquivariantHilbertModule (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B)
          (CountableHilbertModuleSum B E)).conjugateOperator g
            (oddFredholmRowUnitaryPullback (B := B) (E := E) (p t)) -
              oddFredholmRowUnitaryPullback (B := B) (E := E) (p t)) *
                scalarModuleRepresentation (B := B) (E := CountableHilbertModuleSum B E) a)
      have htriv : (EquivariantHilbertModule.trivial :
          EquivariantHilbertModule (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B)
            (CountableHilbertModuleSum B E)).conjugateOperator g
              (oddFredholmRowUnitaryPullback (B := B) (E := E) (p t)) =
                oddFredholmRowUnitaryPullback (B := B) (E := E) (p t) := by
        ext x
        rfl
      rw [htriv, sub_self, zero_mul]
      exact IsModuleCompact.zero

end BC4lean.KKTheory
