import BC4lean.OddFredholmStandardUnitaryPathIndex
import BC4lean.OddKTheorySignedCoordinates
import BC4lean.DoubledAdjointableUnitaryPath
import BC4lean.KasparovHomotopyDirectSum

/-! # Actual identity augmentation of the standard odd index

The checked standard self-absorption uses even and odd coefficient coordinates.
The finite corner of the first copy therefore becomes the explicit even corner
of the first 2n coordinates. Its genuine finite matrix is a finite permutation
of the old matrix plus an identity block. The compact polar path reduces an
arbitrary compact standard unitary to this calculation.
-/

noncomputable section
namespace BC4lean.KKTheory
open unitInterval
open scoped CStarAlgebra
open BC4lean.OperatorKTheory

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

local instance oddContinuationOddFredholmIdentityAugmentationLocalInstance01 : PartialOrder (Unitization ℂ B) := CStarAlgebra.spectralOrder _
local instance oddContinuationOddFredholmIdentityAugmentationLocalInstance02 : StarOrderedRing (Unitization ℂ B) := CStarAlgebra.spectralOrderedRing _
local instance oddContinuationOddFredholmIdentityAugmentationLocalInstance03 : PartialOrder (OddFredholmStandardOperator B) := CStarAlgebra.spectralOrder _
local instance oddContinuationOddFredholmIdentityAugmentationLocalInstance04 : StarOrderedRing (OddFredholmStandardOperator B) := CStarAlgebra.spectralOrderedRing _

/-- The actual two-copy module unitary sends its first copy to even coordinates. -/
theorem oddFredholmSelfAbsorption_inl (i : ℕ) (b : Bᵐᵒᵖ) :
    standardCountableSelfAbsorption (B := B) (sumMk (standardCountableInclusion i b) 0) =
      standardCountableInclusion (2 * i) b := by
  change standardCountableInterleave Equiv.natSumNatEquivNat _ = _
  simp only [standardCountableInterleave_apply, sumMk_fst, sumMk_snd, map_zero,
    add_zero, standardCountableEmbedding_inclusion]
  rfl

/-- The second copy occupies odd coordinates in the completed module. -/
theorem oddFredholmSelfAbsorption_inr (i : ℕ) (b : Bᵐᵒᵖ) :
    standardCountableSelfAbsorption (B := B) (sumMk 0 (standardCountableInclusion i b)) =
      standardCountableInclusion (2 * i + 1) b := by
  change standardCountableInterleave Equiv.natSumNatEquivNat _ = _
  simp only [standardCountableInterleave_apply, sumMk_fst, sumMk_snd, map_zero,
    zero_add, standardCountableEmbedding_inclusion]
  rfl

theorem oddFredholmSelfAbsorption_symm_even (i : ℕ) (b : Bᵐᵒᵖ) :
    (standardCountableSelfAbsorption (B := B)).symm (standardCountableInclusion (2 * i) b) =
      sumMk (standardCountableInclusion i b) 0 := by
  rw [← oddFredholmSelfAbsorption_inl, HilbertModuleEquiv.symm_apply_apply]

theorem oddFredholmSelfAbsorption_symm_odd (i : ℕ) (b : Bᵐᵒᵖ) :
    (standardCountableSelfAbsorption (B := B)).symm
      (standardCountableInclusion (2 * i + 1) b) = sumMk 0 (standardCountableInclusion i b) := by
  rw [← oddFredholmSelfAbsorption_inr, HilbertModuleEquiv.symm_apply_apply]

theorem oddFredholmSelfAbsorption_evaluation_even (i : ℕ)
    (x : HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) :
    standardCountableEvaluation (2 * i) (standardCountableSelfAbsorption x) =
      standardCountableEvaluation i x.fst := by
  have h : (standardCountableSelfAbsorption (B := B)).symm.toAdjointable.comp
      (standardCountableInclusion (B := B) (2 * i)) =
        (sumInl (B := B) (E := StandardCountableHilbertModule B)
          (F := StandardCountableHilbertModule B)).comp (standardCountableInclusion (B := B) i) := by
    ext b
    exact oddFredholmSelfAbsorption_symm_even i b
  have hs := congrArg AdjointableMap.adjoint h
  have he : (standardCountableEvaluation (B := B) (2 * i)).comp
      (standardCountableSelfAbsorption (B := B)).toAdjointable =
        (standardCountableEvaluation (B := B) i).comp
          (sumFst (B := B) (E := StandardCountableHilbertModule B)
            (F := StandardCountableHilbertModule B)) := by
    simpa only [AdjointableMap.adjoint_comp, HilbertModuleEquiv.toAdjointable_adjoint,
      HilbertModuleEquiv.symm_symm, standardCountableEvaluation, sumInl_adjoint] using hs
  exact congrArg (fun T => T x) he

theorem oddFredholmSelfAbsorption_evaluation_odd (i : ℕ)
    (x : HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) :
    standardCountableEvaluation (2 * i + 1) (standardCountableSelfAbsorption x) =
      standardCountableEvaluation i x.snd := by
  have h : (standardCountableSelfAbsorption (B := B)).symm.toAdjointable.comp
      (standardCountableInclusion (B := B) (2 * i + 1)) =
        (sumInr (B := B) (E := StandardCountableHilbertModule B)
          (F := StandardCountableHilbertModule B)).comp (standardCountableInclusion (B := B) i) := by
    ext b
    exact oddFredholmSelfAbsorption_symm_odd i b
  have hs := congrArg AdjointableMap.adjoint h
  have he : (standardCountableEvaluation (B := B) (2 * i + 1)).comp
      (standardCountableSelfAbsorption (B := B)).toAdjointable =
        (standardCountableEvaluation (B := B) i).comp
          (sumSnd (B := B) (E := StandardCountableHilbertModule B)
            (F := StandardCountableHilbertModule B)) := by
    simpa only [AdjointableMap.adjoint_comp, HilbertModuleEquiv.toAdjointable_adjoint,
      HilbertModuleEquiv.symm_symm, standardCountableEvaluation, sumInr_adjoint] using hs
  exact congrArg (fun T => T x) he

/-- Adjoin the actual identity on a second standard module, then interleave. -/
def oddFredholmStandardIdentityAugmentation (U : unitary (OddFredholmStandardOperator B)) :
    unitary (OddFredholmStandardOperator B) :=
  ⟨(standardCountableSelfAbsorption (B := B)).transport
      (sumMap (B := B) (U : OddFredholmStandardOperator B) (1 : OddFredholmStandardOperator B)),
    Unitary.map_mem (standardCountableSelfAbsorption (B := B)).transportStarAlgEquiv.toStarAlgHom
      (sumMap_mem_unitary (B := B) (E := StandardCountableHilbertModule B)
        U (1 : unitary (OddFredholmStandardOperator B)))⟩

set_option maxHeartbeats 1200000 in
theorem continuous_oddFredholmStandardIdentityAugmentation :
    Continuous (oddFredholmStandardIdentityAugmentation (B := B)) := by
  have hpair : Continuous (fun U : unitary (OddFredholmStandardOperator B) =>
      ((U : OddFredholmStandardOperator B), (1 : OddFredholmStandardOperator B))) :=
    continuous_subtype_val.prodMk continuous_const
  have hsum : Continuous (fun U : unitary (OddFredholmStandardOperator B) =>
      sumMap (B := B) (U : OddFredholmStandardOperator B)
        (1 : OddFredholmStandardOperator B)) :=
    by
      let L := sumMapContinuousLinearMap (B := B) (E := StandardCountableHilbertModule B)
        (F := StandardCountableHilbertModule B) (G := StandardCountableHilbertModule B)
        (H := StandardCountableHilbertModule B)
      have hL := L.continuous.comp hpair
      change Continuous (fun U : unitary (OddFredholmStandardOperator B) =>
        sumMap (B := B) (U : OddFredholmStandardOperator B)
          (1 : OddFredholmStandardOperator B)) at hL
      exact hL
  have htransport : Continuous (fun T : AdjointableMap B
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) =>
      (standardCountableSelfAbsorption (B := B)).transport T) :=
    (StarAlgEquiv.isometry
      (standardCountableSelfAbsorption (B := B)).transportStarAlgEquiv).continuous
  apply Continuous.subtype_mk
  exact htransport.comp hsum

theorem oddFredholmStandardIdentityAugmentation_sub_one_isModuleCompact
    (U : unitary (OddFredholmStandardOperator B))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) :
    IsModuleCompact ((oddFredholmStandardIdentityAugmentation U : OddFredholmStandardOperator B) - 1) := by
  have h := (standardCountableSelfAbsorption (B := B)).transportMap_isModuleCompact
    (standardCountableSelfAbsorption (B := B)) (hU.sumMap (IsModuleCompact.zero (B := B)
      (E := StandardCountableHilbertModule B) (F := StandardCountableHilbertModule B)))
  change IsModuleCompact ((standardCountableSelfAbsorption (B := B)).transport
    (sumMap (B := B) ((U : OddFredholmStandardOperator B) - 1)
      (0 : OddFredholmStandardOperator B))) at h
  have hsum : sumMap (B := B) ((U : OddFredholmStandardOperator B) - 1)
      (0 : OddFredholmStandardOperator B) =
      sumMap (B := B) (U : OddFredholmStandardOperator B)
        (1 : OddFredholmStandardOperator B) - 1 := by
    rw [← sumMap_one, ← sumMap_sub, sub_self]
  rw [hsum, HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_one] at h
  exact h

theorem oddFredholmStandardIdentityAugmentation_even
    (U : unitary (OddFredholmStandardOperator B)) (i : ℕ) (b : Bᵐᵒᵖ) :
    (oddFredholmStandardIdentityAugmentation U : OddFredholmStandardOperator B)
      (standardCountableInclusion (2 * i) b) =
      standardCountableSelfAbsorption (sumMk ((U : OddFredholmStandardOperator B)
        (standardCountableInclusion i b)) 0) := by
  simp only [oddFredholmStandardIdentityAugmentation, HilbertModuleEquiv.transport_apply,
    oddFredholmSelfAbsorption_symm_even, sumMap_apply, sumMk_fst, sumMk_snd,
    AdjointableMap.one_apply]

theorem oddFredholmStandardIdentityAugmentation_odd
    (U : unitary (OddFredholmStandardOperator B)) (i : ℕ) (b : Bᵐᵒᵖ) :
    (oddFredholmStandardIdentityAugmentation U : OddFredholmStandardOperator B)
      (standardCountableInclusion (2 * i + 1) b) = standardCountableInclusion (2 * i + 1) b := by
  simp only [oddFredholmStandardIdentityAugmentation, HilbertModuleEquiv.transport_apply,
    oddFredholmSelfAbsorption_symm_odd, sumMap_apply, sumMk_fst, sumMk_snd, map_zero,
    AdjointableMap.one_apply, oddFredholmSelfAbsorption_inr]

/-- The finite permutation is the restriction of the actual even/odd interleave. -/
def oddFredholmEvenOddFinEquiv (n : ℕ) : Fin n ⊕ Fin n ≃ Fin (2 * n) where
  toFun := Sum.elim (fun i => ⟨2 * i.val, by omega⟩) (fun i => ⟨2 * i.val + 1, by omega⟩)
  invFun k := if h : k.val % 2 = 0 then Sum.inl ⟨k.val / 2, by omega⟩
    else Sum.inr ⟨k.val / 2, by omega⟩
  left_inv i := by
    cases i with
    | inl i =>
      dsimp only [Sum.elim]
      rw [dif_pos (show (2 * i.val) % 2 = 0 by omega)]
      apply congrArg Sum.inl
      apply Fin.ext
      dsimp only
      omega
    | inr i =>
      dsimp only [Sum.elim]
      rw [dif_neg (show (2 * i.val + 1) % 2 ≠ 0 by omega)]
      apply congrArg Sum.inr
      apply Fin.ext
      dsimp only
      omega
  right_inv k := by
    dsimp only
    split_ifs with h <;> apply Fin.ext <;> dsimp <;> omega

theorem oddFredholmStandardIdentityAugmentation_tail
    (U : unitary (OddFredholmStandardOperator B)) (n : ℕ)
    (hU : (U : OddFredholmStandardOperator B) * (1 - standardCountableCutoff n) =
      1 - standardCountableCutoff n) :
    (oddFredholmStandardIdentityAugmentation U : OddFredholmStandardOperator B) *
      (1 - standardCountableCutoff (2 * n)) = 1 - standardCountableCutoff (2 * n) := by
  apply oddKTheoryOperator_ext_coordinates
  intro k b
  obtain ⟨i | i, rfl⟩ := Equiv.natSumNatEquivNat.surjective k
  · change ((oddFredholmStandardIdentityAugmentation U : OddFredholmStandardOperator B) *
        (1 - standardCountableCutoff (B := B) (2 * n)))
        (standardCountableInclusion (B := B) (2 * i) b) =
      (1 - standardCountableCutoff (B := B) (2 * n) : OddFredholmStandardOperator B)
        (standardCountableInclusion (B := B) (2 * i) b)
    by_cases hi : i < n
    · simp only [AdjointableMap.mul_apply, AdjointableMap.coe_sub_apply,
        AdjointableMap.one_apply, oddFredholmStandardCutoff_inclusion,
        if_pos (by omega : 2 * i < 2 * n), sub_self, map_zero]
    · have hit : n ≤ i := Nat.le_of_not_gt hi
      simp only [AdjointableMap.mul_apply, AdjointableMap.coe_sub_apply,
        AdjointableMap.one_apply, oddFredholmStandardCutoff_inclusion,
        if_neg (by omega : ¬2 * i < 2 * n), sub_zero]
      rw [oddFredholmStandardIdentityAugmentation_even,
        oddFredholmSupportedUnitary_inclusion_tail U n hU hit, oddFredholmSelfAbsorption_inl]
  · change ((oddFredholmStandardIdentityAugmentation U : OddFredholmStandardOperator B) *
        (1 - standardCountableCutoff (B := B) (2 * n)))
        (standardCountableInclusion (B := B) (2 * i + 1) b) =
      (1 - standardCountableCutoff (B := B) (2 * n) : OddFredholmStandardOperator B)
        (standardCountableInclusion (B := B) (2 * i + 1) b)
    by_cases hi : i < n
    · simp only [AdjointableMap.mul_apply, AdjointableMap.coe_sub_apply,
        AdjointableMap.one_apply, oddFredholmStandardCutoff_inclusion,
        if_pos (by omega : 2 * i + 1 < 2 * n), sub_self, map_zero]
    · simp only [AdjointableMap.mul_apply, AdjointableMap.coe_sub_apply,
        AdjointableMap.one_apply, oddFredholmStandardCutoff_inclusion,
        if_neg (by omega : ¬2 * i + 1 < 2 * n), sub_zero,
        oddFredholmStandardIdentityAugmentation_odd]

/-- A supported compact unitary's chosen index is exactly its genuine finite matrix. -/
theorem oddFredholmStandardUnitaryIndex_eq_supported
    (U : unitary (OddFredholmStandardOperator B))
    (hCompact : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) (n : ℕ)
    (hU : (U : OddFredholmStandardOperator B) * (1 - standardCountableCutoff n) =
      1 - standardCountableCutoff n) :
    oddFredholmStandardUnitaryIndex U hCompact =
      oddFredholmScalarIdentityUnitaryIndex (oddFredholmSupportedFiniteUnitary U hCompact n hU)
        (oddFredholmSupportedFiniteUnitary_scalar U hCompact n hU) := by
  have hcut : oddFredholmUnitaryCutoff U n = (U : OddFredholmStandardOperator B) := by
    have hs : (U : OddFredholmStandardOperator B) - 1 =
        standardCountableCutoff n * ((U : OddFredholmStandardOperator B) - 1) * standardCountableCutoff n := by
      have hr : ((U : OddFredholmStandardOperator B) - 1) * (1 - standardCountableCutoff n) = 0 := by
        rw [sub_mul, hU, one_mul, sub_self]
      have hl : (1 - standardCountableCutoff n) * ((U : OddFredholmStandardOperator B) - 1) = 0 := by
        rw [mul_sub, oddFredholmUnitary_left_tail U _
          (by rw [star_sub, star_one, standardCountableCutoff_star]) hU, mul_one, sub_self]
      rw [mul_sub, mul_one] at hr
      rw [sub_mul, one_mul] at hl
      rw [← sub_eq_zero.mp hl, ← sub_eq_zero.mp hr]
    unfold oddFredholmUnitaryCutoff
    rw [← hs]
    abel
  have hn : ‖oddFredholmUnitaryCutoff U n - (U : OddFredholmStandardOperator B)‖ < 1 := by
    rw [hcut, sub_self, norm_zero]
    exact zero_lt_one
  rw [oddFredholmStandardUnitaryIndex_eq_cutoff U hCompact n hn]
  have hp : oddFredholmStandardCutoffPolarUnitary U n hn = U := by
    apply Subtype.ext
    change oddFredholmPolarElement (oddFredholmUnitaryCutoff U n) = (U : _)
    rw [hcut, oddFredholmPolarElement_unitary]
  apply Subtype.ext
  congr 2
  simp only [oddFredholmStandardFiniteIndexUnitary, oddFredholmStandardFinitePolarUnitary,
    oddFredholmSupportedFiniteUnitary, oddFredholmSupportedUnitaryCompression, hp]

theorem oddFredholmIdentityAugmentationFiniteUnitary
    (U : unitary (OddFredholmStandardOperator B))
    (hc : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) (n : ℕ)
    (hU : (U : OddFredholmStandardOperator B) * (1 - standardCountableCutoff n) =
      1 - standardCountableCutoff n) :
    oddFredholmSupportedFiniteUnitary (oddFredholmStandardIdentityAugmentation U)
      (oddFredholmStandardIdentityAugmentation_sub_one_isModuleCompact U hc) (2 * n)
      (oddFredholmStandardIdentityAugmentation_tail U n hU) =
      unitaryReindex (oddFredholmEvenOddFinEquiv n) (unitaryBlockSum
        (oddFredholmSupportedFiniteUnitary U hc n hU)
        (1 : unitary (CStarMatrix (Fin n) (Fin n) (Unitization ℂ B)))) := by
  apply Subtype.ext
  apply CStarMatrix.ext
  intro i j
  obtain ⟨i, rfl⟩ := (oddFredholmEvenOddFinEquiv n).surjective i
  obtain ⟨j, rfl⟩ := (oddFredholmEvenOddFinEquiv n).surjective j
  apply oddFredholmUnitization_eq_of_scalar_and_left_action
  · have hs := oddFredholmSupportedFiniteUnitary_scalar (oddFredholmStandardIdentityAugmentation U)
      (oddFredholmStandardIdentityAugmentation_sub_one_isModuleCompact U hc) (2 * n)
      (oddFredholmStandardIdentityAugmentation_tail U n hU)
    have hu := oddFredholmSupportedFiniteUnitary_scalar U hc n hU
    have hh (a b : Fin n) : ((oddFredholmSupportedFiniteUnitary U hc n hU :
        CStarMatrix (Fin n) (Fin n) (Unitization ℂ B)) a b).fst = if a = b then 1 else 0 := by
      simpa only [unitizationScalarMatrix_apply, CStarMatrix.one_apply] using
        congrArg (fun M : CStarMatrix (Fin n) (Fin n) ℂ => M a b) hu
    have he := congrArg (fun M : CStarMatrix (Fin (2 * n)) (Fin (2 * n)) ℂ =>
      M (oddFredholmEvenOddFinEquiv n i) (oddFredholmEvenOddFinEquiv n j)) hs
    simp only [unitizationScalarMatrix_apply, CStarMatrix.one_apply,
      Equiv.apply_eq_iff_eq] at he
    rw [he, unitaryReindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change (if (Sum.inl i : Fin n ⊕ Fin n) = Sum.inl j then 1 else 0) =
          ((oddFredholmSupportedFiniteUnitary U hc n hU :
            CStarMatrix (Fin n) (Fin n) (Unitization ℂ B)) i j).fst
        simpa only [Sum.inl.injEq] using (hh i j).symm
      | inr j =>
        change (if (Sum.inl i : Fin n ⊕ Fin n) = Sum.inr j then 1 else 0) =
          (0 : Unitization ℂ B).fst
        simp only [reduceCtorEq, if_false, Unitization.fst_zero]
    | inr i =>
      cases j with
      | inl j =>
        change (if (Sum.inr i : Fin n ⊕ Fin n) = Sum.inl j then 1 else 0) =
          (0 : Unitization ℂ B).fst
        simp only [reduceCtorEq, if_false, Unitization.fst_zero]
      | inr j =>
        change (if (Sum.inr i : Fin n ⊕ Fin n) = Sum.inr j then 1 else 0) =
          ((1 : CStarMatrix (Fin n) (Fin n) (Unitization ℂ B)) i j).fst
        rw [CStarMatrix.one_apply]
        by_cases hij : i = j
        · simp only [Sum.inr.injEq, if_pos hij, Unitization.fst_one]
        · simp only [Sum.inr.injEq, if_neg hij, Unitization.fst_zero]
  · ext b
    rw [oddFredholmSupportedFiniteUnitary_entry_action]
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change standardCountableEvaluation (2 * i.val)
          ((oddFredholmStandardIdentityAugmentation U : OddFredholmStandardOperator B)
            (standardCountableInclusion (2 * j.val) b)) = _
        rw [oddFredholmStandardIdentityAugmentation_even, oddFredholmSelfAbsorption_evaluation_even,
          unitaryReindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        change standardCountableEvaluation i.val ((U : OddFredholmStandardOperator B)
          (standardCountableInclusion j.val b)) = unitizedStandardLeftMul
            ((oddFredholmSupportedFiniteUnitary U hc n hU :
              CStarMatrix (Fin n) (Fin n) (Unitization ℂ B)) i j) b
        exact (oddFredholmSupportedFiniteUnitary_entry_action U hc n hU i j b).symm
      | inr j =>
        change standardCountableEvaluation (2 * i.val)
          ((oddFredholmStandardIdentityAugmentation U : OddFredholmStandardOperator B)
            (standardCountableInclusion (2 * j.val + 1) b)) = _
        rw [oddFredholmStandardIdentityAugmentation_odd, unitaryReindex_apply,
          Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        change standardCountableEvaluation (2 * i.val)
          (standardCountableInclusion (2 * j.val + 1) b) =
            unitizedStandardLeftMul (0 : Unitization ℂ B) b
        rw [standardCountableEvaluation_inclusion,
          if_neg (show 2 * j.val + 1 ≠ 2 * i.val by omega), map_zero,
          AdjointableMap.coe_zero_apply]
    | inr i =>
      cases j with
      | inl j =>
        change standardCountableEvaluation (2 * i.val + 1)
          ((oddFredholmStandardIdentityAugmentation U : OddFredholmStandardOperator B)
            (standardCountableInclusion (2 * j.val) b)) = _
        rw [oddFredholmStandardIdentityAugmentation_even, oddFredholmSelfAbsorption_evaluation_odd,
          unitaryReindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        change standardCountableEvaluation i.val (0 : StandardCountableHilbertModule B) =
          unitizedStandardLeftMul (0 : Unitization ℂ B) b
        simp only [map_zero, AdjointableMap.coe_zero_apply]
      | inr j =>
        change standardCountableEvaluation (2 * i.val + 1)
          ((oddFredholmStandardIdentityAugmentation U : OddFredholmStandardOperator B)
            (standardCountableInclusion (2 * j.val + 1) b)) = _
        rw [oddFredholmStandardIdentityAugmentation_odd, unitaryReindex_apply,
          Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        change standardCountableEvaluation (2 * i.val + 1)
          (standardCountableInclusion (2 * j.val + 1) b) =
            unitizedStandardLeftMul
              ((1 : CStarMatrix (Fin n) (Fin n) (Unitization ℂ B)) i j) b
        rw [standardCountableEvaluation_inclusion, CStarMatrix.one_apply]
        by_cases hij : i = j
        · subst j
          simp only [if_true, map_one, AdjointableMap.one_apply]
        · have hne : 2 * j.val + 1 ≠ 2 * i.val + 1 := by
            intro he
            apply hij
            apply Fin.ext
            omega
          simp only [if_neg hne, if_neg hij, map_zero, AdjointableMap.coe_zero_apply]

theorem oddFredholmStandardUnitaryIndex_identityAugmentation_supported
    (U : unitary (OddFredholmStandardOperator B))
    (hc : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) (n : ℕ)
    (hU : (U : OddFredholmStandardOperator B) * (1 - standardCountableCutoff n) =
      1 - standardCountableCutoff n) :
    oddFredholmStandardUnitaryIndex (oddFredholmStandardIdentityAugmentation U)
      (oddFredholmStandardIdentityAugmentation_sub_one_isModuleCompact U hc) =
      oddFredholmStandardUnitaryIndex U hc := by
  rw [oddFredholmStandardUnitaryIndex_eq_supported _ _ (2 * n)
      (oddFredholmStandardIdentityAugmentation_tail U n hU),
    oddFredholmStandardUnitaryIndex_eq_supported U hc n hU]
  apply Subtype.ext
  change K1.of (FiniteUnitary.ofUnitary _) = K1.of (FiniteUnitary.ofUnitary _)
  rw [oddFredholmIdentityAugmentationFiniteUnitary U hc n hU]
  calc
    _ = K1.of (FiniteUnitary.ofUnitary (unitaryBlockSum (oddFredholmSupportedFiniteUnitary U hc n hU)
        (1 : unitary (CStarMatrix (Fin n) (Fin n) (Unitization ℂ B))))) := by
      apply Quotient.sound
      apply FiniteUnitary.equivalent_symm
      exact FiniteUnitary.equivalent_reindex _ _ (oddFredholmEvenOddFinEquiv n) rfl
    _ = _ := by
      change K1.of (FiniteUnitary.blockSum
        (FiniteUnitary.ofUnitary (oddFredholmSupportedFiniteUnitary U hc n hU))
        (FiniteUnitary.identity (A := Unitization ℂ B) (Fin n))) =
        K1.of (FiniteUnitary.ofUnitary (oddFredholmSupportedFiniteUnitary U hc n hU))
      exact K1.of_stabilize
        (FiniteUnitary.ofUnitary (oddFredholmSupportedFiniteUnitary U hc n hU)) (Fin n)

/-- Identity augmentation preserves the chosen genuine OperatorK1 index of
every compact standard-module unitary. No absorption-independence hypothesis
is used: the assertion follows from the actual polar path and finite entries. -/
theorem oddFredholmStandardUnitaryIndex_identityAugmentation
    (U : unitary (OddFredholmStandardOperator B))
    (hc : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) :
    oddFredholmStandardUnitaryIndex (oddFredholmStandardIdentityAugmentation U)
      (oddFredholmStandardIdentityAugmentation_sub_one_isModuleCompact U hc) =
      oddFredholmStandardUnitaryIndex U hc := by
  let n := oddFredholmStandardIndexSize U hc
  have hn := oddFredholmStandardIndexSize_near U hc
  let p := oddFredholmPolarInterpolation U (oddFredholmUnitaryCutoff U n) hn
  have hp (t : I) : IsModuleCompact ((p t : OddFredholmStandardOperator B) - 1) :=
    oddFredholmPolarInterpolation_sub_one_isModuleCompact U _ hn hc
      (oddFredholmUnitaryCutoff_sub_one_isModuleCompact U hc n) t
  let q : Path (oddFredholmStandardIdentityAugmentation U)
      (oddFredholmStandardIdentityAugmentation (oddFredholmStandardCutoffPolarUnitary U n hn)) :=
    { toFun t := oddFredholmStandardIdentityAugmentation (p t)
      continuous_toFun := continuous_oddFredholmStandardIdentityAugmentation.comp p.continuous
      source' := by rw [Path.source]
      target' := by rw [Path.target]; rfl }
  have hq := oddFredholmStandardUnitaryIndex_path q
    (fun t => oddFredholmStandardIdentityAugmentation_sub_one_isModuleCompact (p t) (hp t))
  have he := oddFredholmStandardUnitaryIndex_identityAugmentation_supported
    (oddFredholmStandardCutoffPolarUnitary U n hn)
    (oddFredholmStandardCutoffPolarUnitary_sub_one_isModuleCompact U hc n hn) n
    (oddFredholmStandardCutoffPolarUnitary_right_tail U n hn)
  have hi := oddFredholmStandardUnitaryIndex_path p hp
  exact hq.trans (he.trans hi.symm)

end BC4lean.KKTheory
