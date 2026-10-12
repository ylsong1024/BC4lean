import BC4lean.OddFredholmCutoffComparison

/-! # Actual identity stabilization of a supported finite odd compression

Enlarging the compression corner adds precisely an identity block. The proof
uses actual completed coordinate actions and the jointly faithful scalar and
coefficient representation, including nonunital and zero coefficient algebras.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped Matrix CStarAlgebra
open BC4lean.OperatorKTheory

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

local instance oddContinuationOddFredholmFiniteCompressionStabilizationLocalInstance01 : PartialOrder (Unitization ℂ B) := CStarAlgebra.spectralOrder _
local instance oddContinuationOddFredholmFiniteCompressionStabilizationLocalInstance02 : StarOrderedRing (Unitization ℂ B) := CStarAlgebra.spectralOrderedRing _

theorem oddFredholmStandardFiniteInclusion_single (n : ℕ) (i : Fin n) (b : Bᵐᵒᵖ) :
    oddFredholmStandardFiniteInclusion n (finiteStandardInclusion i b) =
      standardCountableInclusion i.val b := by
  rw [oddFredholmStandardFiniteInclusion_apply]
  have hz (j : Fin n) : standardCountableInclusion (B := B) j.val 0 = 0 :=
    (standardCountableInclusion (B := B) j.val).toCLM.map_zero
  simp only [finiteStandardInclusion_apply, finiteStandardSingle_apply, Pi.single_apply,
    apply_ite, hz, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem oddFredholmUnitizedMatrix_inclusion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : CStarMatrix ι ι (Unitization ℂ B)) (i j : ι) (b : Bᵐᵒᵖ) :
    unitizedModuleMatrixRepresentation M (finiteStandardInclusion j b) i =
      unitizedStandardLeftMul (M i j) b := by
  rw [unitizedModuleMatrixRepresentation_apply]
  simp [finiteStandardInclusion_apply, finiteStandardSingle_apply, Pi.single_apply, apply_ite]

theorem oddFredholmSupportedFiniteUnitary_entry_action
    (U : unitary (OddFredholmStandardOperator B))
    (hCompact : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) (n : ℕ)
    (hU : (U : OddFredholmStandardOperator B) * (1 - standardCountableCutoff n) =
      1 - standardCountableCutoff n) (i j : Fin n) (b : Bᵐᵒᵖ) :
    unitizedStandardLeftMul ((oddFredholmSupportedFiniteUnitary U hCompact n hU :
      CStarMatrix (Fin n) (Fin n) (Unitization ℂ B)) i j) b =
      standardCountableEvaluation i.val ((U : OddFredholmStandardOperator B)
        (standardCountableInclusion j.val b)) := by
  have h := congrArg (fun T => T (finiteStandardInclusion j b) i)
    (oddFredholmFiniteCompactUnitaryMatrix_operator
      (oddFredholmSupportedUnitaryCompression U n hU)
      (oddFredholmSupportedUnitaryCompression_sub_one_isModuleCompact U hCompact n hU))
  rw [oddFredholmUnitizedMatrix_inclusion] at h
  simpa only [oddFredholmSupportedFiniteUnitary, oddFredholmFiniteCompactUnitary,
    oddFredholmSupportedUnitaryCompression, AdjointableMap.comp_apply,
    oddFredholmStandardFiniteInclusion_single, oddFredholmStandardFiniteInclusion_adjoint_apply] using h

theorem oddFredholmStandardCutoff_inclusion (n i : ℕ) (b : Bᵐᵒᵖ) :
    standardCountableCutoff n (standardCountableInclusion i b) =
      if i < n then standardCountableInclusion i b else 0 := by
  rw [standardCountableInclusion_apply, standardCountableCutoff_mk]
  by_cases h : i < n
  · rw [Finsupp.filter_single_of_pos (fun k : ℕ => k < n) h, if_pos h]
  · rw [Finsupp.filter_single_of_neg (fun k : ℕ => k < n) h, if_neg h, map_zero]

theorem oddFredholmStandardEvaluation_cutoff_eq_zero {n i : ℕ} (hi : n ≤ i)
    (x : StandardCountableHilbertModule B) :
    standardCountableEvaluation i (standardCountableCutoff n x) = 0 := by
  rw [standardCountableCutoff_apply, map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [standardCountableEvaluation_inclusion]
  apply if_neg
  intro he
  subst j
  have hlt := Finset.mem_range.mp hj
  omega

theorem oddFredholmSupportedUnitary_inclusion_tail
    (U : unitary (OddFredholmStandardOperator B)) (n : ℕ)
    (hU : (U : OddFredholmStandardOperator B) * (1 - standardCountableCutoff n) =
      1 - standardCountableCutoff n) {i : ℕ} (hi : n ≤ i) (b : Bᵐᵒᵖ) :
    (U : OddFredholmStandardOperator B) (standardCountableInclusion i b) =
      standardCountableInclusion i b := by
  have hq : (1 - standardCountableCutoff (B := B) n) (standardCountableInclusion i b) =
      standardCountableInclusion i b := by
    rw [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply,
      oddFredholmStandardCutoff_inclusion, if_neg (Nat.not_lt.mpr hi), sub_zero]
  have h := congrArg (fun T : OddFredholmStandardOperator B => T (standardCountableInclusion i b)) hU
  simpa only [AdjointableMap.mul_apply, hq] using h

theorem oddFredholmSupportedUnitary_evaluation_tail
    (U : unitary (OddFredholmStandardOperator B)) (n : ℕ)
    (hU : (U : OddFredholmStandardOperator B) * (1 - standardCountableCutoff n) =
      1 - standardCountableCutoff n) {i : ℕ} (hi : n ≤ i)
    (x : StandardCountableHilbertModule B) :
    standardCountableEvaluation i ((U : OddFredholmStandardOperator B) x) =
      standardCountableEvaluation i x := by
  have hl := oddFredholmUnitary_left_tail U (1 - standardCountableCutoff n)
    (by rw [star_sub, star_one, standardCountableCutoff_star]) hU
  have h := congrArg (fun T : OddFredholmStandardOperator B => standardCountableEvaluation i (T x)) hl
  simpa only [AdjointableMap.mul_apply, AdjointableMap.coe_sub_apply, AdjointableMap.one_apply,
    map_sub, oddFredholmStandardEvaluation_cutoff_eq_zero hi, sub_zero] using h

theorem oddFredholmSupportedUnitary_larger_tail
    (U : unitary (OddFredholmStandardOperator B)) (n m : ℕ)
    (hU : (U : OddFredholmStandardOperator B) * (1 - standardCountableCutoff n) =
      1 - standardCountableCutoff n) :
    (U : OddFredholmStandardOperator B) * (1 - standardCountableCutoff (n + m)) =
      1 - standardCountableCutoff (n + m) := by
  have hq : (1 - standardCountableCutoff (B := B) n) *
      (1 - standardCountableCutoff (n + m)) = 1 - standardCountableCutoff (n + m) := by
    rw [sub_mul, one_mul, mul_sub, mul_one,
      oddFredholmStandardCutoff_mul_of_le (Nat.le_add_right n m)]
    abel
  calc
    _ = (U : OddFredholmStandardOperator B) *
        ((1 - standardCountableCutoff n) * (1 - standardCountableCutoff (n + m))) := by rw [hq]
    _ = ((U : OddFredholmStandardOperator B) * (1 - standardCountableCutoff n)) *
        (1 - standardCountableCutoff (n + m)) := (mul_assoc _ _ _).symm
    _ = _ := by rw [hU, hq]

theorem oddFredholmUnitization_eq_of_scalar_and_left_action
    (a b : Unitization ℂ B) (hScalar : a.fst = b.fst)
    (hAction : unitizedStandardLeftMul a = unitizedStandardLeftMul b) : a = b := by
  apply Unitization.ext hScalar
  apply sub_eq_zero.mp
  apply standardLeftMul_injective
  rw [map_zero]
  have h := unitizedStandardLeftMul_sub_of_fst_eq a b hScalar
  rw [hAction, sub_self] at h
  exact h.symm

/-- The full scalar matrix of an actual stabilized and reindexed unitary is
I whenever the original full scalar matrix is I. -/
theorem oddFredholmScalarIdentity_reindexed_stabilization (n m : ℕ)
    (v : unitary (CStarMatrix (Fin n) (Fin n) (Unitization ℂ B)))
    (hv : unitizationScalarMatrix (v : CStarMatrix (Fin n) (Fin n) (Unitization ℂ B)) = 1) :
    unitizationScalarMatrix (unitaryReindex finSumFinEquiv
      (unitaryBlockSum v (1 : unitary (CStarMatrix (Fin m) (Fin m) (Unitization ℂ B)))) :
        CStarMatrix (Fin (n + m)) (Fin (n + m)) (Unitization ℂ B)) = 1 := by
  let _retainedOriginalOrder : PartialOrder B := inferInstance
  let _retainedOriginalStarOrder : StarOrderedRing B := inferInstance
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  have hh (i j : Fin n) : ((v : CStarMatrix (Fin n) (Fin n) (Unitization ℂ B)) i j).fst =
      if i = j then 1 else 0 := by
    simpa only [unitizationScalarMatrix_apply, CStarMatrix.one_apply] using
      congrArg (fun M : CStarMatrix (Fin n) (Fin n) ℂ => M i j) hv
  simp only [unitizationScalarMatrix_apply, unitaryReindex_apply,
    Equiv.symm_apply_apply, CStarMatrix.one_apply, Equiv.apply_eq_iff_eq]
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      change ((v : CStarMatrix (Fin n) (Fin n) (Unitization ℂ B)) i j).fst =
        if (Sum.inl i : Fin n ⊕ Fin m) = Sum.inl j then 1 else 0
      simpa only [Sum.inl.injEq] using hh i j
    | inr j =>
      change (0 : Unitization ℂ B).fst =
        if (Sum.inl i : Fin n ⊕ Fin m) = Sum.inr j then 1 else 0
      simp only [reduceCtorEq, if_false, Unitization.fst_zero]
  | inr i =>
    cases j with
    | inl j =>
      change (0 : Unitization ℂ B).fst =
        if (Sum.inr i : Fin n ⊕ Fin m) = Sum.inl j then 1 else 0
      simp only [reduceCtorEq, if_false, Unitization.fst_zero]
    | inr j =>
      change ((1 : CStarMatrix (Fin m) (Fin m) (Unitization ℂ B)) i j).fst =
        if (Sum.inr i : Fin n ⊕ Fin m) = Sum.inr j then 1 else 0
      rw [CStarMatrix.one_apply]
      by_cases hij : i = j
      · simp only [Sum.inr.injEq, if_pos hij, Unitization.fst_one]
      · simp only [Sum.inr.injEq, if_neg hij, Unitization.fst_zero]

/-- Increasing the genuine finite compression size adds exactly an actual
identity block, after the concrete finite-coordinate equivalence. -/
theorem oddFredholmSupportedFiniteUnitary_stabilization
    (U : unitary (OddFredholmStandardOperator B))
    (hCompact : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) (n m : ℕ)
    (hU : (U : OddFredholmStandardOperator B) * (1 - standardCountableCutoff n) =
      1 - standardCountableCutoff n) :
    oddFredholmSupportedFiniteUnitary U hCompact (n + m)
      (oddFredholmSupportedUnitary_larger_tail U n m hU) =
        unitaryReindex finSumFinEquiv (unitaryBlockSum
          (oddFredholmSupportedFiniteUnitary U hCompact n hU)
          (1 : unitary (CStarMatrix (Fin m) (Fin m) (Unitization ℂ B)))) := by
  apply Subtype.ext
  apply CStarMatrix.ext
  intro i j
  apply oddFredholmUnitization_eq_of_scalar_and_left_action
  · have hs := (oddFredholmSupportedFiniteUnitary_scalar U hCompact (n + m)
      (oddFredholmSupportedUnitary_larger_tail U n m hU)).trans
      (oddFredholmScalarIdentity_reindexed_stabilization n m
        (oddFredholmSupportedFiniteUnitary U hCompact n hU)
        (oddFredholmSupportedFiniteUnitary_scalar U hCompact n hU)).symm
    exact congrArg (fun M : CStarMatrix (Fin (n + m)) (Fin (n + m)) ℂ => M i j) hs
  · ext b
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rw [oddFredholmSupportedFiniteUnitary_entry_action]
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simpa [unitaryReindex_apply, unitaryBlockSum, matrixBlockSum, Matrix.fromBlocks] using
          (oddFredholmSupportedFiniteUnitary_entry_action U hCompact n hU i j b).symm
      | inr j =>
        rw [show (finSumFinEquiv (Sum.inr j) : Fin (n + m)).val = n + j.val from rfl,
          oddFredholmSupportedUnitary_inclusion_tail U n hU (Nat.le_add_right n j.val)]
        rw [unitaryReindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        change standardCountableEvaluation i.val
          (standardCountableInclusion (n + j.val) b) =
          unitizedStandardLeftMul (0 : Unitization ℂ B) b
        rw [standardCountableEvaluation_inclusion, if_neg (by
          have hi := i.isLt
          omega), map_zero, AdjointableMap.coe_zero_apply]
    | inr i =>
      cases j with
      | inl j =>
        rw [show (finSumFinEquiv (Sum.inr i) : Fin (n + m)).val = n + i.val from rfl,
          oddFredholmSupportedUnitary_evaluation_tail U n hU (Nat.le_add_right n i.val)]
        rw [unitaryReindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        change standardCountableEvaluation (n + i.val)
          (standardCountableInclusion j.val b) =
          unitizedStandardLeftMul (0 : Unitization ℂ B) b
        rw [standardCountableEvaluation_inclusion, if_neg (by
          have hj := j.isLt
          omega), map_zero, AdjointableMap.coe_zero_apply]
      | inr j =>
        rw [show (finSumFinEquiv (Sum.inr j) : Fin (n + m)).val = n + j.val from rfl,
          oddFredholmSupportedUnitary_inclusion_tail U n hU (Nat.le_add_right n j.val)]
        rw [unitaryReindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        change standardCountableEvaluation (n + i.val)
          (standardCountableInclusion (n + j.val) b) =
          unitizedStandardLeftMul
            ((1 : CStarMatrix (Fin m) (Fin m) (Unitization ℂ B)) i j) b
        rw [standardCountableEvaluation_inclusion, CStarMatrix.one_apply]
        by_cases hij : i = j
        · subst j
          simp only [if_true, map_one, AdjointableMap.one_apply]
        · have hne : n + j.val ≠ n + i.val := by
            intro he
            exact hij (Fin.ext (Nat.add_left_cancel he).symm)
          simp only [if_neg hne, if_neg hij, map_zero, AdjointableMap.coe_zero_apply]

theorem oddFredholmSupportedFiniteUnitary_k1_stabilization
    (U : unitary (OddFredholmStandardOperator B))
    (hCompact : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) (n m : ℕ)
    (hU : (U : OddFredholmStandardOperator B) * (1 - standardCountableCutoff n) =
      1 - standardCountableCutoff n) :
    K1.of (FiniteUnitary.ofUnitary (oddFredholmSupportedFiniteUnitary U hCompact (n + m)
      (oddFredholmSupportedUnitary_larger_tail U n m hU))) =
      K1.of (FiniteUnitary.ofUnitary (oddFredholmSupportedFiniteUnitary U hCompact n hU)) := by
  rw [oddFredholmSupportedFiniteUnitary_stabilization U hCompact n m hU]
  calc
    _ = K1.of (FiniteUnitary.ofUnitary (unitaryBlockSum
        (oddFredholmSupportedFiniteUnitary U hCompact n hU)
        (1 : unitary (CStarMatrix (Fin m) (Fin m) (Unitization ℂ B))))) := by
      apply Quotient.sound
      apply FiniteUnitary.equivalent_symm
      exact FiniteUnitary.equivalent_reindex _ _ finSumFinEquiv rfl
    _ = _ := by
      change K1.of (FiniteUnitary.blockSum
        (FiniteUnitary.ofUnitary (oddFredholmSupportedFiniteUnitary U hCompact n hU))
        (FiniteUnitary.identity (A := Unitization ℂ B) (Fin m))) =
        K1.of (FiniteUnitary.ofUnitary (oddFredholmSupportedFiniteUnitary U hCompact n hU))
      exact K1.of_stabilize
        (FiniteUnitary.ofUnitary (oddFredholmSupportedFiniteUnitary U hCompact n hU)) (Fin m)

end BC4lean.KKTheory
