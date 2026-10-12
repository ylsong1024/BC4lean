import BC4lean.OddKTheoryCountableCoordinates
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Lean.Elab.Tactic.Omega

/-! # Actual integer reflections and sign on countable row-module sums

The signed-coordinate construction applies to the genuine completion of
countably many copies of any complete coefficient Hilbert module. In
particular it applies to the actual finite row modules B^n. Every reflection,
projection, and sign symmetry is an actual B-linear adjointable operator;
coordinate projections are not asserted compact.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

/-- Equality on genuine coefficient coordinates determines an actual operator. -/
theorem oddKTheoryRowOperator_ext_coordinates (S T : OddKTheoryCountableOperator B E)
    (h : ∀ n (b : E), S (countableModuleInclusion (B := B) (E := E) n b) =
      T (countableModuleInclusion (B := B) (E := E) n b)) : S = T := by
  apply oddKTheoryCountableOperator_ext_mk
  intro x
  have hx : countableModuleMk (B := B) (E := E) x =
      ∑ n ∈ x.support, countableModuleInclusion (B := B) (E := E) n (x n) := by
    calc
      countableModuleMk (B := B) (E := E) x = countableModuleMk (B := B) (E := E) (x.sum Finsupp.single) :=
        congrArg (countableModuleMk (B := B) (E := E)) x.sum_single.symm
      _ = ∑ n ∈ x.support, countableModuleInclusion (B := B) (E := E) n (x n) := by
        change countableModuleMk (B := B) (E := E) (∑ n ∈ x.support, Finsupp.single n (x n)) = _
        rw [map_sum]
        rfl
  rw [hx, map_sum S.toCLM, map_sum T.toCLM]
  exact Finset.sum_congr rfl (fun n _ => h n (x n))

/-- The actual completed coordinate permutation. -/
def oddKTheoryRowCoordinatePermutation (e : ℕ ≃ ℕ) : OddKTheoryCountableOperator B E :=
  oddKTheoryCountableEmbedding e.toEmbedding

@[simp] theorem oddKTheoryRowCoordinatePermutation_inclusion
    (e : ℕ ≃ ℕ) (n : ℕ) (b : E) :
    oddKTheoryRowCoordinatePermutation e (countableModuleInclusion (B := B) (E := E) n b) =
      countableModuleInclusion (B := B) (E := E) (e n) b :=
  oddKTheoryCountableEmbedding_inclusion e.toEmbedding n b

omit [CompleteSpace E] in
/-- Its actual adjoint is the inverse coordinate permutation. -/
theorem oddKTheoryRowCoordinatePermutation_star (e : ℕ ≃ ℕ) :
    star (oddKTheoryRowCoordinatePermutation (B := B) (E := E) e) =
      oddKTheoryRowCoordinatePermutation e.symm := by
  apply oddKTheoryCountableOperator_ext_mk
  intro x
  simp only [oddKTheoryRowCoordinatePermutation, AdjointableMap.star_eq_adjoint,
    oddKTheoryCountableEmbedding_adjoint_mk, oddKTheoryCountableEmbedding_mk]
  congr 1
  ext n
  rw [oddKTheoryCountableRestrictionLinear_apply e.toEmbedding x n,
    oddKTheoryCountableEmbeddingLinear_apply e.symm.toEmbedding x]
  calc
    x (e n) = (x.embDomain e.symm.toEmbedding) (e.symm.toEmbedding (e n)) :=
      (Finsupp.embDomain_apply_self e.symm.toEmbedding x (e n)).symm
    _ = (x.embDomain e.symm.toEmbedding) n :=
      congrArg (x.embDomain e.symm.toEmbedding) (e.symm_apply_apply n)

@[simp] theorem oddKTheoryRowCoordinatePermutation_refl :
    oddKTheoryRowCoordinatePermutation (B := B) (E := E) (Equiv.refl ℕ) = 1 := by
  apply oddKTheoryRowOperator_ext_coordinates
  intro n b
  simp only [oddKTheoryRowCoordinatePermutation_inclusion, Equiv.refl_apply,
    AdjointableMap.one_apply]

theorem oddKTheoryRowCoordinatePermutation_mul (e f : ℕ ≃ ℕ) :
    oddKTheoryRowCoordinatePermutation (B := B) (E := E) e * oddKTheoryRowCoordinatePermutation f =
      oddKTheoryRowCoordinatePermutation (f.trans e) := by
  apply oddKTheoryRowOperator_ext_coordinates
  intro n b
  simp only [AdjointableMap.mul_apply, oddKTheoryRowCoordinatePermutation_inclusion,
    Equiv.trans_apply]

theorem oddKTheoryRowCoordinatePermutation_mem_unitary (e : ℕ ≃ ℕ) :
    oddKTheoryRowCoordinatePermutation (B := B) (E := E) e ∈ unitary (OddKTheoryCountableOperator B E) := by
  apply Unitary.mem_iff.mpr
  constructor
  · rw [oddKTheoryRowCoordinatePermutation_star]
    apply oddKTheoryRowOperator_ext_coordinates
    intro n b
    simp only [AdjointableMap.mul_apply, oddKTheoryRowCoordinatePermutation_inclusion,
      Equiv.symm_apply_apply, AdjointableMap.one_apply]
  · rw [oddKTheoryRowCoordinatePermutation_star]
    apply oddKTheoryRowOperator_ext_coordinates
    intro n b
    simp only [AdjointableMap.mul_apply, oddKTheoryRowCoordinatePermutation_inclusion,
      Equiv.apply_symm_apply, AdjointableMap.one_apply]

def oddKTheoryRowIntegerIndex (z : ℤ) : ℕ := Equiv.intEquivNat z

@[simp] theorem oddKTheoryRowIntegerIndex_zero : oddKTheoryRowIntegerIndex 0 = 0 := rfl

def oddKTheoryRowIntegerInclusion (z : ℤ) :
    AdjointableMap B E (CountableHilbertModuleSum B E) :=
  countableModuleInclusion (B := B) (E := E) (oddKTheoryRowIntegerIndex z)

theorem oddKTheoryRowOperator_ext_integerCoordinates (S T : OddKTheoryCountableOperator B E)
    (h : ∀ z (b : E), S (oddKTheoryRowIntegerInclusion z b) =
      T (oddKTheoryRowIntegerInclusion z b)) : S = T := by
  apply oddKTheoryRowOperator_ext_coordinates
  intro n b
  obtain ⟨z, rfl⟩ := Equiv.intEquivNat.surjective n
  exact h z b

def oddKTheoryRowIntegerReflection (k : ℤ) : ℤ ≃ ℤ where
  toFun z := -z + k
  invFun z := -z + k
  left_inv z := by
    change -(-z + k) + k = z
    omega
  right_inv z := by
    change -(-z + k) + k = z
    omega

/-- The actual reflection of integer coefficient coordinates about `k/2`. -/
def oddKTheoryRowReflectionOperator (k : ℤ) : OddKTheoryCountableOperator B E :=
  oddKTheoryRowCoordinatePermutation
    ((Equiv.intEquivNat.symm.trans (oddKTheoryRowIntegerReflection k)).trans Equiv.intEquivNat)

@[simp] theorem oddKTheoryRowReflectionOperator_inclusion (k z : ℤ) (b : E) :
    oddKTheoryRowReflectionOperator (B := B) (E := E) k (oddKTheoryRowIntegerInclusion z b) =
      oddKTheoryRowIntegerInclusion (-z + k) b := by
  simp only [oddKTheoryRowReflectionOperator, oddKTheoryRowIntegerInclusion,
    oddKTheoryRowIntegerIndex, oddKTheoryRowCoordinatePermutation_inclusion,
    Equiv.trans_apply, Equiv.symm_apply_apply, oddKTheoryRowIntegerReflection]
  rfl

omit [CompleteSpace E] in
@[simp] theorem oddKTheoryRowReflectionOperator_star (k : ℤ) :
    star (oddKTheoryRowReflectionOperator (B := B) (E := E) k) = oddKTheoryRowReflectionOperator k := by
  rw [oddKTheoryRowReflectionOperator, oddKTheoryRowCoordinatePermutation_star]
  congr 1

@[simp] theorem oddKTheoryRowReflectionOperator_square (k : ℤ) :
    oddKTheoryRowReflectionOperator (B := B) (E := E) k * oddKTheoryRowReflectionOperator k = 1 := by
  apply oddKTheoryRowOperator_ext_integerCoordinates
  intro z b
  have hz : -(-z + k) + k = z := by omega
  simp only [AdjointableMap.mul_apply, oddKTheoryRowReflectionOperator_inclusion,
    hz, AdjointableMap.one_apply]

def oddKTheoryRowPositiveEmbedding : ℕ ↪ ℕ :=
  Function.Embedding.inl.trans Equiv.natSumNatEquivNat.toEmbedding

def oddKTheoryRowNegativeEmbedding : ℕ ↪ ℕ :=
  Function.Embedding.inr.trans Equiv.natSumNatEquivNat.toEmbedding

@[simp] theorem oddKTheoryRowPositiveEmbedding_apply (n : ℕ) :
    oddKTheoryRowPositiveEmbedding n = oddKTheoryRowIntegerIndex (n : ℤ) := rfl

@[simp] theorem oddKTheoryRowNegativeEmbedding_apply (n : ℕ) :
    oddKTheoryRowNegativeEmbedding n = oddKTheoryRowIntegerIndex (Int.negSucc n) := rfl

private theorem oddKTheoryRowPositive_not_negative (n : ℕ) :
    oddKTheoryRowPositiveEmbedding n ∉ Set.range oddKTheoryRowNegativeEmbedding := by
  rintro ⟨m, hm⟩
  have h : Sum.inr m = Sum.inl n := Equiv.natSumNatEquivNat.injective hm
  cases h

/-- The actual closed nonnegative-coordinate projection. -/
def oddKTheoryRowPositiveProjection : OddKTheoryCountableOperator B E :=
  oddKTheoryCountableEmbedding oddKTheoryRowPositiveEmbedding *
    star (oddKTheoryCountableEmbedding oddKTheoryRowPositiveEmbedding)

omit [CompleteSpace E] in
theorem oddKTheoryRowPositiveProjection_isStarProjection :
    IsStarProjection (oddKTheoryRowPositiveProjection (B := B) (E := E)) := by
  let U := oddKTheoryCountableEmbedding (B := B) (E := E) oddKTheoryRowPositiveEmbedding
  have hU : star U * U = 1 := oddKTheoryCountableEmbedding_adjoint_comp_self _
  apply isStarProjection_iff'.mpr
  constructor
  · change (U * star U) * (U * star U) = U * star U
    calc
      _ = U * (star U * U) * star U := by simp only [mul_assoc]
      _ = U * star U := by rw [hU, mul_one]
  · change star (U * star U) = U * star U
    rw [star_mul, star_star]

@[simp] theorem oddKTheoryRowPositiveProjection_positive (n : ℕ) (b : E) :
    oddKTheoryRowPositiveProjection (B := B) (E := E) (oddKTheoryRowIntegerInclusion (n : ℤ) b) =
      oddKTheoryRowIntegerInclusion (n : ℤ) b := by
  let U := oddKTheoryCountableEmbedding (B := B) (E := E) oddKTheoryRowPositiveEmbedding
  have hi : oddKTheoryRowIntegerInclusion (n : ℤ) b = U (countableModuleInclusion (B := B) (E := E) n b) :=
    (oddKTheoryCountableEmbedding_inclusion oddKTheoryRowPositiveEmbedding n b).symm
  have hU : U.adjoint.comp U = AdjointableMap.id :=
    oddKTheoryCountableEmbedding_adjoint_comp_self _
  rw [hi]
  change U ((U.adjoint.comp U) (countableModuleInclusion (B := B) (E := E) n b)) = U (countableModuleInclusion (B := B) (E := E) n b)
  rw [hU, AdjointableMap.id_apply]

@[simp] theorem oddKTheoryRowPositiveProjection_negative (n : ℕ) (b : E) :
    oddKTheoryRowPositiveProjection (B := B) (E := E) (oddKTheoryRowIntegerInclusion (Int.negSucc n) b) = 0 := by
  let U := oddKTheoryCountableEmbedding (B := B) (E := E) oddKTheoryRowPositiveEmbedding
  let V := oddKTheoryCountableEmbedding (B := B) (E := E) oddKTheoryRowNegativeEmbedding
  have hi : oddKTheoryRowIntegerInclusion (Int.negSucc n) b = V (countableModuleInclusion (B := B) (E := E) n b) :=
    (oddKTheoryCountableEmbedding_inclusion oddKTheoryRowNegativeEmbedding n b).symm
  have hUV : U.adjoint.comp V = 0 :=
    oddKTheoryCountableEmbedding_adjoint_comp_eq_zero _ _ oddKTheoryRowPositive_not_negative
  rw [hi]
  change U ((U.adjoint.comp V) (countableModuleInclusion (B := B) (E := E) n b)) = 0
  rw [hUV, AdjointableMap.coe_zero_apply, map_zero U.toCLM]

/-- Negative on nonnegative integer coordinates, positive on negative ones. -/
def oddKTheoryRowSignOperator : OddKTheoryCountableOperator B E :=
  1 - (2 : ℂ) • oddKTheoryRowPositiveProjection

def oddKTheoryRowIntegerSign (z : ℤ) : ℂ := if 0 ≤ z then -1 else 1

@[simp] theorem oddKTheoryRowSignOperator_inclusion (z : ℤ) (b : E) :
    oddKTheoryRowSignOperator (B := B) (E := E) (oddKTheoryRowIntegerInclusion z b) =
      oddKTheoryRowIntegerSign z • oddKTheoryRowIntegerInclusion z b := by
  cases z with
  | ofNat n =>
    change oddKTheoryRowSignOperator (B := B) (E := E)
        (oddKTheoryRowIntegerInclusion (n : ℤ) b) =
      oddKTheoryRowIntegerSign (n : ℤ) • oddKTheoryRowIntegerInclusion (n : ℤ) b
    rw [oddKTheoryRowIntegerSign, if_pos (Int.natCast_nonneg n),
      oddKTheoryRowSignOperator, AdjointableMap.coe_sub_apply,
      AdjointableMap.one_apply, AdjointableMap.coe_smul_apply,
      oddKTheoryRowPositiveProjection_positive]
    module
  | negSucc n =>
    have hn : ¬(0 : ℤ) ≤ Int.negSucc n := by omega
    simp only [oddKTheoryRowSignOperator, AdjointableMap.coe_sub_apply,
      AdjointableMap.one_apply, AdjointableMap.coe_smul_apply,
      oddKTheoryRowPositiveProjection_negative, smul_zero, sub_zero,
      oddKTheoryRowIntegerSign, if_neg hn, one_smul]

omit [CompleteSpace E] in
@[simp] theorem oddKTheoryRowSignOperator_star :
    star (oddKTheoryRowSignOperator (B := B) (E := E)) = oddKTheoryRowSignOperator := by
  simp only [oddKTheoryRowSignOperator, star_sub, star_one, star_smul,
    star_ofNat, oddKTheoryRowPositiveProjection_isStarProjection.isSelfAdjoint.star_eq]

omit [CompleteSpace E] in
@[simp] theorem oddKTheoryRowSignOperator_square :
    oddKTheoryRowSignOperator (B := B) (E := E) * oddKTheoryRowSignOperator = 1 := by
  have hP := (oddKTheoryRowPositiveProjection_isStarProjection (B := B) (E := E)).isIdempotentElem.eq
  simp only [oddKTheoryRowSignOperator, two_smul, mul_sub, sub_mul, mul_add, add_mul,
    one_mul, mul_one, hP]
  abel

/-- The actual zero-coordinate projection; its compactness is not assumed. -/
def oddKTheoryRowZeroProjection : OddKTheoryCountableOperator B E :=
  (countableModuleInclusion (B := B) (E := E) 0).comp (countableModuleEvaluation (B := B) (E := E) 0)

@[simp] theorem oddKTheoryRowZeroProjection_star :
    star (oddKTheoryRowZeroProjection (B := B) (E := E)) = oddKTheoryRowZeroProjection := by
  change ((countableModuleInclusion (B := B) (E := E) 0).comp
    (countableModuleInclusion (B := B) (E := E) 0).adjoint).adjoint =
      (countableModuleInclusion (B := B) (E := E) 0).comp
        (countableModuleInclusion (B := B) (E := E) 0).adjoint
  rw [AdjointableMap.adjoint_comp, AdjointableMap.adjoint_adjoint]

@[simp] theorem oddKTheoryRowZeroProjection_square :
    oddKTheoryRowZeroProjection (B := B) (E := E) * oddKTheoryRowZeroProjection = oddKTheoryRowZeroProjection := by
  ext x
  simp only [AdjointableMap.mul_apply, oddKTheoryRowZeroProjection,
    AdjointableMap.comp_apply, countableModuleEvaluation_inclusion, if_true]

@[simp] theorem oddKTheoryRowZeroProjection_inclusion (z : ℤ) (b : E) :
    oddKTheoryRowZeroProjection (B := B) (E := E) (oddKTheoryRowIntegerInclusion z b) =
      if z = 0 then oddKTheoryRowIntegerInclusion z b else 0 := by
  simp only [oddKTheoryRowZeroProjection, oddKTheoryRowIntegerInclusion,
    AdjointableMap.comp_apply, countableModuleEvaluation_inclusion]
  by_cases hz : z = 0
  · subst z
    simp only [oddKTheoryRowIntegerIndex_zero, if_true]
  · have hn : oddKTheoryRowIntegerIndex z ≠ 0 := by
      intro h
      apply hz
      exact Equiv.intEquivNat.injective (h.trans oddKTheoryRowIntegerIndex_zero.symm)
    simp only [if_neg hn, if_neg hz, map_zero (countableModuleInclusion (B := B) (E := E) 0).toCLM]

@[simp] theorem oddKTheoryRowSign_mul_zeroProjection :
    oddKTheoryRowSignOperator (B := B) (E := E) * oddKTheoryRowZeroProjection = -oddKTheoryRowZeroProjection := by
  ext x
  rw [AdjointableMap.mul_apply, AdjointableMap.coe_neg_apply]
  change oddKTheoryRowSignOperator (B := B) (E := E) (oddKTheoryRowIntegerInclusion (B := B) (E := E) 0
      (countableModuleEvaluation (B := B) (E := E) 0 x)) = -oddKTheoryRowIntegerInclusion 0 (countableModuleEvaluation (B := B) (E := E) 0 x)
  rw [oddKTheoryRowSignOperator_inclusion]
  simp [oddKTheoryRowIntegerSign]

@[simp] theorem oddKTheoryRowZeroProjection_mul_sign :
    oddKTheoryRowZeroProjection (B := B) (E := E) * oddKTheoryRowSignOperator = -oddKTheoryRowZeroProjection := by
  have h := congrArg star (oddKTheoryRowSign_mul_zeroProjection (B := B) (E := E))
  simpa only [star_mul, oddKTheoryRowSignOperator_star, oddKTheoryRowZeroProjection_star, star_neg] using h

@[simp] theorem oddKTheoryRowReflection_zero_mul_zeroProjection :
    oddKTheoryRowReflectionOperator (B := B) (E := E) 0 * oddKTheoryRowZeroProjection = oddKTheoryRowZeroProjection := by
  ext x
  change oddKTheoryRowReflectionOperator (B := B) (E := E) 0 (oddKTheoryRowIntegerInclusion (B := B) (E := E) 0
    (countableModuleEvaluation (B := B) (E := E) 0 x)) = oddKTheoryRowIntegerInclusion 0 (countableModuleEvaluation (B := B) (E := E) 0 x)
  simp only [oddKTheoryRowReflectionOperator_inclusion, neg_zero, add_zero]

@[simp] theorem oddKTheoryRowZeroProjection_mul_reflection_zero :
    oddKTheoryRowZeroProjection (B := B) (E := E) * oddKTheoryRowReflectionOperator 0 = oddKTheoryRowZeroProjection := by
  have h := congrArg star (oddKTheoryRowReflection_zero_mul_zeroProjection (B := B) (E := E))
  simpa only [star_mul, oddKTheoryRowReflectionOperator_star, oddKTheoryRowZeroProjection_star] using h

/-- Reflection at the origin reverses the sign, with exactly the zero-coordinate correction. -/
theorem oddKTheoryRowReflection_zero_sign_conjugate :
    oddKTheoryRowReflectionOperator (B := B) (E := E) 0 * oddKTheoryRowSignOperator *
      oddKTheoryRowReflectionOperator 0 =
      -oddKTheoryRowSignOperator - (2 : ℂ) • oddKTheoryRowZeroProjection := by
  apply oddKTheoryRowOperator_ext_integerCoordinates
  intro z b
  simp only [AdjointableMap.mul_apply, oddKTheoryRowReflectionOperator_inclusion,
    oddKTheoryRowSignOperator_inclusion, map_smul (oddKTheoryRowReflectionOperator 0).toCLM,
    add_zero, neg_neg, AdjointableMap.coe_sub_apply, AdjointableMap.coe_neg_apply,
    AdjointableMap.coe_smul_apply, oddKTheoryRowZeroProjection_inclusion]
  by_cases hz : z = 0
  · subst z
    simp only [if_true, oddKTheoryRowIntegerSign, le_refl, if_true, neg_zero]
    module
  · have hs : oddKTheoryRowIntegerSign (-z) = -oddKTheoryRowIntegerSign z := by
      by_cases hp : 0 ≤ z
      · have hn : ¬0 ≤ -z := by omega
        simp only [oddKTheoryRowIntegerSign, if_neg hn, if_pos hp, neg_neg]
      · have hn : 0 ≤ -z := by omega
        simp only [oddKTheoryRowIntegerSign, if_pos hn, if_neg hp]
    rw [if_neg hz, smul_zero, sub_zero, hs, neg_smul]

/-- Reflection at `-1/2` reverses the sign exactly on every integer coordinate. -/
theorem oddKTheoryRowReflection_neg_one_sign_conjugate :
    oddKTheoryRowReflectionOperator (B := B) (E := E) (-1) * oddKTheoryRowSignOperator *
      oddKTheoryRowReflectionOperator (-1) = -oddKTheoryRowSignOperator := by
  apply oddKTheoryRowOperator_ext_integerCoordinates
  intro z b
  have hz : -(-z + (-1)) + (-1) = z := by omega
  have hs : oddKTheoryRowIntegerSign (-z + (-1)) = -oddKTheoryRowIntegerSign z := by
    by_cases hp : 0 ≤ z
    · have hn : ¬0 ≤ -z + (-1) := by omega
      simp [oddKTheoryRowIntegerSign, hp, hn]
    · have hn : 0 ≤ -z + (-1) := by omega
      simp [oddKTheoryRowIntegerSign, hp, hn]
  simp only [AdjointableMap.mul_apply, oddKTheoryRowReflectionOperator_inclusion,
    oddKTheoryRowSignOperator_inclusion, AdjointableMap.coe_neg_apply]
  rw [map_smul (oddKTheoryRowReflectionOperator (-1)).toCLM,
    oddKTheoryRowReflectionOperator_inclusion, hz, hs, neg_smul]


/-- A genuine diagonal operator sends a single actual row coordinate to the
same coordinate with the actual coefficient-module operator applied. -/
theorem oddKTheoryCountableDiagonal_inclusion (S : AdjointableMap B E E)
    (n : ℕ) (b : E) :
    countableModuleDiagonal S (countableModuleInclusion (B := B) n b) =
      countableModuleInclusion (B := B) n (S b) := by
  apply countableModule_ext_eval
  intro i
  rw [countableModuleEvaluation_diagonal, countableModuleEvaluation_inclusion,
    countableModuleEvaluation_inclusion]
  split_ifs <;> simp only [map_zero]

theorem oddKTheoryRowDiagonal_integerInclusion (S : AdjointableMap B E E)
    (z : ℤ) (b : E) :
    countableModuleDiagonal S (oddKTheoryRowIntegerInclusion z b) =
      oddKTheoryRowIntegerInclusion z (S b) :=
  oddKTheoryCountableDiagonal_inclusion S _ b

/-- Actual integer-coordinate reflections commute with every actual
coordinatewise row coefficient operator. -/
theorem oddKTheoryRowReflection_diagonal_commute (k : ℤ) (S : AdjointableMap B E E) :
    Commute (oddKTheoryRowReflectionOperator k) (countableModuleDiagonal S) := by
  change oddKTheoryRowReflectionOperator k * countableModuleDiagonal S =
    countableModuleDiagonal S * oddKTheoryRowReflectionOperator k
  apply oddKTheoryRowOperator_ext_integerCoordinates
  intro z b
  simp only [AdjointableMap.mul_apply, oddKTheoryRowDiagonal_integerInclusion,
    oddKTheoryRowReflectionOperator_inclusion]

/-- The genuine sign operator commutes with every coordinatewise row
coefficient operator, with no scalar Hilbert-space tensor assumption. -/
theorem oddKTheoryRowSign_diagonal_commute (S : AdjointableMap B E E) :
    Commute (oddKTheoryRowSignOperator (B := B) (E := E)) (countableModuleDiagonal S) := by
  change oddKTheoryRowSignOperator * countableModuleDiagonal S =
    countableModuleDiagonal S * oddKTheoryRowSignOperator
  apply oddKTheoryRowOperator_ext_integerCoordinates
  intro z b
  simp only [AdjointableMap.mul_apply, oddKTheoryRowDiagonal_integerInclusion,
    oddKTheoryRowSignOperator_inclusion, map_smul]

theorem oddKTheoryRowZeroProjection_diagonal_commute (S : AdjointableMap B E E) :
    Commute (oddKTheoryRowZeroProjection (B := B) (E := E)) (countableModuleDiagonal S) := by
  change oddKTheoryRowZeroProjection * countableModuleDiagonal S =
    countableModuleDiagonal S * oddKTheoryRowZeroProjection
  apply oddKTheoryRowOperator_ext_integerCoordinates
  intro z b
  simp only [AdjointableMap.mul_apply, oddKTheoryRowDiagonal_integerInclusion,
    oddKTheoryRowZeroProjection_inclusion]
  split_ifs
  · exact (oddKTheoryRowDiagonal_integerInclusion S z b).symm
  · exact (map_zero (countableModuleDiagonal S).toCLM).symm

end BC4lean.KKTheory
