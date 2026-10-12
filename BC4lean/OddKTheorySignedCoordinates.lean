import BC4lean.StandardCountableReindex
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Lean.Elab.Tactic.Omega

/-! # Actual signed integer coordinates on the genuine standard module

Integer coordinates use the proved equivalence ℤ ≃ ℕ. Reflections are actual
completed coefficient-coordinate permutations. The sign operator is formed
from the actual isometry onto the nonnegative integer coordinates. Its two
reflection identities differ at precisely the actual zero-coordinate
projection. That projection is not declared compact over a nonunital algebra.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

abbrev OddKTheoryStandardOperator (B : Type*) [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] :=
  AdjointableMap B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)

/-- Equality on genuine coefficient coordinates determines an actual operator. -/
theorem oddKTheoryOperator_ext_coordinates (S T : OddKTheoryStandardOperator B)
    (h : ∀ n (b : Bᵐᵒᵖ), S (standardCountableInclusion n b) =
      T (standardCountableInclusion n b)) : S = T := by
  apply standardCountable_adjointable_ext_mk
  intro x
  have hx : standardCountableMk x =
      ∑ n ∈ x.support, standardCountableInclusion n (x n) := by
    calc
      standardCountableMk x = standardCountableMk (x.sum Finsupp.single) :=
        congrArg (standardCountableMk (B := B)) x.sum_single.symm
      _ = ∑ n ∈ x.support, standardCountableInclusion n (x n) := by
        change standardCountableMk (∑ n ∈ x.support, Finsupp.single n (x n)) = _
        rw [map_sum]
        rfl
  rw [hx, map_sum S.toCLM, map_sum T.toCLM]
  exact Finset.sum_congr rfl (fun n _ => h n (x n))

/-- The actual completed coordinate permutation. -/
def oddKTheoryCoordinatePermutation (e : ℕ ≃ ℕ) : OddKTheoryStandardOperator B :=
  standardCountableEmbedding e.toEmbedding

@[simp] theorem oddKTheoryCoordinatePermutation_inclusion
    (e : ℕ ≃ ℕ) (n : ℕ) (b : Bᵐᵒᵖ) :
    oddKTheoryCoordinatePermutation e (standardCountableInclusion n b) =
      standardCountableInclusion (e n) b :=
  standardCountableEmbedding_inclusion e.toEmbedding n b

/-- Its actual adjoint is the inverse coordinate permutation. -/
theorem oddKTheoryCoordinatePermutation_star (e : ℕ ≃ ℕ) :
    star (oddKTheoryCoordinatePermutation (B := B) e) =
      oddKTheoryCoordinatePermutation e.symm := by
  apply standardCountable_adjointable_ext_mk
  intro x
  simp only [oddKTheoryCoordinatePermutation, AdjointableMap.star_eq_adjoint,
    standardCountableEmbedding_adjoint_mk, standardCountableEmbedding_mk]
  congr 1
  ext n
  rw [standardCountableRestrictionLinear_apply e.toEmbedding x n,
    standardCountableEmbeddingLinear_apply e.symm.toEmbedding x]
  calc
    x (e n) = (x.embDomain e.symm.toEmbedding) (e.symm.toEmbedding (e n)) :=
      (Finsupp.embDomain_apply_self e.symm.toEmbedding x (e n)).symm
    _ = (x.embDomain e.symm.toEmbedding) n :=
      congrArg (x.embDomain e.symm.toEmbedding) (e.symm_apply_apply n)

@[simp] theorem oddKTheoryCoordinatePermutation_refl :
    oddKTheoryCoordinatePermutation (B := B) (Equiv.refl ℕ) = 1 := by
  apply oddKTheoryOperator_ext_coordinates
  intro n b
  simp only [oddKTheoryCoordinatePermutation_inclusion, Equiv.refl_apply,
    AdjointableMap.one_apply]

theorem oddKTheoryCoordinatePermutation_mul (e f : ℕ ≃ ℕ) :
    oddKTheoryCoordinatePermutation (B := B) e * oddKTheoryCoordinatePermutation f =
      oddKTheoryCoordinatePermutation (f.trans e) := by
  apply oddKTheoryOperator_ext_coordinates
  intro n b
  simp only [AdjointableMap.mul_apply, oddKTheoryCoordinatePermutation_inclusion,
    Equiv.trans_apply]

theorem oddKTheoryCoordinatePermutation_mem_unitary (e : ℕ ≃ ℕ) :
    oddKTheoryCoordinatePermutation (B := B) e ∈ unitary (OddKTheoryStandardOperator B) := by
  apply Unitary.mem_iff.mpr
  constructor
  · rw [oddKTheoryCoordinatePermutation_star]
    apply oddKTheoryOperator_ext_coordinates
    intro n b
    simp only [AdjointableMap.mul_apply, oddKTheoryCoordinatePermutation_inclusion,
      Equiv.symm_apply_apply, AdjointableMap.one_apply]
  · rw [oddKTheoryCoordinatePermutation_star]
    apply oddKTheoryOperator_ext_coordinates
    intro n b
    simp only [AdjointableMap.mul_apply, oddKTheoryCoordinatePermutation_inclusion,
      Equiv.apply_symm_apply, AdjointableMap.one_apply]

def oddKTheoryIntegerIndex (z : ℤ) : ℕ := Equiv.intEquivNat z

@[simp] theorem oddKTheoryIntegerIndex_zero : oddKTheoryIntegerIndex 0 = 0 := rfl

def oddKTheoryIntegerInclusion (z : ℤ) :
    AdjointableMap B Bᵐᵒᵖ (StandardCountableHilbertModule B) :=
  standardCountableInclusion (oddKTheoryIntegerIndex z)

theorem oddKTheoryOperator_ext_integerCoordinates (S T : OddKTheoryStandardOperator B)
    (h : ∀ z (b : Bᵐᵒᵖ), S (oddKTheoryIntegerInclusion z b) =
      T (oddKTheoryIntegerInclusion z b)) : S = T := by
  apply oddKTheoryOperator_ext_coordinates
  intro n b
  obtain ⟨z, rfl⟩ := Equiv.intEquivNat.surjective n
  exact h z b

def oddKTheoryIntegerReflection (k : ℤ) : ℤ ≃ ℤ where
  toFun z := -z + k
  invFun z := -z + k
  left_inv z := by
    change -(-z + k) + k = z
    omega
  right_inv z := by
    change -(-z + k) + k = z
    omega

/-- The actual reflection of integer coefficient coordinates about `k/2`. -/
def oddKTheoryReflectionOperator (k : ℤ) : OddKTheoryStandardOperator B :=
  oddKTheoryCoordinatePermutation
    ((Equiv.intEquivNat.symm.trans (oddKTheoryIntegerReflection k)).trans Equiv.intEquivNat)

@[simp] theorem oddKTheoryReflectionOperator_inclusion (k z : ℤ) (b : Bᵐᵒᵖ) :
    oddKTheoryReflectionOperator k (oddKTheoryIntegerInclusion z b) =
      oddKTheoryIntegerInclusion (-z + k) b := by
  simp only [oddKTheoryReflectionOperator, oddKTheoryIntegerInclusion,
    oddKTheoryIntegerIndex, oddKTheoryCoordinatePermutation_inclusion,
    Equiv.trans_apply, Equiv.symm_apply_apply, oddKTheoryIntegerReflection,
    Equiv.coe_fn_mk]

@[simp] theorem oddKTheoryReflectionOperator_star (k : ℤ) :
    star (oddKTheoryReflectionOperator (B := B) k) = oddKTheoryReflectionOperator k := by
  rw [oddKTheoryReflectionOperator, oddKTheoryCoordinatePermutation_star]
  congr 1

@[simp] theorem oddKTheoryReflectionOperator_square (k : ℤ) :
    oddKTheoryReflectionOperator (B := B) k * oddKTheoryReflectionOperator k = 1 := by
  apply oddKTheoryOperator_ext_integerCoordinates
  intro z b
  have hz : -(-z + k) + k = z := by omega
  simp only [AdjointableMap.mul_apply, oddKTheoryReflectionOperator_inclusion,
    AdjointableMap.one_apply, hz]

def oddKTheoryPositiveEmbedding : ℕ ↪ ℕ :=
  Function.Embedding.inl.trans Equiv.natSumNatEquivNat.toEmbedding

def oddKTheoryNegativeEmbedding : ℕ ↪ ℕ :=
  Function.Embedding.inr.trans Equiv.natSumNatEquivNat.toEmbedding

@[simp] theorem oddKTheoryPositiveEmbedding_apply (n : ℕ) :
    oddKTheoryPositiveEmbedding n = oddKTheoryIntegerIndex (n : ℤ) := rfl

@[simp] theorem oddKTheoryNegativeEmbedding_apply (n : ℕ) :
    oddKTheoryNegativeEmbedding n = oddKTheoryIntegerIndex (Int.negSucc n) := rfl

private theorem oddKTheoryPositive_not_negative (n : ℕ) :
    oddKTheoryPositiveEmbedding n ∉ Set.range oddKTheoryNegativeEmbedding := by
  rintro ⟨m, hm⟩
  have h : Sum.inr m = Sum.inl n := Equiv.natSumNatEquivNat.injective hm
  cases h

/-- The actual closed nonnegative-coordinate projection. -/
def oddKTheoryPositiveProjection : OddKTheoryStandardOperator B :=
  standardCountableEmbedding oddKTheoryPositiveEmbedding *
    star (standardCountableEmbedding oddKTheoryPositiveEmbedding)

theorem oddKTheoryPositiveProjection_isStarProjection :
    IsStarProjection (oddKTheoryPositiveProjection (B := B)) := by
  let U := standardCountableEmbedding (B := B) oddKTheoryPositiveEmbedding
  have hU : star U * U = 1 := standardCountableEmbedding_adjoint_comp_self _
  apply isStarProjection_iff'.mpr
  constructor
  · change (U * star U) * (U * star U) = U * star U
    calc
      _ = U * (star U * U) * star U := by simp only [mul_assoc]
      _ = U * star U := by rw [hU, mul_one]
  · change star (U * star U) = U * star U
    rw [star_mul, star_star]

@[simp] theorem oddKTheoryPositiveProjection_positive (n : ℕ) (b : Bᵐᵒᵖ) :
    oddKTheoryPositiveProjection (oddKTheoryIntegerInclusion (n : ℤ) b) =
      oddKTheoryIntegerInclusion (n : ℤ) b := by
  let U := standardCountableEmbedding (B := B) oddKTheoryPositiveEmbedding
  have hi : oddKTheoryIntegerInclusion (n : ℤ) b = U (standardCountableInclusion n b) :=
    (standardCountableEmbedding_inclusion oddKTheoryPositiveEmbedding n b).symm
  have hU : U.adjoint.comp U = AdjointableMap.id :=
    standardCountableEmbedding_adjoint_comp_self _
  rw [hi]
  change U ((U.adjoint.comp U) (standardCountableInclusion n b)) = U (standardCountableInclusion n b)
  rw [hU, AdjointableMap.id_apply]

@[simp] theorem oddKTheoryPositiveProjection_negative (n : ℕ) (b : Bᵐᵒᵖ) :
    oddKTheoryPositiveProjection (oddKTheoryIntegerInclusion (Int.negSucc n) b) = 0 := by
  let U := standardCountableEmbedding (B := B) oddKTheoryPositiveEmbedding
  let V := standardCountableEmbedding (B := B) oddKTheoryNegativeEmbedding
  have hi : oddKTheoryIntegerInclusion (Int.negSucc n) b = V (standardCountableInclusion n b) :=
    (standardCountableEmbedding_inclusion oddKTheoryNegativeEmbedding n b).symm
  have hUV : U.adjoint.comp V = 0 :=
    standardCountableEmbedding_adjoint_comp_eq_zero _ _ oddKTheoryPositive_not_negative
  rw [hi]
  change U ((U.adjoint.comp V) (standardCountableInclusion n b)) = 0
  rw [hUV, AdjointableMap.coe_zero_apply, map_zero U.toCLM]

/-- Negative on nonnegative integer coordinates, positive on negative ones. -/
def oddKTheorySignOperator : OddKTheoryStandardOperator B :=
  1 - (2 : ℂ) • oddKTheoryPositiveProjection

def oddKTheoryIntegerSign (z : ℤ) : ℂ := if 0 ≤ z then -1 else 1

@[simp] theorem oddKTheorySignOperator_inclusion (z : ℤ) (b : Bᵐᵒᵖ) :
    oddKTheorySignOperator (oddKTheoryIntegerInclusion z b) =
      oddKTheoryIntegerSign z • oddKTheoryIntegerInclusion z b := by
  cases z with
  | ofNat n =>
    have hSign : oddKTheoryIntegerSign (Int.ofNat n) = -1 := by
      unfold oddKTheoryIntegerSign
      exact if_pos (Int.natCast_nonneg n)
    rw [hSign]
    change (1 - (2 : ℂ) • oddKTheoryPositiveProjection)
      (oddKTheoryIntegerInclusion (n : ℤ) b) =
      (-1 : ℂ) • oddKTheoryIntegerInclusion (n : ℤ) b
    rw [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply,
      AdjointableMap.coe_smul_apply, oddKTheoryPositiveProjection_positive]
    module
  | negSucc n =>
    have hn : ¬(0 : ℤ) ≤ Int.negSucc n := by omega
    simp only [oddKTheorySignOperator, AdjointableMap.coe_sub_apply,
      AdjointableMap.one_apply, AdjointableMap.coe_smul_apply,
      oddKTheoryPositiveProjection_negative, smul_zero, sub_zero,
      oddKTheoryIntegerSign, if_neg hn, one_smul]

@[simp] theorem oddKTheorySignOperator_star :
    star (oddKTheorySignOperator (B := B)) = oddKTheorySignOperator := by
  simp only [oddKTheorySignOperator, star_sub, star_one, star_smul,
    star_ofNat, oddKTheoryPositiveProjection_isStarProjection.isSelfAdjoint.star_eq]

@[simp] theorem oddKTheorySignOperator_square :
    oddKTheorySignOperator (B := B) * oddKTheorySignOperator = 1 := by
  have hP := (oddKTheoryPositiveProjection_isStarProjection (B := B)).isIdempotentElem.eq
  simp only [oddKTheorySignOperator, two_smul, mul_sub, sub_mul, mul_add, add_mul,
    one_mul, mul_one, hP]
  abel

/-- The actual zero-coordinate projection; its compactness is not assumed. -/
def oddKTheoryZeroProjection : OddKTheoryStandardOperator B :=
  (standardCountableInclusion 0).comp (standardCountableEvaluation 0)

@[simp] theorem oddKTheoryZeroProjection_star :
    star (oddKTheoryZeroProjection (B := B)) = oddKTheoryZeroProjection := by
  change (oddKTheoryZeroProjection (B := B)).adjoint = _
  simp only [oddKTheoryZeroProjection, AdjointableMap.adjoint_comp,
    standardCountableEvaluation, AdjointableMap.adjoint_adjoint]

@[simp] theorem oddKTheoryZeroProjection_square :
    oddKTheoryZeroProjection (B := B) * oddKTheoryZeroProjection = oddKTheoryZeroProjection := by
  ext x
  simp only [AdjointableMap.mul_apply, oddKTheoryZeroProjection,
    AdjointableMap.comp_apply, standardCountableEvaluation_inclusion, if_true]

@[simp] theorem oddKTheoryZeroProjection_inclusion (z : ℤ) (b : Bᵐᵒᵖ) :
    oddKTheoryZeroProjection (oddKTheoryIntegerInclusion z b) =
      if z = 0 then oddKTheoryIntegerInclusion z b else 0 := by
  simp only [oddKTheoryZeroProjection, oddKTheoryIntegerInclusion,
    AdjointableMap.comp_apply, standardCountableEvaluation_inclusion]
  by_cases hz : z = 0
  · subst z
    simp only [oddKTheoryIntegerIndex_zero, if_true]
  · have hn : oddKTheoryIntegerIndex z ≠ 0 := by
      intro h
      apply hz
      exact Equiv.intEquivNat.injective (h.trans oddKTheoryIntegerIndex_zero.symm)
    simp only [if_neg hn, if_neg hz]
    exact (standardCountableInclusion (B := B) 0).toCLM.map_zero

@[simp] theorem oddKTheorySign_mul_zeroProjection :
    oddKTheorySignOperator (B := B) * oddKTheoryZeroProjection = -oddKTheoryZeroProjection := by
  ext x
  simp only [AdjointableMap.mul_apply, AdjointableMap.coe_neg_apply,
    oddKTheoryZeroProjection, AdjointableMap.comp_apply]
  change oddKTheorySignOperator (oddKTheoryIntegerInclusion 0
      (standardCountableEvaluation 0 x)) = -oddKTheoryIntegerInclusion 0 (standardCountableEvaluation 0 x)
  rw [oddKTheorySignOperator_inclusion]
  simp [oddKTheoryIntegerSign]

@[simp] theorem oddKTheoryZeroProjection_mul_sign :
    oddKTheoryZeroProjection (B := B) * oddKTheorySignOperator = -oddKTheoryZeroProjection := by
  have h := congrArg star (oddKTheorySign_mul_zeroProjection (B := B))
  simpa only [star_mul, oddKTheorySignOperator_star, oddKTheoryZeroProjection_star, star_neg] using h

@[simp] theorem oddKTheoryReflection_zero_mul_zeroProjection :
    oddKTheoryReflectionOperator (B := B) 0 * oddKTheoryZeroProjection = oddKTheoryZeroProjection := by
  ext x
  change oddKTheoryReflectionOperator 0 (oddKTheoryIntegerInclusion 0
    (standardCountableEvaluation 0 x)) = oddKTheoryIntegerInclusion 0 (standardCountableEvaluation 0 x)
  simp only [oddKTheoryReflectionOperator_inclusion, neg_zero, add_zero]

@[simp] theorem oddKTheoryZeroProjection_mul_reflection_zero :
    oddKTheoryZeroProjection (B := B) * oddKTheoryReflectionOperator 0 = oddKTheoryZeroProjection := by
  have h := congrArg star (oddKTheoryReflection_zero_mul_zeroProjection (B := B))
  simpa only [star_mul, oddKTheoryReflectionOperator_star, oddKTheoryZeroProjection_star] using h

/-- Reflection at the origin reverses the sign, with exactly the zero-coordinate correction. -/
theorem oddKTheoryReflection_zero_sign_conjugate :
    oddKTheoryReflectionOperator (B := B) 0 * oddKTheorySignOperator *
      oddKTheoryReflectionOperator 0 =
      -oddKTheorySignOperator - (2 : ℂ) • oddKTheoryZeroProjection := by
  apply oddKTheoryOperator_ext_integerCoordinates
  intro z b
  simp only [AdjointableMap.mul_apply, oddKTheoryReflectionOperator_inclusion,
    oddKTheorySignOperator_inclusion, map_smul (oddKTheoryReflectionOperator 0).toCLM,
    add_zero, neg_neg, AdjointableMap.coe_sub_apply, AdjointableMap.coe_neg_apply,
    AdjointableMap.coe_smul_apply, oddKTheoryZeroProjection_inclusion]
  by_cases hz : z = 0
  · subst z
    simp only [if_true, oddKTheoryIntegerSign, le_refl, if_true, neg_zero]
    module
  · have hs : oddKTheoryIntegerSign (-z) = -oddKTheoryIntegerSign z := by
      by_cases hp : 0 ≤ z
      · have hn : ¬0 ≤ -z := by omega
        simp only [oddKTheoryIntegerSign, if_pos hp, if_neg hn, neg_neg]
      · have hn : 0 ≤ -z := by omega
        simp only [oddKTheoryIntegerSign, if_neg hp, if_pos hn]
    rw [if_neg hz, smul_zero, sub_zero, hs, neg_smul]

/-- Reflection at `-1/2` reverses the sign exactly on every integer coordinate. -/
theorem oddKTheoryReflection_neg_one_sign_conjugate :
    oddKTheoryReflectionOperator (B := B) (-1) * oddKTheorySignOperator *
      oddKTheoryReflectionOperator (-1) = -oddKTheorySignOperator := by
  apply oddKTheoryOperator_ext_integerCoordinates
  intro z b
  have hz : -(-z + (-1)) + (-1) = z := by omega
  have hs : oddKTheoryIntegerSign (-z + (-1)) = -oddKTheoryIntegerSign z := by
    by_cases hp : 0 ≤ z
    · have hn : ¬0 ≤ -z + (-1) := by omega
      simp only [oddKTheoryIntegerSign, if_pos hp, if_neg hn, neg_neg]
    · have hn : 0 ≤ -z + (-1) := by omega
      simp only [oddKTheoryIntegerSign, if_neg hp, if_pos hn]
  calc
    (oddKTheoryReflectionOperator (B := B) (-1) * oddKTheorySignOperator (B := B) *
        oddKTheoryReflectionOperator (B := B) (-1)) (oddKTheoryIntegerInclusion z b) =
        oddKTheoryReflectionOperator (B := B) (-1)
          (oddKTheoryIntegerSign (-z + (-1)) •
            oddKTheoryIntegerInclusion (-z + (-1)) b) := by
      simp only [AdjointableMap.mul_apply, oddKTheoryReflectionOperator_inclusion,
        oddKTheorySignOperator_inclusion]
    _ = oddKTheoryIntegerSign (-z + (-1)) •
        oddKTheoryReflectionOperator (B := B) (-1)
          (oddKTheoryIntegerInclusion (-z + (-1)) b) :=
      (oddKTheoryReflectionOperator (B := B) (-1)).toCLM.map_smul _ _
    _ = oddKTheoryIntegerSign (-z + (-1)) • oddKTheoryIntegerInclusion z b := by
      rw [oddKTheoryReflectionOperator_inclusion, hz]
    _ = -(oddKTheoryIntegerSign z • oddKTheoryIntegerInclusion z b) := by
      rw [hs, neg_smul]
    _ = (-oddKTheorySignOperator) (oddKTheoryIntegerInclusion z b) := by
      rw [AdjointableMap.coe_neg_apply, oddKTheorySignOperator_inclusion]

end BC4lean.KKTheory
