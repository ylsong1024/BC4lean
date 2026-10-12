import BC4lean.OddFredholmFiniteCompression
import BC4lean.OddFredholmOperatorK1Index

/-! # Concrete common-corner comparison of two genuine odd cutoff indices

Two radius-one cutoff approximants are joined by their actual affine segment
inside that invertible neighbourhood. Polar normalization gives an actual
compact unitary path supported in the first n+m coordinates. Its genuine
finite compression yields an actual scalar-identity finite matrix path.
Relating each enlarged endpoint to its original finite size is a further
stabilization calculation, not an additional existence hypothesis.
-/

noncomputable section
namespace BC4lean.KKTheory

open unitInterval
open scoped CStarAlgebra

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

local instance oddContinuationOddFredholmCutoffComparisonLocalInstance01 : PartialOrder (OddFredholmStandardOperator B) := CStarAlgebra.spectralOrder _
local instance oddContinuationOddFredholmCutoffComparisonLocalInstance02 : StarOrderedRing (OddFredholmStandardOperator B) := CStarAlgebra.spectralOrderedRing _

theorem oddFredholmStandardCutoff_mul_of_le {n N : ℕ} (h : n ≤ N) :
    standardCountableCutoff (B := B) n * standardCountableCutoff N = standardCountableCutoff n := by
  apply standardCountable_adjointable_ext_mk
  intro x
  simp only [AdjointableMap.mul_apply, standardCountableCutoff_mk]
  congr 1
  ext i
  simp only [Finsupp.filter_apply]
  split_ifs <;> try rfl
  all_goals omega

theorem oddFredholmStandardCutoff_mul_of_ge {n N : ℕ} (h : n ≤ N) :
    standardCountableCutoff (B := B) N * standardCountableCutoff n = standardCountableCutoff n := by
  have hs := congrArg star (oddFredholmStandardCutoff_mul_of_le (B := B) h)
  simpa only [star_mul, standardCountableCutoff_star] using hs

def oddFredholmCutoffComparisonAffine
    (U : unitary (OddFredholmStandardOperator B)) (n m : ℕ) (t : I) :
    OddFredholmStandardOperator B :=
  (1 - (t : ℝ)) • oddFredholmUnitaryCutoff U n + (t : ℝ) • oddFredholmUnitaryCutoff U m

theorem oddFredholmCutoffComparisonAffine_near
    (U : unitary (OddFredholmStandardOperator B)) (n m : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : _)‖ < 1)
    (hm : ‖oddFredholmUnitaryCutoff U m - (U : _)‖ < 1) (t : I) :
    ‖oddFredholmCutoffComparisonAffine U n m t - (U : _)‖ < 1 := by
  let r := max ‖oddFredholmUnitaryCutoff U n - (U : _)‖
    ‖oddFredholmUnitaryCutoff U m - (U : _)‖
  have hr : r < 1 := max_lt hn hm
  have htn : 0 ≤ (t : ℝ) := t.2.1
  have htn' : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.2.2
  have he : oddFredholmCutoffComparisonAffine U n m t - (U : _) =
      (1 - (t : ℝ)) • (oddFredholmUnitaryCutoff U n - (U : _)) +
        (t : ℝ) • (oddFredholmUnitaryCutoff U m - (U : _)) := by
    unfold oddFredholmCutoffComparisonAffine
    module
  rw [he]
  calc
    _ ≤ ‖(1 - (t : ℝ)) • (oddFredholmUnitaryCutoff U n - (U : _))‖ +
        ‖(t : ℝ) • (oddFredholmUnitaryCutoff U m - (U : _))‖ := norm_add_le _ _
    _ = (1 - (t : ℝ)) * ‖oddFredholmUnitaryCutoff U n - (U : _)‖ +
        (t : ℝ) * ‖oddFredholmUnitaryCutoff U m - (U : _)‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg htn', abs_of_nonneg htn]
    _ ≤ (1 - (t : ℝ)) * r + (t : ℝ) * r :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) htn')
        (mul_le_mul_of_nonneg_left (le_max_right _ _) htn)
    _ = r := by ring
    _ < 1 := hr

def oddFredholmCutoffComparisonUnitary
    (U : unitary (OddFredholmStandardOperator B)) (n m : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : _)‖ < 1)
    (hm : ‖oddFredholmUnitaryCutoff U m - (U : _)‖ < 1) (t : I) :
    unitary (OddFredholmStandardOperator B) :=
  oddFredholmPolarUnitary (oddFredholmCutoffComparisonAffine U n m t)
    (oddFredholmIsUnit_of_norm_sub_unitary_lt_one_all _ U
      (oddFredholmCutoffComparisonAffine_near U n m hn hm t))

theorem continuous_oddFredholmCutoffComparisonUnitary
    (U : unitary (OddFredholmStandardOperator B)) (n m : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : _)‖ < 1)
    (hm : ‖oddFredholmUnitaryCutoff U m - (U : _)‖ < 1) :
    Continuous (oddFredholmCutoffComparisonUnitary U n m hn hm) :=
  (continuousOn_oddFredholmPolarElement.comp_continuous
    (by unfold oddFredholmCutoffComparisonAffine; fun_prop)
    (fun t => oddFredholmIsUnit_of_norm_sub_unitary_lt_one_all _ U
      (oddFredholmCutoffComparisonAffine_near U n m hn hm t))).subtype_mk _

@[simp] theorem oddFredholmCutoffComparisonUnitary_zero
    (U : unitary (OddFredholmStandardOperator B)) (n m : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : _)‖ < 1)
    (hm : ‖oddFredholmUnitaryCutoff U m - (U : _)‖ < 1) :
    oddFredholmCutoffComparisonUnitary U n m hn hm 0 = oddFredholmStandardCutoffPolarUnitary U n hn := by
  apply Subtype.ext
  simp [oddFredholmCutoffComparisonUnitary, oddFredholmCutoffComparisonAffine,
    oddFredholmStandardCutoffPolarUnitary]

@[simp] theorem oddFredholmCutoffComparisonUnitary_one
    (U : unitary (OddFredholmStandardOperator B)) (n m : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : _)‖ < 1)
    (hm : ‖oddFredholmUnitaryCutoff U m - (U : _)‖ < 1) :
    oddFredholmCutoffComparisonUnitary U n m hn hm 1 = oddFredholmStandardCutoffPolarUnitary U m hm := by
  apply Subtype.ext
  simp [oddFredholmCutoffComparisonUnitary, oddFredholmCutoffComparisonAffine,
    oddFredholmStandardCutoffPolarUnitary]

theorem oddFredholmCutoffComparisonUnitary_compact
    (U : unitary (OddFredholmStandardOperator B))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) (n m : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : _)‖ < 1)
    (hm : ‖oddFredholmUnitaryCutoff U m - (U : _)‖ < 1) (t : I) :
    IsModuleCompact ((oddFredholmCutoffComparisonUnitary U n m hn hm t : OddFredholmStandardOperator B) - 1) := by
  apply oddFredholmPolarElement_sub_one_isModuleCompact _
    (oddFredholmIsUnit_of_norm_sub_unitary_lt_one_all _ U
      (oddFredholmCutoffComparisonAffine_near U n m hn hm t))
  have he : oddFredholmCutoffComparisonAffine U n m t - 1 =
      (1 - (t : ℝ)) • (oddFredholmUnitaryCutoff U n - 1) +
        (t : ℝ) • (oddFredholmUnitaryCutoff U m - 1) := by
    unfold oddFredholmCutoffComparisonAffine
    module
  rw [he, RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact ((oddFredholmUnitaryCutoff_sub_one_isModuleCompact U hU n).smul _).add
    ((oddFredholmUnitaryCutoff_sub_one_isModuleCompact U hU m).smul _)

theorem oddFredholmUnitaryCutoff_right_larger_tail
    (U : unitary (OddFredholmStandardOperator B)) {n N : ℕ} (h : n ≤ N) :
    oddFredholmUnitaryCutoff U n * (1 - standardCountableCutoff N) = 1 - standardCountableCutoff N := by
  have hz : standardCountableCutoff (B := B) n * (1 - standardCountableCutoff N) = 0 := by
    rw [mul_sub, mul_one, oddFredholmStandardCutoff_mul_of_le h, sub_self]
  simp only [oddFredholmUnitaryCutoff, add_mul, one_mul, mul_assoc, hz, mul_zero, add_zero]

theorem oddFredholmUnitaryCutoff_left_larger_tail
    (U : unitary (OddFredholmStandardOperator B)) {n N : ℕ} (h : n ≤ N) :
    (1 - standardCountableCutoff N) * oddFredholmUnitaryCutoff U n = 1 - standardCountableCutoff N := by
  have hz : (1 - standardCountableCutoff (B := B) N) * standardCountableCutoff n = 0 := by
    rw [sub_mul, one_mul, oddFredholmStandardCutoff_mul_of_ge h, sub_self]
  simp only [oddFredholmUnitaryCutoff, mul_add, mul_one, ← mul_assoc, hz, zero_mul, add_zero]

theorem oddFredholmCutoffComparisonUnitary_tail
    (U : unitary (OddFredholmStandardOperator B)) (n m : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : _)‖ < 1)
    (hm : ‖oddFredholmUnitaryCutoff U m - (U : _)‖ < 1) (t : I) :
    (oddFredholmCutoffComparisonUnitary U n m hn hm t : OddFredholmStandardOperator B) *
      (1 - standardCountableCutoff (n + m)) = 1 - standardCountableCutoff (n + m) := by
  apply oddFredholmPolarElement_right_tail _ _
    (oddFredholmIsUnit_of_norm_sub_unitary_lt_one_all _ U
      (oddFredholmCutoffComparisonAffine_near U n m hn hm t))
    (by rw [star_sub, star_one, standardCountableCutoff_star])
  · simp only [oddFredholmCutoffComparisonAffine, add_mul, smul_mul_assoc,
      oddFredholmUnitaryCutoff_right_larger_tail U (Nat.le_add_right n m),
      oddFredholmUnitaryCutoff_right_larger_tail U (Nat.le_add_left m n)]
    module
  · simp only [oddFredholmCutoffComparisonAffine, mul_add, mul_smul_comm,
      oddFredholmUnitaryCutoff_left_larger_tail U (Nat.le_add_right n m),
      oddFredholmUnitaryCutoff_left_larger_tail U (Nat.le_add_left m n)]
    module

def oddFredholmCutoffComparisonFiniteUnitary
    (U : unitary (OddFredholmStandardOperator B))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) (n m : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : _)‖ < 1)
    (hm : ‖oddFredholmUnitaryCutoff U m - (U : _)‖ < 1) (t : I) :
    unitary (CStarMatrix (Fin (n + m)) (Fin (n + m)) (Unitization ℂ B)) :=
  oddFredholmSupportedFiniteUnitary (oddFredholmCutoffComparisonUnitary U n m hn hm t)
    (oddFredholmCutoffComparisonUnitary_compact U hU n m hn hm t) (n + m)
    (oddFredholmCutoffComparisonUnitary_tail U n m hn hm t)

theorem continuous_oddFredholmCutoffComparisonFiniteUnitary
    (U : unitary (OddFredholmStandardOperator B))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) (n m : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : _)‖ < 1)
    (hm : ‖oddFredholmUnitaryCutoff U m - (U : _)‖ < 1) :
    Continuous (oddFredholmCutoffComparisonFiniteUnitary U hU n m hn hm) :=
  continuous_oddFredholmSupportedFiniteUnitary _ _ _ _
    (continuous_oddFredholmCutoffComparisonUnitary U n m hn hm)

end BC4lean.KKTheory
