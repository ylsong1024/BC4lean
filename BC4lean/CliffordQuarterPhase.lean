import BC4lean.CliffordExternalEvenBalancedCompatibility
import BC4lean.CliffordOddSourceCycle
import BC4lean.AdjointableUnitaryHilbertModuleEquiv
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module

/-! # The actual quarter-phase unitary for the signed Clifford source

For a genuine grading K, the phases Q₊±iQ₋ are mutually adjoint unitary
operators and square to K. They exchange an odd operator by the exact
identities U₊DU₊=iD and U₋DU₋=−iD. These signs are needed to transfer all
four creator laws in the source-Clifford product comparison.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordQuarterPhase
open CliffordExternalEvenBalancedTensor CliffordExternalEvenRepresentation

variable {C M : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Cᵐᵒᵖ M] [CStarModule Cᵐᵒᵖ M]
  [CompleteSpace M]
  (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading C) M)

def upper : AdjointableMap C M M := plus J + Complex.I • minus J
def lower : AdjointableMap C M M := plus J - Complex.I • minus J

theorem upper_star : star (upper J) = lower J := by
  simp only [upper, lower, star_add, star_smul, AdjointableMap.star_eq_adjoint,
    plus_adjoint, minus_adjoint,
    Complex.star_def, Complex.conj_I, neg_smul, sub_eq_add_neg]

theorem lower_star : star (lower J) = upper J := by
  rw [← upper_star, star_star]

theorem upper_mul_lower : upper J * lower J = 1 := by
  simp only [upper, lower, mul_sub, add_mul, mul_smul_comm, smul_mul_assoc,
    smul_smul, plus_square, minus_square, plus_mul_minus, minus_mul_plus,
    smul_zero, zero_add, add_zero, Complex.I_mul_I, neg_one_smul]
  simpa only [sub_neg_eq_add] using plus_add_minus J

theorem lower_mul_upper : lower J * upper J = 1 := by
  simp only [upper, lower, mul_add, sub_mul, mul_smul_comm, smul_mul_assoc,
    smul_neg, smul_smul, plus_square, minus_square, plus_mul_minus, minus_mul_plus,
    smul_zero, zero_sub, sub_zero, Complex.I_mul_I, neg_one_smul]
  simpa only [sub_neg_eq_add, neg_neg] using plus_add_minus J

theorem upper_square : upper J * upper J = J.toAdjointable := by
  simp only [upper, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    smul_smul, plus_square, minus_square, plus_mul_minus, minus_mul_plus,
    smul_zero, zero_add, add_zero, Complex.I_mul_I, neg_one_smul]
  simp only [plus, minus, CliffordOne.plusProjection, CliffordOne.minusProjection]
  module

theorem lower_square : lower J * lower J = J.toAdjointable := by
  have h := congrArg star (upper_square J)
  simpa only [star_mul, upper_star, AdjointableMap.star_eq_adjoint J.toAdjointable,
    J.toAdjointable_adjoint] using h

theorem upper_mul_odd (D : AdjointableMap C M M) (hD : J.IsOdd J D) :
    upper J * D = Complex.I • (D * lower J) := by
  have hDP : D * plus J = minus J * D := odd_mul_plus J D hD
  have hDM : D * minus J = plus J * D := odd_mul_minus J D hD
  simp only [upper, lower, add_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    smul_sub, smul_smul, hDP, hDM, Complex.I_mul_I, neg_one_smul]
  module

theorem lower_mul_odd (D : AdjointableMap C M M) (hD : J.IsOdd J D) :
    lower J * D = (-Complex.I) • (D * upper J) := by
  have hDP : D * plus J = minus J * D := odd_mul_plus J D hD
  have hDM : D * minus J = plus J * D := odd_mul_minus J D hD
  simp only [upper, lower, sub_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    smul_add, smul_smul, hDP, hDM, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
  module

theorem upper_odd (D : AdjointableMap C M M) (hD : J.IsOdd J D) :
    upper J * D * upper J = Complex.I • D := by
  rw [upper_mul_odd J D hD, smul_mul_assoc, mul_assoc, lower_mul_upper, mul_one]

theorem lower_odd (D : AdjointableMap C M M) (hD : J.IsOdd J D) :
    lower J * D * lower J = (-Complex.I) • D := by
  rw [lower_mul_odd J D hD, smul_mul_assoc, mul_assoc, upper_mul_lower, mul_one]

def sumUnitary : unitary (AdjointableMap C (HilbertModuleSum C M M) (HilbertModuleSum C M M)) :=
  ⟨sumMap (upper J) (lower J), by
    constructor
    · change star (sumMap (upper J) (lower J)) * sumMap (upper J) (lower J) = 1
      rw [← sumMap_star, ← sumMap_mul, upper_star, lower_star,
        lower_mul_upper, upper_mul_lower, sumMap_one]
    · change sumMap (upper J) (lower J) * star (sumMap (upper J) (lower J)) = 1
      rw [← sumMap_star, ← sumMap_mul, upper_star, lower_star,
        upper_mul_lower, lower_mul_upper, sumMap_one]⟩

def sumEquiv : HilbertModuleEquiv C (HilbertModuleSum C M M) (HilbertModuleSum C M M) :=
  HilbertModuleEquiv.ofAdjointableUnitary (sumUnitary J)

@[simp] theorem sumEquiv_apply (x : HilbertModuleSum C M M) :
    sumEquiv J x = sumMk (upper J x.fst) (lower J x.snd) := by
  simp only [sumEquiv, HilbertModuleEquiv.ofAdjointableUnitary_apply,
    sumUnitary, sumMap_apply]

@[simp] theorem sumEquiv_symm_apply (x : HilbertModuleSum C M M) :
    (sumEquiv J).symm x = sumMk (lower J x.fst) (upper J x.snd) := by
  simp only [sumEquiv, HilbertModuleEquiv.ofAdjointableUnitary_symm_apply,
    sumUnitary, ← sumMap_star, upper_star, lower_star, sumMap_apply]

theorem sumEquiv_grading (x : HilbertModuleSum C M M) :
    sumEquiv J ((CliffordOddSourceCycle.grading (C := C) (H := M)).grading x) =
      sumMk (J.grading (sumEquiv J x).snd) (J.grading (sumEquiv J x).fst) := by
  have hUp : J.toAdjointable * upper J = lower J := by
    simp only [upper, lower, mul_add, mul_smul_comm, grading_mul_plus,
      grading_mul_minus, smul_neg, sub_eq_add_neg]
  have hLo : J.toAdjointable * lower J = upper J := by
    simp only [upper, lower, mul_sub, mul_smul_comm, grading_mul_plus,
      grading_mul_minus, smul_neg, sub_neg_eq_add]
  apply Prod.ext
  · simpa only [sumEquiv_apply, CliffordOddSourceCycle.grading, sumSwap_apply,
      sumMk_fst, sumMk_snd, AdjointableMap.mul_apply,
      GradedHilbertModule.toAdjointable_apply] using
      (congrArg (fun T : AdjointableMap C M M => T x.snd) hLo).symm
  · simpa only [sumEquiv_apply, CliffordOddSourceCycle.grading, sumSwap_apply,
      sumMk_fst, sumMk_snd, AdjointableMap.mul_apply,
      GradedHilbertModule.toAdjointable_apply] using
      (congrArg (fun T : AdjointableMap C M M => T x.fst) hUp).symm

end BC4lean.KKTheory.CliffordQuarterPhase
