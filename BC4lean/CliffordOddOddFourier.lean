import BC4lean.CliffordQuarterPhaseConnection
import BC4lean.CliffordOddPauliRotation
import BC4lean.KasparovDirectSumIso
import Mathlib.Tactic.Ring

/-! # A genuine Pauli Fourier unitary for odd-odd-odd coherence

The scalar α=(1+i)/2 gives the exact unitary matrix
[[α,α],[iα,−iα]]. It sends swap to the signed diagonal and the signed
diagonal to σ_y. The second coefficient coordinate uses X V X, so the
entire product-coefficient grading and both source coordinates match.
No unit of the coefficient algebra occurs.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordOddOddFourier
open CliffordQuarterPhase

variable {C M : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Cᵐᵒᵖ M] [CStarModule Cᵐᵒᵖ M]

abbrev Sum := HilbertModuleSum C M M

def alpha : ℂ := (1 + Complex.I) / 2

private theorem alpha_norm : star alpha * alpha = (1 / 2 : ℂ) := by
  simp only [alpha, star_div₀, star_add, star_one, star_ofNat,
    Complex.star_def, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem alpha_norm_reverse : alpha * star alpha = (1 / 2 : ℂ) := by
  rw [mul_comm, alpha_norm]

private theorem alpha_minus_I : star alpha - Complex.I * star alpha = -Complex.I := by
  simp only [alpha, star_div₀, star_add, star_one, star_ofNat,
    Complex.star_def, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem alpha_plus_I : star alpha + Complex.I * star alpha = 1 := by
  simp only [alpha, star_div₀, star_add, star_one, star_ofNat,
    Complex.star_def, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

def sign : AdjointableMap C (Sum (C := C) (M := M)) (Sum (C := C) (M := M)) := sumMap 1 (-1)

@[simp] theorem sign_apply (x : Sum (C := C) (M := M)) : sign x = sumMk x.fst (-x.snd) := by
  simp only [sign, sumMap_apply, AdjointableMap.one_apply, AdjointableMap.coe_neg_apply]

@[simp] theorem sign_star : star (sign (C := C) (M := M)) = sign := by
  simp only [sign, ← sumMap_star, star_one, star_neg]

@[simp] theorem sign_square : sign (C := C) (M := M) * sign = 1 := by
  simp only [sign, ← sumMap_mul, one_mul, neg_mul_neg, sumMap_one]

def unnormalized : AdjointableMap C (Sum (C := C) (M := M)) (Sum (C := C) (M := M)) := sign + sumFlip

@[simp] theorem unnormalized_star : star (unnormalized (C := C) (M := M)) = unnormalized := by
  simp only [unnormalized, star_add, sign_star, sumFlip_star]

theorem unnormalized_square : unnormalized (C := C) (M := M) * unnormalized = (2 : ℂ) • 1 := by
  have ha : sign (C := C) (M := M) * sumFlip + sumFlip * sign = 0 :=
    sumFlip_anticommutes_signed_diagonal (1 : AdjointableMap C M M)
  calc
    _ = sign * sign + (sign * sumFlip + sumFlip * sign) + sumFlip * sumFlip := by
      dsimp [unnormalized]
      noncomm_ring
    _ = (2 : ℂ) • 1 := by rw [sign_square, ha, sumFlip_square]; module

def phases : AdjointableMap C (Sum (C := C) (M := M)) (Sum (C := C) (M := M)) :=
  sumMap (alpha • 1) ((Complex.I * alpha) • 1)

private theorem phases_star_mul : star (phases (C := C) (M := M)) * phases = (1 / 2 : ℂ) • 1 := by
  have hI : star Complex.I = -Complex.I := by
    simp only [Complex.star_def, Complex.conj_I]
  simp only [phases, ← sumMap_star, ← sumMap_mul, star_smul, star_one,
    smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, star_mul, hI]
  have hi : (Complex.I * alpha) * (star alpha * -Complex.I) = (1 / 2 : ℂ) := by
    calc
      _ = alpha * star alpha := by ring_nf; simp only [Complex.I_sq]; ring
      _ = _ := alpha_norm_reverse
  rw [alpha_norm_reverse, hi, sumMap_smul, sumMap_one]

private theorem phases_mul_star : phases (C := C) (M := M) * star phases = (1 / 2 : ℂ) • 1 := by
  have h := phases_star_mul (C := C) (M := M)
  have hc : phases (C := C) (M := M) * star phases = star phases * phases := by
    simp only [phases, ← sumMap_star, ← sumMap_mul, star_smul, star_one,
      smul_mul_assoc, mul_smul_comm, smul_smul, one_mul]
    congr 1 <;> congr 1 <;> exact mul_comm _ _
  exact hc.trans h

def operator : AdjointableMap C (Sum (C := C) (M := M)) (Sum (C := C) (M := M)) :=
  phases * unnormalized

theorem operator_star_mul : star (operator (C := C) (M := M)) * operator = 1 := by
  simp only [operator, star_mul, unnormalized_star]
  calc
    _ = unnormalized * (star phases * phases) * unnormalized := by noncomm_ring
    _ = 1 := by
      rw [phases_star_mul, mul_smul_comm, mul_one, smul_mul_assoc, unnormalized_square,
        smul_smul]
      norm_num

theorem operator_mul_star : operator (C := C) (M := M) * star operator = 1 := by
  simp only [operator, star_mul, unnormalized_star]
  calc
    _ = phases * (unnormalized * unnormalized) * star phases := by noncomm_ring
    _ = 1 := by
      rw [unnormalized_square, mul_smul_comm, mul_one, smul_mul_assoc, phases_mul_star,
        smul_smul]
      norm_num

def unitaryOperator : unitary (AdjointableMap C (Sum (C := C) (M := M)) (Sum (C := C) (M := M))) :=
  ⟨operator, ⟨operator_star_mul, operator_mul_star⟩⟩

def hilbertEquiv : HilbertModuleEquiv C (Sum (C := C) (M := M)) (Sum (C := C) (M := M)) :=
  HilbertModuleEquiv.ofAdjointableUnitary unitaryOperator

@[simp] theorem operator_apply (x : Sum (C := C) (M := M)) :
    operator x = sumMk (alpha • (x.fst + x.snd)) ((Complex.I * alpha) • (x.fst - x.snd)) := by
  simp only [operator, phases, unnormalized, AdjointableMap.mul_apply,
    AdjointableMap.coe_add_apply, sign_apply, sumFlip_apply, sumMap_apply,
    sumMk_add, sumMk_fst, sumMk_snd, AdjointableMap.coe_smul_apply,
    AdjointableMap.one_apply, sub_eq_add_neg, add_comm]

@[simp] theorem operator_star_apply (x : Sum (C := C) (M := M)) :
    star operator x = sumMk
      (star alpha • x.fst - (Complex.I * star alpha) • x.snd)
      (star alpha • x.fst + (Complex.I * star alpha) • x.snd) := by
  rw [operator, star_mul, unnormalized_star]
  have hI : star Complex.I = -Complex.I := by
    simp only [Complex.star_def, Complex.conj_I]
  simp only [phases, ← sumMap_star, star_smul, star_one, star_mul, hI,
    AdjointableMap.mul_apply, sumMap_apply, AdjointableMap.coe_smul_apply,
    AdjointableMap.coe_neg_apply, AdjointableMap.one_apply, unnormalized, AdjointableMap.coe_add_apply,
    sign_apply, sumFlip_apply, sumMk_fst, sumMk_snd, sumMk_add,
    neg_mul, mul_comm, neg_smul, neg_neg, sub_eq_add_neg, add_comm]

@[simp] theorem hilbertEquiv_apply (x : Sum (C := C) (M := M)) : hilbertEquiv x = operator x := rfl
@[simp] theorem hilbertEquiv_symm_apply (x : Sum (C := C) (M := M)) : hilbertEquiv.symm x = star operator x := rfl

theorem operator_swap (x : Sum (C := C) (M := M)) : operator (sumSwap x) = sign (operator x) := by
  apply Prod.ext <;> simp only [operator_apply, sumSwap_apply, sign_apply, sumMk_fst, sumMk_snd]
  · rw [add_comm]
  · rw [← smul_neg]; congr 1; abel

theorem operator_signed (A : AdjointableMap C M M) (x : Sum (C := C) (M := M)) :
    operator (sumMap A (-A) x) = CliffordOddSourceCycle.operator A (operator x) := by
  have hI : Complex.I * (Complex.I * alpha) = -alpha := by
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  apply Prod.ext <;>
    simp only [operator_apply, sumMap_apply, AdjointableMap.coe_neg_apply,
      CliffordOddSourceCycle.operator_apply, sumMk_fst, sumMk_snd,
      map_add, map_sub, map_smul, smul_smul, hI, neg_mul,
      sub_neg_eq_add, neg_neg]
  module

def oppositeEquiv : HilbertModuleEquiv C (Sum (C := C) (M := M)) (Sum (C := C) (M := M)) :=
  HilbertModuleEquiv.sumSwapEquiv.trans (hilbertEquiv.trans HilbertModuleEquiv.sumSwapEquiv)

@[simp] theorem oppositeEquiv_apply (x : Sum (C := C) (M := M)) :
    oppositeEquiv x = sumSwap (operator (sumSwap x)) := rfl

@[simp] theorem oppositeEquiv_symm_apply (x : Sum (C := C) (M := M)) :
    oppositeEquiv.symm x = sumSwap (star operator (sumSwap x)) := rfl

def pairEquiv : HilbertModuleEquiv (C × C)
    (CliffordPairModule C (Sum (C := C) (M := M)))
    (CliffordPairModule C (Sum (C := C) (M := M))) where
  linearIsometryEquiv :=
    { toFun x := cliffordPairMk (hilbertEquiv x.1) (oppositeEquiv x.2)
      invFun x := cliffordPairMk (hilbertEquiv.symm x.1) (oppositeEquiv.symm x.2)
      left_inv x := by apply Prod.ext <;> simp only [cliffordPairMk,
        HilbertModuleEquiv.symm_apply_apply]
      right_inv x := by apply Prod.ext <;> simp only [cliffordPairMk,
        HilbertModuleEquiv.apply_symm_apply]
      map_add' x y := by apply Prod.ext <;> exact map_add _ _ _
      map_smul' a x := by apply Prod.ext <;> exact map_smul _ _ _
      norm_map' x := by
        change max ‖hilbertEquiv x.1‖ ‖oppositeEquiv x.2‖ = max ‖x.1‖ ‖x.2‖
        rw [HilbertModuleEquiv.norm_map, HilbertModuleEquiv.norm_map] }
  inner_map x y := by
    apply MulOpposite.unop_injective
    apply Prod.ext
    · exact congrArg MulOpposite.unop (hilbertEquiv.inner_map x.1 y.1)
    · exact congrArg MulOpposite.unop (oppositeEquiv.inner_map x.2 y.2)

@[simp] theorem pairEquiv_apply (x : CliffordPairModule C (Sum (C := C) (M := M))) :
    pairEquiv x = cliffordPairMk (operator x.1) (oppositeEquiv x.2) := rfl

@[simp] theorem pairEquiv_symm_apply (x : CliffordPairModule C (Sum (C := C) (M := M))) :
    pairEquiv.symm x = cliffordPairMk (star operator x.1) (oppositeEquiv.symm x.2) := rfl

theorem pairEquiv_grading (x : CliffordPairModule C (Sum (C := C) (M := M))) :
    pairEquiv ((cliffordExternalEvenGrading CliffordOddSourceCycle.grading).grading x) =
      (cliffordExternalEvenGrading CliffordOddSourceCycle.grading).grading (pairEquiv x) := by
  change cliffordPairMk (operator (sumSwap x.2)) (oppositeEquiv (sumSwap x.1)) =
    cliffordPairMk (sumSwap (oppositeEquiv x.2)) (sumSwap (operator x.1))
  have hswap (z : Sum (C := C) (M := M)) : sumSwap (sumSwap z) = z := by
    apply Prod.ext <;> rfl
  apply Prod.ext <;> simp only [cliffordPairMk, oppositeEquiv_apply, hswap]

theorem oppositeEquiv_signed (A : AdjointableMap C M M) (x : Sum (C := C) (M := M)) :
    oppositeEquiv (sumMap A (-A) x) = CliffordOddSourceCycle.operator A (oppositeEquiv x) := by
  have hX (z : Sum (C := C) (M := M)) :
      sumSwap (CliffordOddSourceCycle.operator A z) = -CliffordOddSourceCycle.operator A (sumSwap z) :=
    CliffordOddSourceCycle.operator_odd A z
  have hZ (z : Sum (C := C) (M := M)) :
      sumSwap (sumMap A (-A) z) = -sumMap A (-A) (sumSwap z) := by
    apply Prod.ext <;> simp only [sumSwap_apply, sumMap_apply, AdjointableMap.coe_neg_apply,
      sumMk_fst, sumMk_snd, WithCStarModule.neg_fst, WithCStarModule.neg_snd, neg_neg]
  simp only [oppositeEquiv_apply, hZ, map_neg, operator_signed, hX, neg_neg]

theorem pairEquiv_signed (A : AdjointableMap C M M)
    (x : CliffordPairModule C (Sum (C := C) (M := M))) :
    pairEquiv (cliffordPairMap (sumMap A (-A)) (sumMap A (-A)) x) =
      cliffordPairMap (CliffordOddSourceCycle.operator A) (CliffordOddSourceCycle.operator A) (pairEquiv x) := by
  apply Prod.ext
  · exact operator_signed A x.1
  · exact oppositeEquiv_signed A x.2

section Creator
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]

theorem adjoint_column_even (T : AdjointableMap C F M) :
    (star operator).comp (column T T) = column ((-Complex.I) • T) T := by
  ext y
  apply Prod.ext <;>
    simp only [AdjointableMap.comp_apply, column, AdjointableMap.coe_add_apply, sumInl_apply, sumInr_apply,
      sumMk_add, add_zero, zero_add, operator_star_apply,
      sumMk_fst, sumMk_snd, AdjointableMap.coe_smul_apply]
  · exact (sub_smul (star alpha) (Complex.I * star alpha) (T y)).symm.trans
      (congrArg (fun z : ℂ => z • T y) alpha_minus_I)
  · simpa only [add_smul, one_smul] using
      congrArg (fun z : ℂ => z • T y) alpha_plus_I

theorem adjoint_column_odd (T : AdjointableMap C F M) :
    (star operator).comp (column T (-T)) = column T ((-Complex.I) • T) := by
  ext y
  apply Prod.ext <;>
    simp only [AdjointableMap.comp_apply, column, AdjointableMap.coe_add_apply, sumInl_apply, sumInr_apply,
      sumMk_add, add_zero, zero_add, operator_star_apply,
      sumMk_fst, sumMk_snd, AdjointableMap.coe_smul_apply, AdjointableMap.coe_neg_apply]
  · simpa only [smul_neg, sub_neg_eq_add, add_smul, one_smul] using
      congrArg (fun z : ℂ => z • T y) alpha_plus_I
  · simpa only [smul_neg, sub_eq_add_neg, neg_smul] using
      (sub_smul (star alpha) (Complex.I * star alpha) (T y)).symm.trans
        (congrArg (fun z : ℂ => z • T y) alpha_minus_I)

end Creator
end BC4lean.KKTheory.CliffordOddOddFourier
