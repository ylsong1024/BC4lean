import BC4lean.CliffordOddSourceCycle
import BC4lean.HilbertModuleEquiv
import BC4lean.CliffordOne
import Mathlib.Tactic.Module

/-! # The actual Pauli row unitary for odd external Clifford coordinates

The unitary is Q₊(σₓ)+i Q₋(σₓ). Its eigenvalues are 1 and i, so its
unitarity follows from the genuine universal Clifford representation. It
commutes with the swap grading and converts σ_y D into diag(D,−D).
Only complex scalar phases occur; the coefficient algebra may be nonunital.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordOddPauliRotation
open scoped InnerProductSpace

variable {C H : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H] [CStarModule Cᵐᵒᵖ H]
  [CompleteSpace H]

local instance cliffordOddPauliRotationLocalInstance1 : CompleteSpace (HilbertModuleSum C H H) := hilbertModuleSum_complete

def alpha : ℂ := (1 + Complex.I) / 2
def beta : ℂ := (1 - Complex.I) / 2

private theorem alpha_mul_I : alpha * Complex.I = -beta := by
  unfold alpha beta
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem beta_mul_I : beta * Complex.I = alpha := by
  unfold alpha beta
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- A genuine adjointable coefficient-linear row unitary. -/
def rotation : AdjointableMap C (HilbertModuleSum C H H) (HilbertModuleSum C H H) :=
  CliffordOne.lift sumFlip sumFlip_star sumFlip_square (1, Complex.I)

theorem star_rotation_mul_rotation :
    star (rotation (C := C) (H := H)) * rotation = 1 := by
  have h : star ((1, Complex.I) : CliffordOne) * (1, Complex.I) = 1 := by
    apply Prod.ext <;> simp [Complex.conj_I, Complex.I_mul_I]
  change star (CliffordOne.lift sumFlip sumFlip_star sumFlip_square (1, Complex.I)) *
    CliffordOne.lift sumFlip sumFlip_star sumFlip_square (1, Complex.I) = 1
  rw [← map_star, ← map_mul, h, map_one]

theorem rotation_mul_star_rotation :
    rotation (C := C) (H := H) * star rotation = 1 := by
  have h : ((1, Complex.I) : CliffordOne) * star (1, Complex.I) = 1 := by
    apply Prod.ext <;> simp [Complex.conj_I, Complex.I_mul_I]
  change CliffordOne.lift sumFlip sumFlip_star sumFlip_square (1, Complex.I) *
    star (CliffordOne.lift sumFlip sumFlip_star sumFlip_square (1, Complex.I)) = 1
  rw [← map_star, ← map_mul, h, map_one]

theorem rotation_inner (x y : HilbertModuleSum C H H) :
    ⟪rotation x, rotation y⟫_(Cᵐᵒᵖ) = ⟪x, y⟫_(Cᵐᵒᵖ) := by
  rw [(rotation (C := C) (H := H)).adjoint_identity]
  change ⟪x, ((star (rotation (C := C) (H := H)) * rotation :
    AdjointableMap C (HilbertModuleSum C H H) (HilbertModuleSum C H H)) y)⟫_(Cᵐᵒᵖ) = _
  rw [star_rotation_mul_rotation, AdjointableMap.one_apply]

def hilbertEquiv : HilbertModuleEquiv C (HilbertModuleSum C H H) (HilbertModuleSum C H H) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun := rotation
          invFun := (star (rotation (C := C) (H := H)) :
            AdjointableMap C (HilbertModuleSum C H H) (HilbertModuleSum C H H))
          left_inv x := by
            simpa only [AdjointableMap.mul_apply, AdjointableMap.one_apply] using
              congrArg (fun T : AdjointableMap C (HilbertModuleSum C H H)
                (HilbertModuleSum C H H) => T x) star_rotation_mul_rotation
          right_inv x := by
            simpa only [AdjointableMap.mul_apply, AdjointableMap.one_apply] using
              congrArg (fun T : AdjointableMap C (HilbertModuleSum C H H)
                (HilbertModuleSum C H H) => T x) rotation_mul_star_rotation
          map_add' := rotation.toCLM.map_add
          map_smul' := rotation.toCLM.map_smul }
      norm_map' x := by
        change ‖rotation x‖ = ‖x‖
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ), rotation_inner,
          ← CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ)] }
  inner_map := rotation_inner

@[simp] theorem rotation_apply (x : HilbertModuleSum C H H) :
    rotation x = sumMk (alpha • x.fst + beta • x.snd) (beta • x.fst + alpha • x.snd) := by
  apply Prod.ext <;>
    simp only [rotation, CliffordOne.lift_apply, CliffordOne.plusProjection,
      CliffordOne.minusProjection, AdjointableMap.coe_add_apply,
      AdjointableMap.coe_sub_apply, AdjointableMap.coe_smul_apply,
      AdjointableMap.one_apply, sumFlip_apply, sumMk_fst, sumMk_snd,
      WithCStarModule.add_fst, WithCStarModule.add_snd,
      WithCStarModule.sub_fst, WithCStarModule.sub_snd,
      WithCStarModule.smul_fst, WithCStarModule.smul_snd, alpha, beta] <;> module

@[simp] theorem hilbertEquiv_apply (x : HilbertModuleSum C H H) :
    hilbertEquiv x = sumMk (alpha • x.fst + beta • x.snd) (beta • x.fst + alpha • x.snd) :=
  rotation_apply x

theorem rotation_swap (x : HilbertModuleSum C H H) :
    rotation (sumSwap x) = sumSwap (rotation x) := by
  simp only [rotation_apply, sumSwap_apply, sumMk_fst, sumMk_snd]
  apply Prod.ext <;> exact add_comm _ _

/-- The genuine unitary intertwines the corrected Pauli operator and the
original signed diagonal odd operator. -/
theorem rotation_operator (T : AdjointableMap C H H) (x : HilbertModuleSum C H H) :
    rotation (CliffordOddSourceCycle.operator T x) = sumMap T (-T) (rotation x) := by
  apply Prod.ext
  · simp only [rotation_apply, CliffordOddSourceCycle.operator_apply,
      sumMap_apply, sumMk_fst, sumMk_snd]
    simp only [map_add, map_smul]
    rw [smul_smul, smul_smul, mul_neg, alpha_mul_I, beta_mul_I, neg_neg]
    exact add_comm _ _
  · simp only [rotation_apply, CliffordOddSourceCycle.operator_apply,
      sumMap_apply, sumMk_fst, sumMk_snd, AdjointableMap.coe_neg_apply]
    simp only [map_add, map_smul]
    rw [smul_smul, smul_smul, mul_neg, beta_mul_I, alpha_mul_I]
    simp only [neg_smul, neg_add]
    abel

/-- The original source Clifford generator becomes −σ_y on the row coordinates. -/
theorem rotation_signed_diagonal (T : AdjointableMap C H H)
    (x : HilbertModuleSum C H H) :
    rotation (sumMap T (-T) x) = CliffordOddSourceCycle.operator (-T) (rotation x) := by
  have hAlpha : (-Complex.I) * alpha = beta := by
    rw [neg_mul, mul_comm Complex.I alpha, alpha_mul_I, neg_neg]
  have hBeta : (-Complex.I) * beta = -alpha := by
    rw [neg_mul, mul_comm Complex.I beta, beta_mul_I]
  apply Prod.ext
  · simp only [rotation_apply, CliffordOddSourceCycle.operator_apply,
      sumMap_apply, sumMk_fst, sumMk_snd, AdjointableMap.coe_neg_apply]
    simp only [map_add, map_smul]
    rw [smul_neg, smul_neg, smul_add, smul_smul, smul_smul, hBeta, hAlpha]
    simp only [neg_smul, neg_add, neg_neg]
  · simp only [rotation_apply, CliffordOddSourceCycle.operator_apply,
      sumMap_apply, sumMk_fst, sumMk_snd, AdjointableMap.coe_neg_apply]
    simp only [map_add, map_smul]
    rw [smul_neg, smul_neg, smul_add, smul_smul, smul_smul,
      mul_comm Complex.I alpha, mul_comm Complex.I beta, alpha_mul_I, beta_mul_I]
    simp only [neg_smul, neg_add, neg_neg]

end BC4lean.KKTheory.CliffordOddPauliRotation
