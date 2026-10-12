import BC4lean.CliffordCoefficientGrading
import BC4lean.KasparovDirectSum
import BC4lean.KasparovInverseRotation
import Mathlib.Tactic.NoncommRing

/-! # The signed odd source cycle for Cl₁(B)

The carrier is the genuine C-valued Hilbert sum H ⊕ H. The source
coordinates act diagonally, the grading exchanges the two summands, and
the operator is the Pauli matrix σ_y times the original odd Fredholm
operator. In particular this is not the incorrect signed diagonal operator,
which does not graded-commute with the source Clifford generator.

This file constructs actual cycle data. Identification with the external
Clifford tensor and its Cl₂ Morita reduction is a separate construction.
-/

noncomputable section
namespace BC4lean.KKTheory

namespace CliffordOddSourceCycle

variable {C H : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H] [CStarModule Cᵐᵒᵖ H]

def offDiagonal (S T : AdjointableMap C H H) :
    AdjointableMap C (HilbertModuleSum C H H) (HilbertModuleSum C H H) :=
  sumInl.comp (S.comp sumSnd) + sumInr.comp (T.comp sumFst)

@[simp] theorem offDiagonal_apply (S T : AdjointableMap C H H)
    (x : HilbertModuleSum C H H) :
    offDiagonal S T x = sumMk (S x.snd) (T x.fst) := by
  simp [offDiagonal, AdjointableMap.comp_apply]

theorem offDiagonal_add (S T U V : AdjointableMap C H H) :
    offDiagonal (S + U) (T + V) = offDiagonal S T + offDiagonal U V := by
  ext x
  simp only [offDiagonal_apply, AdjointableMap.coe_add_apply, sumMk_add]

theorem offDiagonal_sub (S T U V : AdjointableMap C H H) :
    offDiagonal (S - U) (T - V) = offDiagonal S T - offDiagonal U V := by
  ext x
  apply Prod.ext <;>
    simp only [offDiagonal_apply, AdjointableMap.coe_sub_apply,
      sumMk_fst, sumMk_snd, WithCStarModule.sub_fst, WithCStarModule.sub_snd]

theorem offDiagonal_star (S T : AdjointableMap C H H) :
    star (offDiagonal S T) = offDiagonal (star T) (star S) := by
  simp only [offDiagonal, star_add, AdjointableMap.star_eq_adjoint,
    AdjointableMap.adjoint_comp, sumInl_adjoint, sumInr_adjoint,
    sumFst_adjoint, sumSnd_adjoint]
  rw [add_comm]
  rfl

theorem offDiagonal_isModuleCompact {S T : AdjointableMap C H H}
    (hS : IsModuleCompact S) (hT : IsModuleCompact T) :
    IsModuleCompact (offDiagonal S T) :=
  ((hS.comp_right sumSnd).comp_left sumInl).add
    ((hT.comp_right sumFst).comp_left sumInr)

/-- The genuine Pauli σ_y Fredholm operator. -/
def operator (T : AdjointableMap C H H) :
    AdjointableMap C (HilbertModuleSum C H H) (HilbertModuleSum C H H) :=
  offDiagonal ((-Complex.I) • T) (Complex.I • T)

@[simp] theorem operator_apply (T : AdjointableMap C H H)
    (x : HilbertModuleSum C H H) :
    operator T x = sumMk ((-Complex.I) • T x.snd) (Complex.I • T x.fst) := by
  simp only [operator, offDiagonal_apply, AdjointableMap.coe_smul_apply]

theorem operator_star (T : AdjointableMap C H H) :
    star (operator T) = operator (star T) := by
  simp only [operator, offDiagonal_star, star_smul, star_neg,
    Complex.star_def, Complex.conj_I, neg_neg]

theorem operator_sub (T S : AdjointableMap C H H) :
    operator (T - S) = operator T - operator S := by
  simp only [operator, smul_sub, offDiagonal_sub]

theorem operator_square (T : AdjointableMap C H H) :
    operator T * operator T = sumMap (T * T) (T * T) := by
  ext x
  apply Prod.ext <;>
    simp only [AdjointableMap.mul_apply, operator_apply, sumMk_fst,
      sumMk_snd, sumMap_apply, map_smul, smul_smul,
      neg_mul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]

theorem operator_mul_diagonal (T R S : AdjointableMap C H H) :
    operator T * sumMap R S =
      offDiagonal ((-Complex.I) • (T * S)) (Complex.I • (T * R)) := by
  ext x
  simp only [AdjointableMap.mul_apply, operator_apply, sumMap_apply,
    offDiagonal_apply, AdjointableMap.coe_smul_apply, sumMk_fst, sumMk_snd]

theorem operator_graded_commutator (T R S : AdjointableMap C H H) :
    operator T * sumMap R S - sumMap S R * operator T =
      offDiagonal ((-Complex.I) • (T * S - S * T))
        (Complex.I • (T * R - R * T)) := by
  ext x
  apply Prod.ext <;>
    simp only [AdjointableMap.coe_sub_apply, AdjointableMap.mul_apply,
      operator_apply, offDiagonal_apply, sumMap_apply,
      sumMk_fst, sumMk_snd, WithCStarModule.sub_fst, WithCStarModule.sub_snd,
      map_smul, AdjointableMap.coe_smul_apply, smul_sub]

def grading : GradedHilbertModule (CStarGrading.trivial : CStarGrading C)
    (HilbertModuleSum C H H) where
  grading := sumSwap
  involutive x := by exact Prod.ext rfl rfl
  inner_grading x y := by
    simpa only [CStarGrading.op_trivial_apply] using sumSwap_inner x y

theorem operator_odd (T : AdjointableMap C H H) :
    grading.IsOdd grading (operator T) := by
  intro x
  apply Prod.ext <;>
    simp only [grading, sumSwap_apply, operator_apply, sumMk_fst,
      sumMk_snd, neg_smul, WithCStarModule.neg_fst, WithCStarModule.neg_snd, neg_neg]

section Equivariance
variable {Γ : Type*} [Group Γ] {γ : CStarAlgebraAction Γ C}

theorem conjugate_operator (U : EquivariantHilbertModule γ H)
    (g : Γ) (T : AdjointableMap C H H) :
    (U.sum U).conjugateOperator g (operator T) =
      operator (U.conjugateOperator g T) := by
  ext x
  apply Prod.ext <;>
    simp only [EquivariantHilbertModule.conjugateMap_apply,
      EquivariantHilbertModule.sum_action_apply, operator_apply,
      sumMk_fst, sumMk_snd, map_smul]

end Equivariance

section Cycle

variable {Γ B : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [CompleteSpace H] {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

local instance cliffordOddSourceCycleLocalInstance1 : CompleteSpace (HilbertModuleSum C H H) := hilbertModuleSum_complete

def representation (φ : B →⋆ₙₐ[ℂ] AdjointableMap C H H) :
    (B × B) →⋆ₙₐ[ℂ] AdjointableMap C (HilbertModuleSum C H H) (HilbertModuleSum C H H) where
  toFun b := sumMap (φ b.1) (φ b.2)
  map_zero' := by
    change sumMap (φ (0 : B)) (φ (0 : B)) = 0
    simp only [map_zero, sumMap_zero]
  map_add' b c := by simp only [Prod.fst_add, Prod.snd_add, map_add, sumMap_add]
  map_mul' b c := by simp only [Prod.fst_mul, Prod.snd_mul, map_mul, sumMap_mul]
  map_smul' a b := by
    change sumMap (φ (a • b.1)) (φ (a • b.2)) = _
    simp only [map_smul, sumMap_smul, MonoidHom.id_apply]
  map_star' b := by simp only [Prod.fst_star, Prod.snd_star, map_star, sumMap_star]

/-- Actual graded Cl₁(B)-to-C cycle data, with all four defects discharged
from the given genuine odd cycle. -/
def cycle (c : OddKasparovCycle β γ H) :
    GradedKasparovCycle (cliffordCoefficientAction β) γ
      cliffordCoefficientGrading CStarGrading.trivial (HilbertModuleSum C H H) where
  sourceAction_preservesGrading := cliffordCoefficientAction_preservesGrading β
  coefficientAction_preservesGrading := γ.preservesGrading_trivial
  countablyGenerated := c.countablyGenerated.sum c.countablyGenerated
  grading := grading
  groupAction := c.groupAction.sum c.groupAction
  grading_preserved _ _ := rfl
  representation := representation c.representation
  representation_graded b x := by
    change sumSwap (sumMap (c.representation b.1) (c.representation b.2) x) =
      sumMap (c.representation b.2) (c.representation b.1) (sumSwap x)
    simp only [sumSwap_apply, sumMap_apply, sumMk_fst, sumMk_snd]
  representation_equivariant g b := by
    change (c.groupAction.sum c.groupAction).conjugateOperator g
      (sumMap (c.representation b.1) (c.representation b.2)) = _
    rw [EquivariantHilbertModule.sum_conjugateOperator,
      c.representation_equivariant, c.representation_equivariant]
    rfl
  operator := operator c.operator
  operator_odd := operator_odd c.operator
  selfadjoint_mod_compact b := by
    change IsModuleCompact ((operator c.operator - star (operator c.operator)) *
      sumMap (c.representation b.1) (c.representation b.2))
    rw [operator_star, ← operator_sub, operator_mul_diagonal]
    exact offDiagonal_isModuleCompact
      ((c.selfadjoint_mod_compact b.2).smul (-Complex.I))
      ((c.selfadjoint_mod_compact b.1).smul Complex.I)
  square_mod_compact b := by
    change IsModuleCompact ((operator c.operator * operator c.operator - 1) *
      sumMap (c.representation b.1) (c.representation b.2))
    rw [operator_square, ← sumMap_one, ← sumMap_sub, ← sumMap_mul]
    exact (c.square_mod_compact b.1).sumMap (c.square_mod_compact b.2)
  commutator_compact b := by
    change IsModuleCompact (operator c.operator * sumMap (c.representation b.1) (c.representation b.2) -
      sumMap (c.representation b.2) (c.representation b.1) * operator c.operator)
    rw [operator_graded_commutator]
    exact offDiagonal_isModuleCompact
      ((c.commutator_compact b.2).smul (-Complex.I))
      ((c.commutator_compact b.1).smul Complex.I)
  equivariance_mod_compact g b := by
    change IsModuleCompact (((c.groupAction.sum c.groupAction).conjugateOperator g
      (operator c.operator) - operator c.operator) *
        sumMap (c.representation b.1) (c.representation b.2))
    rw [conjugate_operator, ← operator_sub, operator_mul_diagonal]
    exact offDiagonal_isModuleCompact
      ((c.equivariance_mod_compact g b.2).smul (-Complex.I))
      ((c.equivariance_mod_compact g b.1).smul Complex.I)

end Cycle
end CliffordOddSourceCycle
end BC4lean.KKTheory
