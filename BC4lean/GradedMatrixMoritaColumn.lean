import BC4lean.GradedMatrixMoritaMatrix
import BC4lean.FiniteModuleCompactMatrix
import BC4lean.HilbertModuleCountableGenerationSeparable

/-! # The genuine graded matrix-B/B column module

The column uses the actual finite Hilbert B-module norm and inner product.
The matrix left action is the faithful adjointable action from ModuleGramMatrix.
Its range is proved to be exactly the actual compact operators. The column
grading changes the sign of its second coordinate and intertwines that action
with the actual matrix grading.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace WithCStarModule

abbrev GradedMatrixMoritaColumn (B : Type*) := FiniteStandardModule B (Fin 2)

namespace GradedMatrixMoritaColumn

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def parity (x : GradedMatrixMoritaColumn B) : GradedMatrixMoritaColumn B :=
  (WithCStarModule.equiv _ _).symm fun i => if i = 0 then x 0 else -x 1

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem parity_zero_apply (x : GradedMatrixMoritaColumn B) : parity x 0 = x 0 := by
  simp [parity]
omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem parity_one_apply (x : GradedMatrixMoritaColumn B) : parity x 1 = -x 1 := by
  simp [parity]

def parityLinear : GradedMatrixMoritaColumn B →ₗ[ℂ] GradedMatrixMoritaColumn B where
  toFun := parity
  map_add' x y := by ext i; fin_cases i <;> simp [WithCStarModule.add_apply, add_comm]
  map_smul' c x := by ext i; fin_cases i <;> simp [WithCStarModule.smul_apply]

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem parity_parity (x : GradedMatrixMoritaColumn B) : parity (parity x) = x := by
  ext i
  fin_cases i <;> simp

theorem inner_parity (x y : GradedMatrixMoritaColumn B) :
    ⟪parity x, parity y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) := by
  simp [WithCStarModule.pi_inner, WithCStarModule.inner_def, Fin.sum_univ_two]

theorem norm_parity (x : GradedMatrixMoritaColumn B) : ‖parity x‖ = ‖x‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ), inner_parity,
    ← CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ)]

def parityIsometry : GradedMatrixMoritaColumn B ≃ₗᵢ[ℂ] GradedMatrixMoritaColumn B where
  toLinearEquiv :=
    { toLinearMap := parityLinear
      invFun := parity
      left_inv := parity_parity
      right_inv := parity_parity }
  norm_map' := norm_parity

def grading : GradedHilbertModule (CStarGrading.trivial : CStarGrading B)
    (GradedMatrixMoritaColumn B) where
  grading := parityIsometry
  involutive := parity_parity
  inner_grading x y := by
    change ⟪parity x, parity y⟫_(Bᵐᵒᵖ) =
      opStarAlgEquiv (CStarGrading.trivial : CStarGrading B).automorphism ⟪x, y⟫_(Bᵐᵒᵖ)
    rw [CStarGrading.op_trivial_apply, inner_parity]

def leftAction : GradedMatrixMoritaMatrix B →⋆ₙₐ[ℂ]
    AdjointableMap B (GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn B) :=
  moduleMatrixRepresentation

/-- The actual matrix operator has its usual column formula. -/
theorem leftAction_apply (M : GradedMatrixMoritaMatrix B)
    (x : GradedMatrixMoritaColumn B) (i : Fin 2) :
    leftAction M x i = MulOpposite.op (∑ j : Fin 2, M i j * MulOpposite.unop (x j)) := by
  change (CStarMatrix.toCLM (moduleMatrixOpposite M) x) i = _
  apply MulOpposite.unop_injective
  simp only [CStarMatrix.toCLM_apply_eq_sum, WithCStarModule.equiv_symm_pi_apply,
    moduleMatrixOpposite_apply, Finset.unop_sum, MulOpposite.unop_mul,
    MulOpposite.unop_op]

/-- The actual column grading is compatible with the graded matrix left action. -/
theorem leftAction_graded (M : GradedMatrixMoritaMatrix B) (x : GradedMatrixMoritaColumn B) :
    parity (leftAction M x) = leftAction (GradedMatrixMoritaMatrix.parity M) (parity x) := by
  ext i
  apply MulOpposite.unop_injective
  fin_cases i <;>
    simp [leftAction_apply, GradedMatrixMoritaMatrix.parity, Fin.sum_univ_two]
  exact add_comm _ _

theorem leftAction_injective : Function.Injective (leftAction (B := B)) :=
  moduleMatrixRepresentation_injective

theorem leftAction_isometry : Isometry (leftAction (B := B)) :=
  moduleMatrixRepresentation_isometry

theorem leftAction_compact (M : GradedMatrixMoritaMatrix B) : IsModuleCompact (leftAction M) :=
  moduleMatrixRepresentation_isModuleCompact M

/-- Every actual compact operator has one unique actual coefficient matrix. -/
theorem compact_existsUnique_matrix
    (T : AdjointableMap B (GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn B))
    (hT : IsModuleCompact T) : ∃! M : GradedMatrixMoritaMatrix B, leftAction M = T := by
  obtain ⟨M, hM⟩ := finiteModuleCompact_exists_matrix hT
  exact ⟨M, hM, fun N hN => leftAction_injective (hN.trans hM.symm)⟩

/-- Separability supplies true countable generation by coefficient spans. -/
theorem countablyGenerated [TopologicalSpace.SeparableSpace B] : IsCountablyGeneratedModule B
    (GradedMatrixMoritaColumn B) := by
  let : TopologicalSpace.SeparableSpace Bᵐᵒᵖ :=
    (MulOpposite.op_surjective : Function.Surjective (MulOpposite.op : B → Bᵐᵒᵖ)).denseRange.separableSpace
      MulOpposite.continuous_op
  let e : GradedMatrixMoritaColumn B ≃L[ℂ] (Fin 2 → Bᵐᵒᵖ) :=
    WithCStarModule.equivL ℂ (A := Bᵐᵒᵖ) (E := Fin 2 → Bᵐᵒᵖ)
  let : TopologicalSpace.SeparableSpace (GradedMatrixMoritaColumn B) :=
    e.symm.surjective.denseRange.separableSpace e.symm.continuous
  exact isCountablyGeneratedModule_of_separableSpace

end GradedMatrixMoritaColumn
end BC4lean.KKTheory
