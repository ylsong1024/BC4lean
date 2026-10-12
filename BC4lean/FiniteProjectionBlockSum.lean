import BC4lean.FiniteProjectionKasparovCycle
import BC4lean.ProjectionModuleEquiv
import BC4lean.KasparovDirectSum

/-! # Concrete block sums of finite projection cycles

The sum-indexed finite standard module splits unitarily using the actual sum
of coefficient inner products. This equivalence intertwines the matrix block
action and restricts to projection-supported modules. The resulting cycle
isomorphism realizes the block-sum addition used by `StableProjectionMonoid`.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace Matrix

variable {B ι κ : Type*}

section NonUnital
variable [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype ι] [Fintype κ]

/-- Split a sum-indexed finite coefficient vector into its two coordinate families. -/
def finiteStandardSplit (x : FiniteStandardModule B (ι ⊕ κ)) :
    HilbertModuleSum B (FiniteStandardModule B ι) (FiniteStandardModule B κ) :=
  sumMk ((WithCStarModule.equiv _ _).symm fun i => x (Sum.inl i))
    ((WithCStarModule.equiv _ _).symm fun j => x (Sum.inr j))

omit [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [Fintype ι] [Fintype κ] in
@[simp] theorem finiteStandardSplit_fst (x : FiniteStandardModule B (ι ⊕ κ)) (i : ι) :
    (finiteStandardSplit x).fst i = x (Sum.inl i) := rfl
omit [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [Fintype ι] [Fintype κ] in
@[simp] theorem finiteStandardSplit_snd (x : FiniteStandardModule B (ι ⊕ κ)) (j : κ) :
    (finiteStandardSplit x).snd j = x (Sum.inr j) := rfl

theorem finiteStandardSplit_inner (x y : FiniteStandardModule B (ι ⊕ κ)) :
    ⟪finiteStandardSplit x, finiteStandardSplit y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) := by
  simp only [inner_sum, WithCStarModule.pi_inner, finiteStandardSplit_fst,
    finiteStandardSplit_snd, Fintype.sum_sum_type]

/-- Splitting the finite index sum is an actual Hilbert-module unitary. -/
def finiteStandardSumEquiv : HilbertModuleEquiv B (FiniteStandardModule B (ι ⊕ κ))
    (HilbertModuleSum B (FiniteStandardModule B ι) (FiniteStandardModule B κ)) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun := finiteStandardSplit
          invFun := fun y => (WithCStarModule.equiv _ _).symm (Sum.elim y.fst y.snd)
          left_inv := fun x => by
            apply (WithCStarModule.equiv Bᵐᵒᵖ ((ι ⊕ κ) → Bᵐᵒᵖ)).injective
            funext i
            cases i <;> rfl
          right_inv := fun y => by
            apply (WithCStarModule.equiv Bᵐᵒᵖ
              (FiniteStandardModule B ι × FiniteStandardModule B κ)).injective
            apply Prod.ext
            · apply (WithCStarModule.equiv Bᵐᵒᵖ (ι → Bᵐᵒᵖ)).injective
              funext i
              rfl
            · apply (WithCStarModule.equiv Bᵐᵒᵖ (κ → Bᵐᵒᵖ)).injective
              funext i
              rfl
          map_add' := fun x y => by
            apply (WithCStarModule.equiv Bᵐᵒᵖ
              (FiniteStandardModule B ι × FiniteStandardModule B κ)).injective
            apply Prod.ext
            · apply (WithCStarModule.equiv Bᵐᵒᵖ (ι → Bᵐᵒᵖ)).injective
              funext i
              rfl
            · apply (WithCStarModule.equiv Bᵐᵒᵖ (κ → Bᵐᵒᵖ)).injective
              funext i
              rfl
          map_smul' := fun c x => by
            apply (WithCStarModule.equiv Bᵐᵒᵖ
              (FiniteStandardModule B ι × FiniteStandardModule B κ)).injective
            apply Prod.ext
            · apply (WithCStarModule.equiv Bᵐᵒᵖ (ι → Bᵐᵒᵖ)).injective
              funext i
              rfl
            · apply (WithCStarModule.equiv Bᵐᵒᵖ (κ → Bᵐᵒᵖ)).injective
              funext i
              rfl }
      norm_map' x := by
        change ‖finiteStandardSplit (B := B) x‖ = ‖x‖
        calc
          ‖finiteStandardSplit (B := B) x‖ =
              Real.sqrt ‖⟪finiteStandardSplit x, finiteStandardSplit x⟫_(Bᵐᵒᵖ)‖ :=
            CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ)
              (E := HilbertModuleSum B (FiniteStandardModule B ι) (FiniteStandardModule B κ)) _
          _ = Real.sqrt ‖⟪x, x⟫_(Bᵐᵒᵖ)‖ :=
            congrArg (fun b : Bᵐᵒᵖ => Real.sqrt ‖b‖) (finiteStandardSplit_inner x x)
          _ = ‖x‖ :=
            (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ)
              (E := FiniteStandardModule B (ι ⊕ κ)) x).symm }
  inner_map := finiteStandardSplit_inner

@[simp] theorem finiteStandardSumEquiv_apply (x : FiniteStandardModule B (ι ⊕ κ)) :
    finiteStandardSumEquiv x = finiteStandardSplit x := rfl

end NonUnital

section Unital
variable [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Splitting coordinates intertwines the actual coefficient matrix block action. -/
theorem finiteStandardSumEquiv_block_action (M : CStarMatrix ι ι B) (N : CStarMatrix κ κ B)
    (x : FiniteStandardModule B (ι ⊕ κ)) :
    finiteStandardSumEquiv (moduleMatrixRepresentation (BC4lean.OperatorKTheory.matrixBlockSum M N) x) =
      sumMap (moduleMatrixRepresentation M) (moduleMatrixRepresentation N) (finiteStandardSumEquiv x) := by
  apply Prod.ext
  · ext i
    simp only [← rectangularModuleOperator_square]
    simp only [finiteStandardSumEquiv_apply, finiteStandardSplit_fst, sumMap_apply,
      sumMk_fst, rectangularModuleOperator_apply, Fintype.sum_sum_type,
      BC4lean.OperatorKTheory.matrixBlockSum, CStarMatrix.ofMatrix_symm_apply,
      CStarMatrix.ofMatrix_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
      MulOpposite.op_zero, mul_zero, Finset.sum_const_zero, add_zero]
  · ext j
    simp only [← rectangularModuleOperator_square]
    simp only [finiteStandardSumEquiv_apply, finiteStandardSplit_snd, sumMap_apply,
      sumMk_snd, rectangularModuleOperator_apply, Fintype.sum_sum_type,
      BC4lean.OperatorKTheory.matrixBlockSum, CStarMatrix.ofMatrix_symm_apply,
      CStarMatrix.ofMatrix_apply,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
      MulOpposite.op_zero, mul_zero, Finset.sum_const_zero, zero_add]

/-- The supported range of a block projection is the genuine direct sum of the ranges. -/
def finiteProjectionBlockSumEquiv (p : BC4lean.OperatorKTheory.MatrixProjection B ι)
    (q : BC4lean.OperatorKTheory.MatrixProjection B κ) :
    HilbertModuleEquiv B (FiniteProjectionModule (BC4lean.OperatorKTheory.projectionBlockSum p q))
      (HilbertModuleSum B (FiniteProjectionModule p) (FiniteProjectionModule q)) :=
  (finiteStandardSumEquiv.restrictProjection _ _
      (finiteStandardSumEquiv_block_action p.val q.val)).trans
    (projectionSumRangeEquiv (matrixProjectionOperator p) (matrixProjectionOperator q))

variable {Γ : Type*} [Group Γ]

/-- Projection block sum realizes cycle direct sum on the actual supported modules. -/
def finiteProjectionRangeCycleBlockSumIso (p q : BC4lean.OperatorKTheory.FiniteProjection B) :
    KasparovCycleIso
      (finiteProjectionRangeCycle (Γ := Γ) (BC4lean.OperatorKTheory.FiniteProjection.blockSum p q))
      ((finiteProjectionRangeCycle (Γ := Γ) p).directSum (finiteProjectionRangeCycle (Γ := Γ) q)) where
  moduleEquiv := finiteProjectionBlockSumEquiv p.projection q.projection
  grading_intertwine x := by
    change finiteProjectionBlockSumEquiv p.projection q.projection x =
      sumMk (finiteProjectionBlockSumEquiv p.projection q.projection x).fst
        (finiteProjectionBlockSumEquiv p.projection q.projection x).snd
    rfl
  action_intertwine g x := by
    change finiteProjectionBlockSumEquiv p.projection q.projection x =
      sumMk (finiteProjectionBlockSumEquiv p.projection q.projection x).fst
        (finiteProjectionBlockSumEquiv p.projection q.projection x).snd
    rfl
  representation_intertwine a x := by
    rw [KasparovCycle.directSum_representation, finiteProjectionRangeCycle_representation,
      finiteProjectionRangeCycle_representation, finiteProjectionRangeCycle_representation]
    simp only [scalarModuleRepresentation_apply, sumMap_apply]
    exact (finiteProjectionBlockSumEquiv p.projection q.projection).map_smul a x
  operator_intertwine x := by
    rw [KasparovCycle.directSum_operator, finiteProjectionRangeCycle_operator,
      finiteProjectionRangeCycle_operator, finiteProjectionRangeCycle_operator, sumMap_zero]
    change finiteProjectionBlockSumEquiv p.projection q.projection 0 = 0
    exact (finiteProjectionBlockSumEquiv p.projection q.projection).map_zero

end Unital
end BC4lean.KKTheory
