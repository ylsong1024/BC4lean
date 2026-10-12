import BC4lean.GradedMatrixMoritaCompact
import BC4lean.ModuleTensorInner
import BC4lean.GradedEquivariantInteriorModuleTensor

/-! # Actual balanced contractions of the graded matrix Morita modules

The column-row contraction is the actual outer-product matrix. The row-column
contraction is the actual coefficient dot product. Both descend through their
genuine coefficient-balancing quotients, and their complete coefficient-valued
inner-product identities are proved from the finite coordinate formulas.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace WithCStarModule

namespace GradedMatrixMoritaContractions

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def columnRow (x : GradedMatrixMoritaColumn B) (y : GradedMatrixMoritaRow B) :
    (GradedMatrixMoritaMatrix B)ᵐᵒᵖ :=
  MulOpposite.op (CStarMatrix.ofMatrix fun i j =>
    MulOpposite.unop (x i) * GradedMatrixMoritaRow.matrix y 0 j)

def rowColumn (x : GradedMatrixMoritaRow B) (y : GradedMatrixMoritaColumn B) : Bᵐᵒᵖ :=
  MulOpposite.op (∑ j : Fin 2, GradedMatrixMoritaRow.matrix x 0 j * MulOpposite.unop (y j))

def columnRowBilinear : GradedMatrixMoritaColumn B →ₗ[ℂ]
    GradedMatrixMoritaRow B →ₗ[ℂ] (GradedMatrixMoritaMatrix B)ᵐᵒᵖ where
  toFun x :=
    { toFun := columnRow x
      map_add' y z := by
        apply MulOpposite.unop_injective
        ext i j
        change MulOpposite.unop (x i) * GradedMatrixMoritaRow.matrix (y + z) 0 j =
          MulOpposite.unop (x i) * GradedMatrixMoritaRow.matrix y 0 j +
            MulOpposite.unop (x i) * GradedMatrixMoritaRow.matrix z 0 j
        simp only [GradedMatrixMoritaRow.matrix_add, CStarMatrix.add_apply, mul_add]
      map_smul' c y := by
        apply MulOpposite.unop_injective
        ext i j
        change MulOpposite.unop (x i) * GradedMatrixMoritaRow.matrix (c • y) 0 j =
          c • (MulOpposite.unop (x i) * GradedMatrixMoritaRow.matrix y 0 j)
        simp only [GradedMatrixMoritaRow.matrix_smul, CStarMatrix.smul_apply,
          mul_smul_comm] }
  map_add' x z := by
    ext y
    apply MulOpposite.unop_injective
    ext i j
    change MulOpposite.unop ((x + z) i) * GradedMatrixMoritaRow.matrix y 0 j =
      MulOpposite.unop (x i) * GradedMatrixMoritaRow.matrix y 0 j +
        MulOpposite.unop (z i) * GradedMatrixMoritaRow.matrix y 0 j
    simp only [WithCStarModule.add_apply, MulOpposite.unop_add, add_mul]
  map_smul' c x := by
    ext y
    apply MulOpposite.unop_injective
    ext i j
    change MulOpposite.unop ((c • x) i) * GradedMatrixMoritaRow.matrix y 0 j =
      c • (MulOpposite.unop (x i) * GradedMatrixMoritaRow.matrix y 0 j)
    simp only [WithCStarModule.smul_apply, MulOpposite.unop_smul, smul_mul_assoc]

def rowColumnBilinear : GradedMatrixMoritaRow B →ₗ[ℂ]
    GradedMatrixMoritaColumn B →ₗ[ℂ] Bᵐᵒᵖ where
  toFun x :=
    { toFun := rowColumn x
      map_add' y z := by
        simp [rowColumn, WithCStarModule.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' c y := by
        simp [rowColumn, WithCStarModule.smul_apply, mul_smul_comm] }
  map_add' x z := by
    ext y
    simp [rowColumn, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    ext y
    simp [rowColumn, smul_mul_assoc]

theorem columnRow_balance (b : B) (x : GradedMatrixMoritaColumn B)
    (y : GradedMatrixMoritaRow B) :
    columnRow (MulOpposite.op b • x) y = columnRow x (GradedMatrixMoritaRow.leftAction b y) := by
  apply MulOpposite.unop_injective
  ext i j
  change (MulOpposite.unop (x i) * b) * GradedMatrixMoritaRow.matrix y 0 j =
    MulOpposite.unop (x i) *
      (GradedMatrixMoritaMatrix.corner b * GradedMatrixMoritaRow.matrix y) 0 j
  simp [GradedMatrixMoritaMatrix.corner, CStarMatrix.mul_apply, Fin.sum_univ_two, mul_assoc]

theorem rowColumn_balance (M : GradedMatrixMoritaMatrix B) (x : GradedMatrixMoritaRow B)
    (y : GradedMatrixMoritaColumn B) :
    rowColumn (MulOpposite.op M • x) y = rowColumn x (GradedMatrixMoritaColumn.leftAction M y) := by
  apply MulOpposite.unop_injective
  simp [rowColumn, GradedMatrixMoritaRow.matrix_op_smul,
    GradedMatrixMoritaColumn.leftAction_apply, CStarMatrix.mul_apply,
    Fin.sum_univ_two, add_mul, mul_add, mul_assoc]
  abel

def columnRowBalanced : BalancedModuleTensor (E := GradedMatrixMoritaColumn B)
    (GradedMatrixMoritaRow.leftAction (B := B)) →ₗ[ℂ] (GradedMatrixMoritaMatrix B)ᵐᵒᵖ :=
  moduleTensorLift _ columnRowBilinear columnRow_balance

def rowColumnBalanced : BalancedModuleTensor (E := GradedMatrixMoritaRow B)
    (GradedMatrixMoritaColumn.leftAction (B := B)) →ₗ[ℂ] Bᵐᵒᵖ :=
  moduleTensorLift _ rowColumnBilinear rowColumn_balance

@[simp] theorem columnRowBalanced_mk (x : GradedMatrixMoritaColumn B) (y : GradedMatrixMoritaRow B) :
    columnRowBalanced (moduleTensorMk (E := GradedMatrixMoritaColumn B)
      (GradedMatrixMoritaRow.leftAction (B := B)) x y) = columnRow x y := by
  exact moduleTensorLift_apply (E := GradedMatrixMoritaColumn B)
    (GradedMatrixMoritaRow.leftAction (B := B)) (columnRowBilinear (B := B)) (columnRow_balance (B := B)) x y
@[simp] theorem rowColumnBalanced_mk (x : GradedMatrixMoritaRow B) (y : GradedMatrixMoritaColumn B) :
    rowColumnBalanced (moduleTensorMk (E := GradedMatrixMoritaRow B)
      (GradedMatrixMoritaColumn.leftAction (B := B)) x y) = rowColumn x y := by
  exact moduleTensorLift_apply (E := GradedMatrixMoritaRow B)
    (GradedMatrixMoritaColumn.leftAction (B := B)) (rowColumnBilinear (B := B)) (rowColumn_balance (B := B)) x y

theorem columnRow_inner (x x' : GradedMatrixMoritaColumn B) (y y' : GradedMatrixMoritaRow B) :
    ⟪columnRow x y, columnRow x' y'⟫_((GradedMatrixMoritaMatrix B)ᵐᵒᵖ) =
      moduleTensorPureInner GradedMatrixMoritaRow.leftAction x y x' y' := by
  have hentry (N : Matrix (Fin 2) (Fin 2) B) (r s : Fin 2) :
      (CStarMatrix.ofMatrix N) r s = N r s := rfl
  apply MulOpposite.unop_injective
  change star (MulOpposite.unop (columnRow x y)) * MulOpposite.unop (columnRow x' y') =
    star (GradedMatrixMoritaRow.matrix y) *
      (GradedMatrixMoritaMatrix.corner (MulOpposite.unop ⟪x, x'⟫_(Bᵐᵒᵖ)) *
        GradedMatrixMoritaRow.matrix y')
  ext i j
  simp [columnRow, hentry, GradedMatrixMoritaMatrix.corner,
    WithCStarModule.pi_inner, WithCStarModule.inner_def,
    CStarMatrix.star_apply, CStarMatrix.mul_apply, Fin.sum_univ_two,
    GradedMatrixMoritaRow.matrix_second_row, mul_add, add_mul, mul_assoc]
  change
    star (MulOpposite.unop (x 0) * GradedMatrixMoritaRow.matrix y 0 i) *
        (MulOpposite.unop (x' 0) * GradedMatrixMoritaRow.matrix y' 0 j) +
      star (MulOpposite.unop (x 1) * GradedMatrixMoritaRow.matrix y 0 i) *
        (MulOpposite.unop (x' 1) * GradedMatrixMoritaRow.matrix y' 0 j) =
    star (GradedMatrixMoritaRow.matrix y 0 i) *
        (star (MulOpposite.unop (x 0)) *
          (MulOpposite.unop (x' 0) * GradedMatrixMoritaRow.matrix y' 0 j)) +
      star (GradedMatrixMoritaRow.matrix y 0 i) *
        (star (MulOpposite.unop (x 1)) *
          (MulOpposite.unop (x' 1) * GradedMatrixMoritaRow.matrix y' 0 j))
  simp only [star_mul, mul_assoc]

theorem rowColumn_inner (x x' : GradedMatrixMoritaRow B) (y y' : GradedMatrixMoritaColumn B) :
    ⟪rowColumn x y, rowColumn x' y'⟫_(Bᵐᵒᵖ) =
      moduleTensorPureInner GradedMatrixMoritaColumn.leftAction x y x' y' := by
  apply MulOpposite.unop_injective
  change star (MulOpposite.unop (rowColumn x y)) * MulOpposite.unop (rowColumn x' y') =
    MulOpposite.unop ⟪y, GradedMatrixMoritaColumn.leftAction
      (star (GradedMatrixMoritaRow.matrix x) * GradedMatrixMoritaRow.matrix x') y'⟫_(Bᵐᵒᵖ)
  simp [rowColumn,
    GradedMatrixMoritaColumn.leftAction_apply,
    WithCStarModule.pi_inner, WithCStarModule.inner_def,
    CStarMatrix.star_apply, Fin.sum_univ_two,
    star_mul, star_add, GradedMatrixMoritaRow.matrix_second_row]; noncomm_ring

/-- The entire outer-product balanced form is pulled back from actual matrices. -/
theorem columnRowBalanced_inner
    (u v : BalancedModuleTensor (E := GradedMatrixMoritaColumn B)
      (GradedMatrixMoritaRow.leftAction (B := B))) :
    ⟪columnRowBalanced u, columnRowBalanced v⟫_((GradedMatrixMoritaMatrix B)ᵐᵒᵖ) =
      moduleTensorInner (E := GradedMatrixMoritaColumn B) (GradedMatrixMoritaRow.leftAction (B := B)) u v := by
  revert v
  refine moduleTensor_induction (E := GradedMatrixMoritaColumn B)
    (GradedMatrixMoritaRow.leftAction (B := B)) u ?_ ?_ ?_
  · intro v
    simp only [map_zero, LinearMap.zero_apply, CStarModule.inner_zero_left]
  · intro x y v
    refine moduleTensor_induction (E := GradedMatrixMoritaColumn B)
      (GradedMatrixMoritaRow.leftAction (B := B)) v ?_ ?_ ?_
    · simp only [map_zero, CStarModule.inner_zero_right]
    · intro x' y'
      simpa only [columnRowBalanced_mk, moduleTensorInner_mk_mk] using
        columnRow_inner x x' y y'
    · intro v w hv hw
      simp only [map_add, CStarModule.inner_add_right, hv, hw]
  · intro u w hu hw v
    simp only [map_add, LinearMap.add_apply, CStarModule.inner_add_left, hu, hw]

/-- The entire dot-product balanced form is pulled back from actual B coefficients. -/
theorem rowColumnBalanced_inner
    (u v : BalancedModuleTensor (E := GradedMatrixMoritaRow B)
      (GradedMatrixMoritaColumn.leftAction (B := B))) :
    ⟪rowColumnBalanced u, rowColumnBalanced v⟫_(Bᵐᵒᵖ) =
      moduleTensorInner (E := GradedMatrixMoritaRow B) (GradedMatrixMoritaColumn.leftAction (B := B)) u v := by
  revert v
  refine moduleTensor_induction (E := GradedMatrixMoritaRow B)
    (GradedMatrixMoritaColumn.leftAction (B := B)) u ?_ ?_ ?_
  · intro v
    simp only [map_zero, LinearMap.zero_apply, CStarModule.inner_zero_left]
  · intro x y v
    refine moduleTensor_induction (E := GradedMatrixMoritaRow B)
      (GradedMatrixMoritaColumn.leftAction (B := B)) v ?_ ?_ ?_
    · simp only [map_zero, CStarModule.inner_zero_right]
    · intro x' y'
      simpa only [rowColumnBalanced_mk, moduleTensorInner_mk_mk] using
        rowColumn_inner x x' y y'
    · intro v w hv hw
      simp only [map_add, CStarModule.inner_add_right, hv, hw]
  · intro u w hu hw v
    simp only [map_add, LinearMap.add_apply, CStarModule.inner_add_left, hu, hw]

/-- The outer product intertwines both genuine factor gradings with matrix parity. -/
theorem columnRow_graded (x : GradedMatrixMoritaColumn B) (y : GradedMatrixMoritaRow B) :
    columnRow (GradedMatrixMoritaColumn.parity x) (GradedMatrixMoritaRow.parity y) =
      opStarAlgEquiv GradedMatrixMoritaMatrix.parityEquiv (columnRow x y) := by
  apply MulOpposite.unop_injective
  ext i j
  fin_cases i <;> fin_cases j
  · change MulOpposite.unop (x 0) * GradedMatrixMoritaRow.matrix y 0 0 =
      MulOpposite.unop (x 0) * GradedMatrixMoritaRow.matrix y 0 0
    rfl
  · change MulOpposite.unop (x 0) * (-GradedMatrixMoritaRow.matrix y 0 1) =
      -(MulOpposite.unop (x 0) * GradedMatrixMoritaRow.matrix y 0 1)
    exact mul_neg _ _
  · change (-MulOpposite.unop (x 1)) * GradedMatrixMoritaRow.matrix y 0 0 =
      -(MulOpposite.unop (x 1) * GradedMatrixMoritaRow.matrix y 0 0)
    exact neg_mul _ _
  · change (-MulOpposite.unop (x 1)) * (-GradedMatrixMoritaRow.matrix y 0 1) =
      MulOpposite.unop (x 1) * GradedMatrixMoritaRow.matrix y 0 1
    exact neg_mul_neg _ _

/-- The two factor signs cancel in the actual B-valued dot contraction. -/
theorem rowColumn_graded (x : GradedMatrixMoritaRow B) (y : GradedMatrixMoritaColumn B) :
    rowColumn (GradedMatrixMoritaRow.parity x) (GradedMatrixMoritaColumn.parity y) = rowColumn x y := by
  simp [rowColumn, GradedMatrixMoritaRow.matrix_parity, GradedMatrixMoritaMatrix.parity,
    Fin.sum_univ_two]

end GradedMatrixMoritaContractions
end BC4lean.KKTheory
