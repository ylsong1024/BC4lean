import BC4lean.GradedMatrixMoritaColumn
import BC4lean.GradedMatrixMoritaSeparable
import BC4lean.StandardModuleOperator

/-! # The genuine graded B/matrix-B row module

The row module is the closed first-row right ideal of the actual matrix C⋆
algebra, equipped with its inherited regular right-module norm and inner
product. This uses the C⋆ matrix operator norm. Right matrix coefficients
act by actual multiplication, and B acts on the left through its top-left
corner. Both this Hilbert module and its grading are constructed explicitly.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

namespace GradedMatrixMoritaRow

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def submodule : Submodule ℂ (GradedMatrixMoritaMatrix B)ᵐᵒᵖ where
  carrier := {x | ∀ j : Fin 2, MulOpposite.unop x 1 j = 0}
  zero_mem' j := rfl
  add_mem' hx hy j := by simp [MulOpposite.unop_add, CStarMatrix.add_apply, hx j, hy j]
  smul_mem' c x hx j := by simp [MulOpposite.unop_smul, CStarMatrix.smul_apply, hx j]

end GradedMatrixMoritaRow

abbrev GradedMatrixMoritaRow (B : Type*) [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] := GradedMatrixMoritaRow.submodule (B := B)

namespace GradedMatrixMoritaRow

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def matrix (x : GradedMatrixMoritaRow B) : GradedMatrixMoritaMatrix B :=
  MulOpposite.unop (x : (GradedMatrixMoritaMatrix B)ᵐᵒᵖ)

@[simp] theorem matrix_zero : matrix (0 : GradedMatrixMoritaRow B) = 0 := rfl
@[simp] theorem matrix_add (x y : GradedMatrixMoritaRow B) : matrix (x + y) = matrix x + matrix y := rfl
@[simp] theorem matrix_smul (c : ℂ) (x : GradedMatrixMoritaRow B) : matrix (c • x) = c • matrix x := rfl

@[simp] theorem matrix_second_row (x : GradedMatrixMoritaRow B) (j : Fin 2) :
    matrix x 1 j = 0 := x.property j

@[simp] theorem norm_matrix (x : GradedMatrixMoritaRow B) : ‖matrix x‖ = ‖x‖ := rfl

def entryCLM (i j : Fin 2) : GradedMatrixMoritaMatrix B →L[ℂ] B :=
  LinearMap.mkContinuous
    { toFun := fun M => M i j
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    1 (fun M => by
      change ‖M i j‖ ≤ 1 * ‖M‖
      rw [one_mul]
      exact CStarMatrix.norm_entry_le_norm (M := M) (i := i) (j := j))

theorem submodule_isClosed :
    IsClosed (submodule (B := B) : Set (GradedMatrixMoritaMatrix B)ᵐᵒᵖ) := by
  change IsClosed {x : (GradedMatrixMoritaMatrix B)ᵐᵒᵖ |
    ∀ j : Fin 2, MulOpposite.unop x 1 j = 0}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun j =>
    isClosed_eq ((entryCLM (B := B) 1 j).continuous.comp MulOpposite.continuous_unop)
      continuous_const

instance completeSpace : CompleteSpace (GradedMatrixMoritaRow B) :=
  submodule_isClosed.completeSpace_coe

instance coefficientSMul : SMul (GradedMatrixMoritaMatrix B)ᵐᵒᵖ (GradedMatrixMoritaRow B) where
  smul a x := ⟨a • (x : (GradedMatrixMoritaMatrix B)ᵐᵒᵖ), by
    intro j
    change (matrix x * MulOpposite.unop a) 1 j = 0
    simp only [CStarMatrix.mul_apply, matrix_second_row, zero_mul, Finset.sum_const_zero]⟩

@[simp] theorem matrix_op_smul (a : (GradedMatrixMoritaMatrix B)ᵐᵒᵖ)
    (x : GradedMatrixMoritaRow B) : matrix (a • x) = matrix x * MulOpposite.unop a := rfl

instance cstarModule : CStarModule (GradedMatrixMoritaMatrix B)ᵐᵒᵖ
    (GradedMatrixMoritaRow B) where
  inner x y := ⟪(x : (GradedMatrixMoritaMatrix B)ᵐᵒᵖ),
    (y : (GradedMatrixMoritaMatrix B)ᵐᵒᵖ)⟫_((GradedMatrixMoritaMatrix B)ᵐᵒᵖ)
  inner_add_right := CStarModule.inner_add_right
  inner_self_nonneg := CStarModule.inner_self_nonneg
  inner_self := by
    intro x
    constructor
    · intro h
      apply Subtype.ext
      exact CStarModule.inner_self.mp h
    · intro h
      rw [h]
      exact CStarModule.inner_zero_left
  inner_op_smul_right := CStarModule.inner_op_smul_right
  inner_smul_right_complex := CStarModule.inner_smul_right_complex
  star_inner x y := CStarModule.star_inner
    (x : (GradedMatrixMoritaMatrix B)ᵐᵒᵖ) (y : (GradedMatrixMoritaMatrix B)ᵐᵒᵖ)
  norm_eq_sqrt_norm_inner_self x := CStarModule.norm_eq_sqrt_norm_inner_self
    (A := (GradedMatrixMoritaMatrix B)ᵐᵒᵖ) (x : (GradedMatrixMoritaMatrix B)ᵐᵒᵖ)

/-- The row's genuine matrix-valued inner product is x* y. -/
@[simp] theorem inner_matrix (x y : GradedMatrixMoritaRow B) :
    MulOpposite.unop ⟪x, y⟫_((GradedMatrixMoritaMatrix B)ᵐᵒᵖ) = star (matrix x) * matrix y := rfl

def leftCLM (b : B) : GradedMatrixMoritaRow B →L[ℂ] GradedMatrixMoritaRow B :=
  (((standardLeftMul (GradedMatrixMoritaMatrix.corner b)).toCLM).comp
      (submodule (B := B)).subtypeL).codRestrict (submodule (B := B)) (fun x => by
    intro j
    change (GradedMatrixMoritaMatrix.corner b * matrix x) 1 j = 0
    simp [GradedMatrixMoritaMatrix.corner, CStarMatrix.mul_apply, Fin.sum_univ_two])

@[simp] theorem matrix_leftCLM (b : B) (x : GradedMatrixMoritaRow B) :
    matrix (leftCLM b x) = GradedMatrixMoritaMatrix.corner b * matrix x := rfl

def leftMap (b : B) : AdjointableMap (GradedMatrixMoritaMatrix B)
    (GradedMatrixMoritaRow B) (GradedMatrixMoritaRow B) where
  toCLM := leftCLM b
  adjointCLM := leftCLM (star b)
  adjoint_identity x y := by
    apply MulOpposite.unop_injective
    simp only [inner_matrix, matrix_leftCLM, star_mul, mul_assoc]
    have h : star (GradedMatrixMoritaMatrix.corner b) =
        GradedMatrixMoritaMatrix.corner (star b) := by
      change star ((GradedMatrixMoritaMatrix.cornerHom (B := B)) b) =
        (GradedMatrixMoritaMatrix.cornerHom (B := B)) (star b)
      exact (map_star (GradedMatrixMoritaMatrix.cornerHom (B := B)) b).symm
    rw [h]

def leftAction : B →⋆ₙₐ[ℂ] AdjointableMap (GradedMatrixMoritaMatrix B)
    (GradedMatrixMoritaRow B) (GradedMatrixMoritaRow B) where
  toFun := leftMap
  map_zero' := by
    ext x
    change MulOpposite.op (GradedMatrixMoritaMatrix.corner 0 * matrix x) = 0
    rw [show GradedMatrixMoritaMatrix.corner (0 : B) = 0 from
      map_zero (GradedMatrixMoritaMatrix.cornerHom (B := B))]
    simp
  map_add' b c := by
    ext x
    apply MulOpposite.unop_injective
    change GradedMatrixMoritaMatrix.corner (b + c) * matrix x =
      GradedMatrixMoritaMatrix.corner b * matrix x + GradedMatrixMoritaMatrix.corner c * matrix x
    rw [show GradedMatrixMoritaMatrix.corner (b + c) =
      GradedMatrixMoritaMatrix.corner b + GradedMatrixMoritaMatrix.corner c from
      map_add (GradedMatrixMoritaMatrix.cornerHom (B := B)) b c, add_mul]
  map_smul' c b := by
    ext x
    apply MulOpposite.unop_injective
    change GradedMatrixMoritaMatrix.corner (c • b) * matrix x =
      c • (GradedMatrixMoritaMatrix.corner b * matrix x)
    rw [show GradedMatrixMoritaMatrix.corner (c • b) = c • GradedMatrixMoritaMatrix.corner b from
      map_smul (GradedMatrixMoritaMatrix.cornerHom (B := B)) c b, smul_mul_assoc]
  map_mul' b c := by
    ext x
    apply MulOpposite.unop_injective
    change GradedMatrixMoritaMatrix.corner (b * c) * matrix x =
      GradedMatrixMoritaMatrix.corner b * (GradedMatrixMoritaMatrix.corner c * matrix x)
    rw [show GradedMatrixMoritaMatrix.corner (b * c) =
      GradedMatrixMoritaMatrix.corner b * GradedMatrixMoritaMatrix.corner c from
      map_mul (GradedMatrixMoritaMatrix.cornerHom (B := B)) b c, mul_assoc]
  map_star' b := by ext x; rfl

def parity (x : GradedMatrixMoritaRow B) : GradedMatrixMoritaRow B :=
  ⟨MulOpposite.op (GradedMatrixMoritaMatrix.parity (matrix x)), by
    intro j
    change GradedMatrixMoritaMatrix.parity (matrix x) 1 j = 0
    fin_cases j <;> simp [GradedMatrixMoritaMatrix.parity, matrix_second_row]⟩

@[simp] theorem matrix_parity (x : GradedMatrixMoritaRow B) :
    matrix (parity x) = GradedMatrixMoritaMatrix.parity (matrix x) := rfl

def parityLinear : GradedMatrixMoritaRow B →ₗ[ℂ] GradedMatrixMoritaRow B where
  toFun := parity
  map_add' x y := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    change GradedMatrixMoritaMatrix.parity (matrix x + matrix y) =
      GradedMatrixMoritaMatrix.parity (matrix x) + GradedMatrixMoritaMatrix.parity (matrix y)
    exact GradedMatrixMoritaMatrix.parity_add _ _
  map_smul' c x := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    change GradedMatrixMoritaMatrix.parity (c • matrix x) =
      c • GradedMatrixMoritaMatrix.parity (matrix x)
    exact GradedMatrixMoritaMatrix.parity_smul _ _

@[simp] theorem parity_parity (x : GradedMatrixMoritaRow B) : parity (parity x) = x := by
  apply Subtype.ext
  apply MulOpposite.unop_injective
  exact GradedMatrixMoritaMatrix.parity_parity (matrix x)

def parityIsometry : GradedMatrixMoritaRow B ≃ₗᵢ[ℂ] GradedMatrixMoritaRow B where
  toLinearEquiv :=
    { toLinearMap := parityLinear
      invFun := parity
      left_inv x := by
        change parity (parity x) = x
        exact parity_parity x
      right_inv x := by
        change parity (parity x) = x
        exact parity_parity x }
  norm_map' x := by
    change ‖GradedMatrixMoritaMatrix.parity (matrix x)‖ = ‖matrix x‖
    exact StarAlgEquiv.norm_map (GradedMatrixMoritaMatrix.parityEquiv (B := B)) (matrix x)

def grading : GradedHilbertModule (GradedMatrixMoritaMatrix.grading (B := B))
    (GradedMatrixMoritaRow B) where
  grading := parityIsometry
  involutive := parity_parity
  inner_grading x y := by
    apply MulOpposite.unop_injective
    change star (GradedMatrixMoritaMatrix.parity (matrix x)) *
      GradedMatrixMoritaMatrix.parity (matrix y) =
      GradedMatrixMoritaMatrix.parity (star (matrix x) * matrix y)
    rw [GradedMatrixMoritaMatrix.parity_mul, GradedMatrixMoritaMatrix.parity_star]

/-- B has the trivial grading; its actual corner action is even on the row. -/
theorem leftAction_graded (b : B) (x : GradedMatrixMoritaRow B) :
    parity (leftAction b x) = leftAction b (parity x) := by
  apply Subtype.ext
  apply MulOpposite.unop_injective
  change GradedMatrixMoritaMatrix.parity (GradedMatrixMoritaMatrix.corner b * matrix x) =
    GradedMatrixMoritaMatrix.corner b * GradedMatrixMoritaMatrix.parity (matrix x)
  rw [GradedMatrixMoritaMatrix.parity_mul, GradedMatrixMoritaMatrix.parity_corner]

theorem countablyGenerated [TopologicalSpace.SeparableSpace B] :
    IsCountablyGeneratedModule (GradedMatrixMoritaMatrix B) (GradedMatrixMoritaRow B) := by
  let : TopologicalSpace.SeparableSpace (GradedMatrixMoritaMatrix B)ᵐᵒᵖ :=
    MulOpposite.op_surjective.denseRange.separableSpace MulOpposite.continuous_op
  let : TopologicalSpace.SeparableSpace (GradedMatrixMoritaRow B) := inferInstance
  exact isCountablyGeneratedModule_of_separableSpace

end GradedMatrixMoritaRow
end BC4lean.KKTheory
