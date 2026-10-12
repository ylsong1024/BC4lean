import BC4lean.GradedMatrixMoritaUnitary

/-! # Genuine equivariance of the graded matrix Morita modules

The coefficient group acts entrywise on matrices, columns and rows. Actual
coefficient inner products prove the module isometries. Both representation
intertwinings and both completed contraction intertwinings are proved from
the coordinate formulas. Joint continuity for discrete groups follows from
the existing genuine isometric-action theorem.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace WithCStarModule

namespace GradedMatrixMoritaEquivariant

variable {Γ B : Type*} [Group Γ] [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def matrixEquiv (e : B ≃⋆ₐ[ℂ] B) : GradedMatrixMoritaMatrix B ≃⋆ₐ[ℂ] GradedMatrixMoritaMatrix B where
  toFun M := CStarMatrix.ofMatrix fun i j => e (M i j)
  invFun M := CStarMatrix.ofMatrix fun i j => e.symm (M i j)
  left_inv M := by ext i j; exact e.symm_apply_apply _
  right_inv M := by ext i j; exact e.apply_symm_apply _
  map_add' M N := by ext i j; exact map_add e _ _
  map_smul' c M := by ext i j; exact map_smul e c _
  map_mul' M N := by
    ext i j
    change e (∑ k : Fin 2, M i k * N k j) =
      ∑ k : Fin 2, e (M i k) * e (N k j)
    simp only [Fin.sum_univ_two, map_add, map_mul]
  map_star' M := by
    ext i j
    change e (star (M j i)) = star (e (M j i))
    exact map_star e _

def matrixAction (β : CStarAlgebraAction Γ B) : CStarAlgebraAction Γ (GradedMatrixMoritaMatrix B) where
  automorphism :=
    { toFun g := matrixEquiv (β.automorphism g)
      map_one' := by ext M i j; exact β.one_apply _
      map_mul' g h := by ext M i j; exact β.mul_apply g h _ }

@[simp] theorem matrixAction_apply (β : CStarAlgebraAction Γ B) (g : Γ)
    (M : GradedMatrixMoritaMatrix B) (i j : Fin 2) :
    (matrixAction β).automorphism g M i j = β.automorphism g (M i j) := rfl

theorem matrixAction_preservesGrading (β : CStarAlgebraAction Γ B) :
    (matrixAction β).PreservesGrading GradedMatrixMoritaMatrix.grading := by
  intro g M
  ext i j
  fin_cases i <;> fin_cases j <;> simp [GradedMatrixMoritaMatrix.grading,
    GradedMatrixMoritaMatrix.parityEquiv, GradedMatrixMoritaMatrix.parity]

def columnMap (e : B ≃⋆ₐ[ℂ] B) (x : GradedMatrixMoritaColumn B) : GradedMatrixMoritaColumn B :=
  (WithCStarModule.equiv _ _).symm fun i => opStarAlgEquiv e (x i)

@[simp] theorem columnMap_apply (e : B ≃⋆ₐ[ℂ] B) (x : GradedMatrixMoritaColumn B) (i : Fin 2) :
    columnMap e x i = opStarAlgEquiv e (x i) := by
  let _retainedOrderB : PartialOrder B := inferInstance
  let _retainedStarOrderB : StarOrderedRing B := inferInstance
  rfl

theorem columnMap_inner (e : B ≃⋆ₐ[ℂ] B) (x y : GradedMatrixMoritaColumn B) :
    ⟪columnMap e x, columnMap e y⟫_(Bᵐᵒᵖ) = opStarAlgEquiv e ⟪x, y⟫_(Bᵐᵒᵖ) := by
  apply MulOpposite.unop_injective
  simp [WithCStarModule.pi_inner, WithCStarModule.inner_def, opStarAlgEquiv_apply,
    map_mul, map_star]

def columnIsometry (e : B ≃⋆ₐ[ℂ] B) : GradedMatrixMoritaColumn B ≃ₗᵢ[ℂ] GradedMatrixMoritaColumn B where
  toLinearEquiv :=
    { toFun := columnMap e
      invFun := columnMap e.symm
      left_inv x := by
        ext i
        change (opStarAlgEquiv e).symm ((opStarAlgEquiv e) (x i)) = x i
        exact (opStarAlgEquiv e).symm_apply_apply _
      right_inv x := by
        ext i
        change (opStarAlgEquiv e) ((opStarAlgEquiv e).symm (x i)) = x i
        exact (opStarAlgEquiv e).apply_symm_apply _
      map_add' x y := by
        ext i
        change opStarAlgEquiv e (x i + y i) = opStarAlgEquiv e (x i) + opStarAlgEquiv e (y i)
        exact map_add (opStarAlgEquiv e) _ _
      map_smul' c x := by
        ext i
        change opStarAlgEquiv e (c • x i) = c • opStarAlgEquiv e (x i)
        exact map_smul (opStarAlgEquiv e) c _ }
  norm_map' x := by
    change ‖columnMap e x‖ = ‖x‖
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ), columnMap_inner,
      StarAlgEquiv.norm_map, ← CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ)]

def columnAction (β : CStarAlgebraAction Γ B) : EquivariantHilbertModule β (GradedMatrixMoritaColumn B) where
  action :=
    { toFun g := columnIsometry (β.automorphism g)
      map_one' := by
        apply DFunLike.ext
        intro x
        ext i
        change opStarAlgEquiv (β.automorphism 1) (x i) = x i
        apply MulOpposite.unop_injective
        exact β.one_apply _
      map_mul' g h := by
        apply DFunLike.ext
        intro x
        ext i
        change opStarAlgEquiv (β.automorphism (g * h)) (x i) =
          opStarAlgEquiv (β.automorphism g) (opStarAlgEquiv (β.automorphism h) (x i))
        apply MulOpposite.unop_injective
        exact β.mul_apply g h _ }
  inner_action g := columnMap_inner _

theorem columnAction_preservesGrading (β : CStarAlgebraAction Γ B) :
    (columnAction β).PreservesGrading GradedMatrixMoritaColumn.grading := by
  intro g x
  ext i
  fin_cases i <;> simp [columnAction, columnIsometry, columnMap,
    GradedMatrixMoritaColumn.grading, GradedMatrixMoritaColumn.parityIsometry,
    GradedMatrixMoritaColumn.parityLinear]

def rowMap (e : B ≃⋆ₐ[ℂ] B) (x : GradedMatrixMoritaRow B) : GradedMatrixMoritaRow B :=
  ⟨MulOpposite.op (matrixEquiv e (GradedMatrixMoritaRow.matrix x)), by
    intro j
    change e (GradedMatrixMoritaRow.matrix x 1 j) = 0
    rw [GradedMatrixMoritaRow.matrix_second_row, map_zero]⟩

@[simp] theorem rowMap_matrix (e : B ≃⋆ₐ[ℂ] B) (x : GradedMatrixMoritaRow B) :
    GradedMatrixMoritaRow.matrix (rowMap e x) = matrixEquiv e (GradedMatrixMoritaRow.matrix x) := rfl

def rowIsometry (e : B ≃⋆ₐ[ℂ] B) : GradedMatrixMoritaRow B ≃ₗᵢ[ℂ] GradedMatrixMoritaRow B where
  toLinearEquiv :=
    { toFun := rowMap e
      invFun := rowMap e.symm
      left_inv x := by
        apply Subtype.ext
        apply MulOpposite.unop_injective
        ext i j
        exact e.symm_apply_apply _
      right_inv x := by
        apply Subtype.ext
        apply MulOpposite.unop_injective
        ext i j
        exact e.apply_symm_apply _
      map_add' x y := by
        apply Subtype.ext
        apply MulOpposite.unop_injective
        exact map_add (matrixEquiv e) _ _
      map_smul' c x := by
        apply Subtype.ext
        apply MulOpposite.unop_injective
        exact map_smul (matrixEquiv e) c _ }
  norm_map' x := StarAlgEquiv.norm_map (matrixEquiv e) _

def rowAction (β : CStarAlgebraAction Γ B) : EquivariantHilbertModule (matrixAction β)
    (GradedMatrixMoritaRow B) where
  action :=
    { toFun g := rowIsometry (β.automorphism g)
      map_one' := by
        apply DFunLike.ext
        intro x
        apply Subtype.ext
        apply MulOpposite.unop_injective
        ext i j
        exact β.one_apply _
      map_mul' g h := by
        apply DFunLike.ext
        intro x
        apply Subtype.ext
        apply MulOpposite.unop_injective
        ext i j
        exact β.mul_apply g h _ }
  inner_action g x y := by
    apply MulOpposite.unop_injective
    change star (matrixEquiv (β.automorphism g) (GradedMatrixMoritaRow.matrix x)) *
      matrixEquiv (β.automorphism g) (GradedMatrixMoritaRow.matrix y) =
      matrixEquiv (β.automorphism g) (star (GradedMatrixMoritaRow.matrix x) * GradedMatrixMoritaRow.matrix y)
    rw [map_mul, map_star]

theorem rowAction_preservesGrading (β : CStarAlgebraAction Γ B) :
    (rowAction β).PreservesGrading GradedMatrixMoritaRow.grading := by
  intro g x
  apply Subtype.ext
  apply MulOpposite.unop_injective
  exact matrixAction_preservesGrading β g (GradedMatrixMoritaRow.matrix x)

theorem columnRepresentation_equivariant (β : CStarAlgebraAction Γ B) (g : Γ)
    (M : GradedMatrixMoritaMatrix B) (x : GradedMatrixMoritaColumn B) :
    (columnAction β).action g (GradedMatrixMoritaColumn.leftAction M x) =
      GradedMatrixMoritaColumn.leftAction ((matrixAction β).automorphism g M)
        ((columnAction β).action g x) := by
  ext i
  change columnMap (β.automorphism g) (GradedMatrixMoritaColumn.leftAction M x) i =
    GradedMatrixMoritaColumn.leftAction (matrixEquiv (β.automorphism g) M)
      (columnMap (β.automorphism g) x) i
  rw [columnMap_apply, GradedMatrixMoritaColumn.leftAction_apply,
    GradedMatrixMoritaColumn.leftAction_apply]
  apply MulOpposite.unop_injective
  change β.automorphism g (∑ j : Fin 2, M i j * MulOpposite.unop (x j)) =
    ∑ j : Fin 2, β.automorphism g (M i j) * β.automorphism g (MulOpposite.unop (x j))
  simp only [Fin.sum_univ_two, map_add, map_mul]

theorem rowRepresentation_equivariant (β : CStarAlgebraAction Γ B) (g : Γ)
    (b : B) (x : GradedMatrixMoritaRow B) :
    (rowAction β).action g (GradedMatrixMoritaRow.leftAction b x) =
      GradedMatrixMoritaRow.leftAction (β.automorphism g b) ((rowAction β).action g x) := by
  apply Subtype.ext
  apply MulOpposite.unop_injective
  change matrixEquiv (β.automorphism g)
    (GradedMatrixMoritaMatrix.corner b * GradedMatrixMoritaRow.matrix x) =
    GradedMatrixMoritaMatrix.corner (β.automorphism g b) *
      matrixEquiv (β.automorphism g) (GradedMatrixMoritaRow.matrix x)
  rw [map_mul]
  congr 1
  ext i j
  change β.automorphism g (GradedMatrixMoritaMatrix.corner b i j) =
    GradedMatrixMoritaMatrix.corner (β.automorphism g b) i j
  fin_cases i <;> fin_cases j
  · change β.automorphism g b = β.automorphism g b
    rfl
  · change β.automorphism g (0 : B) = (0 : B)
    exact map_zero (β.automorphism g)
  · change β.automorphism g (0 : B) = (0 : B)
    exact map_zero (β.automorphism g)
  · change β.automorphism g (0 : B) = (0 : B)
    exact map_zero (β.automorphism g)

open GradedMatrixMoritaContractions GradedMatrixMoritaCompletion

def columnRowTensorAction (β : CStarAlgebraAction Γ B) : EquivariantHilbertModule (matrixAction β)
    (InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
      (E := GradedMatrixMoritaColumn B) (F := GradedMatrixMoritaRow B)
      (GradedMatrixMoritaRow.leftAction (B := B))) :=
  (columnAction β).interiorTensor (rowAction β) (rowRepresentation_equivariant β)

def rowColumnTensorAction (β : CStarAlgebraAction Γ B) : EquivariantHilbertModule β
    (InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
      (E := GradedMatrixMoritaRow B) (F := GradedMatrixMoritaColumn B)
      (GradedMatrixMoritaColumn.leftAction (B := B))) :=
  (rowAction β).interiorTensor (columnAction β) (columnRepresentation_equivariant β)

theorem columnRow_equivariant (β : CStarAlgebraAction Γ B) (g : Γ)
    (x : GradedMatrixMoritaColumn B) (y : GradedMatrixMoritaRow B) :
    columnRow ((columnAction β).action g x) ((rowAction β).action g y) =
      opStarAlgEquiv ((matrixAction β).automorphism g) (columnRow x y) := by
  apply MulOpposite.unop_injective
  ext i j
  change β.automorphism g (MulOpposite.unop (x i)) *
      β.automorphism g (GradedMatrixMoritaRow.matrix y 0 j) =
    β.automorphism g (MulOpposite.unop (x i) * GradedMatrixMoritaRow.matrix y 0 j)
  exact (map_mul (β.automorphism g) _ _).symm

theorem rowColumn_equivariant (β : CStarAlgebraAction Γ B) (g : Γ)
    (x : GradedMatrixMoritaRow B) (y : GradedMatrixMoritaColumn B) :
    rowColumn ((rowAction β).action g x) ((columnAction β).action g y) =
      opStarAlgEquiv (β.automorphism g) (rowColumn x y) := by
  apply MulOpposite.unop_injective
  change (∑ j : Fin 2, β.automorphism g (GradedMatrixMoritaRow.matrix x 0 j) *
      β.automorphism g (MulOpposite.unop (y j))) =
    β.automorphism g (∑ j : Fin 2, GradedMatrixMoritaRow.matrix x 0 j * MulOpposite.unop (y j))
  simp only [Fin.sum_univ_two, map_add, map_mul]

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 400000 in
theorem columnRowUnitary_equivariant (β : CStarAlgebraAction Γ B) (g : Γ)
    (u : InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
      (E := GradedMatrixMoritaColumn B) (F := GradedMatrixMoritaRow B)
      (GradedMatrixMoritaRow.leftAction (B := B))) :
    columnRowUnitary ((columnRowTensorAction β).action g u) =
      opStarAlgEquiv ((matrixAction β).automorphism g) (columnRowUnitary u) := by
  let : CStarModule (GradedMatrixMoritaMatrix B)ᵐᵒᵖ
      (PreHilbertModuleTensor (E := GradedMatrixMoritaColumn B)
        (GradedMatrixMoritaRow.leftAction (B := B))) :=
    preModuleTensorCStarModule (E := GradedMatrixMoritaColumn B)
      (GradedMatrixMoritaRow.leftAction (B := B))
  let : CStarModule (GradedMatrixMoritaMatrix B)ᵐᵒᵖ
      (InteriorModuleTensor (E := GradedMatrixMoritaColumn B)
        (GradedMatrixMoritaRow.leftAction (B := B))) :=
    completionCStarModule (B := GradedMatrixMoritaMatrix B)
      (E := PreHilbertModuleTensor (E := GradedMatrixMoritaColumn B)
        (GradedMatrixMoritaRow.leftAction (B := B)))
  let e := opStarAlgEquiv ((matrixAction β).automorphism g)
  let eL : (GradedMatrixMoritaMatrix B)ᵐᵒᵖ →ₗᵢ[ℂ] (GradedMatrixMoritaMatrix B)ᵐᵒᵖ :=
    { toLinearMap := { toFun := e, map_add' := map_add e, map_smul' := map_smul e }
      norm_map' := StarAlgEquiv.norm_map e }
  have h : (columnRowCompleted (B := B)).toContinuousLinearMap.comp
      ((columnRowTensorAction β).action g).toContinuousLinearEquiv.toContinuousLinearMap =
      eL.toContinuousLinearMap.comp (columnRowCompleted (B := B)).toContinuousLinearMap := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change columnRowCompleted (B := B)
      (((columnAction β).interiorTensor (rowAction β) (rowRepresentation_equivariant β)).action g
        (interiorModuleTensorMk (B := B) (C := GradedMatrixMoritaMatrix B)
          (E := GradedMatrixMoritaColumn B) (F := GradedMatrixMoritaRow B)
          (GradedMatrixMoritaRow.leftAction (B := B)) x y)) =
      opStarAlgEquiv ((matrixAction β).automorphism g)
        (columnRowCompleted (B := B)
          (interiorModuleTensorMk (B := B) (C := GradedMatrixMoritaMatrix B)
            (E := GradedMatrixMoritaColumn B) (F := GradedMatrixMoritaRow B)
            (GradedMatrixMoritaRow.leftAction (B := B)) x y))
    rw [EquivariantHilbertModule.interiorTensor_action_mk
      (φ := GradedMatrixMoritaRow.leftAction (B := B))
      (columnAction β) (rowAction β) (rowRepresentation_equivariant β) g x y,
      columnRowCompleted_mk, columnRowCompleted_mk]
    exact columnRow_equivariant β g x y
  have hpoint := DFunLike.congr_fun h u
  change columnRowCompleted (B := B) ((columnRowTensorAction β).action g u) =
    opStarAlgEquiv ((matrixAction β).automorphism g) (columnRowCompleted (B := B) u) at hpoint
  change columnRowCompleted (B := B) ((columnRowTensorAction β).action g u) =
    opStarAlgEquiv ((matrixAction β).automorphism g) (columnRowCompleted (B := B) u)
  exact hpoint

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 400000 in
theorem rowColumnUnitary_equivariant (β : CStarAlgebraAction Γ B) (g : Γ)
    (u : InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
      (E := GradedMatrixMoritaRow B) (F := GradedMatrixMoritaColumn B)
      (GradedMatrixMoritaColumn.leftAction (B := B))) :
    rowColumnUnitary ((rowColumnTensorAction β).action g u) =
      opStarAlgEquiv (β.automorphism g) (rowColumnUnitary u) := by
  let : CStarModule Bᵐᵒᵖ
      (PreHilbertModuleTensor (E := GradedMatrixMoritaRow B)
        (GradedMatrixMoritaColumn.leftAction (B := B))) :=
    preModuleTensorCStarModule (E := GradedMatrixMoritaRow B)
      (GradedMatrixMoritaColumn.leftAction (B := B))
  let : CStarModule Bᵐᵒᵖ
      (InteriorModuleTensor (E := GradedMatrixMoritaRow B)
        (GradedMatrixMoritaColumn.leftAction (B := B))) :=
    completionCStarModule (B := B)
      (E := PreHilbertModuleTensor (E := GradedMatrixMoritaRow B)
        (GradedMatrixMoritaColumn.leftAction (B := B)))
  let e := opStarAlgEquiv (β.automorphism g)
  let eL : Bᵐᵒᵖ →ₗᵢ[ℂ] Bᵐᵒᵖ :=
    { toLinearMap := { toFun := e, map_add' := map_add e, map_smul' := map_smul e }
      norm_map' := StarAlgEquiv.norm_map e }
  have h : (rowColumnCompleted (B := B)).toContinuousLinearMap.comp
      ((rowColumnTensorAction β).action g).toContinuousLinearEquiv.toContinuousLinearMap =
      eL.toContinuousLinearMap.comp (rowColumnCompleted (B := B)).toContinuousLinearMap := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change rowColumnCompleted (B := B)
      (((rowAction β).interiorTensor (columnAction β) (columnRepresentation_equivariant β)).action g
        (interiorModuleTensorMk (B := GradedMatrixMoritaMatrix B) (C := B)
          (E := GradedMatrixMoritaRow B) (F := GradedMatrixMoritaColumn B)
          (GradedMatrixMoritaColumn.leftAction (B := B)) x y)) =
      opStarAlgEquiv (β.automorphism g)
        (rowColumnCompleted (B := B)
          (interiorModuleTensorMk (B := GradedMatrixMoritaMatrix B) (C := B)
            (E := GradedMatrixMoritaRow B) (F := GradedMatrixMoritaColumn B)
            (GradedMatrixMoritaColumn.leftAction (B := B)) x y))
    rw [EquivariantHilbertModule.interiorTensor_action_mk
      (φ := GradedMatrixMoritaColumn.leftAction (B := B))
      (rowAction β) (columnAction β) (columnRepresentation_equivariant β) g x y,
      rowColumnCompleted_mk, rowColumnCompleted_mk]
    exact rowColumn_equivariant β g x y
  have hpoint := DFunLike.congr_fun h u
  change rowColumnCompleted (B := B) ((rowColumnTensorAction β).action g u) =
    opStarAlgEquiv (β.automorphism g) (rowColumnCompleted (B := B) u) at hpoint
  change rowColumnCompleted (B := B) ((rowColumnTensorAction β).action g u) =
    opStarAlgEquiv (β.automorphism g) (rowColumnCompleted (B := B) u)
  exact hpoint

end GradedMatrixMoritaEquivariant
end BC4lean.KKTheory
