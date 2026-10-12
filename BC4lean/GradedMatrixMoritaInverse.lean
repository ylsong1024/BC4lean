import BC4lean.GradedMatrixMoritaCycle
import BC4lean.GradedMatrixMoritaTensorUnitary
import BC4lean.GradedKasparovCycleIso

/-! # Actual inverse double-tensor isomorphisms for whole Morita cycles

The module inverse is the genuine associator followed by the genuine paired
Morita contraction and the actual right tensor unit. Its triple formula
proves grading, group action, representation and operator intertwinings for
the entire original cycle. No inverse cycle law or KK equivalence is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory.GradedMatrixMoritaInverse
open scoped InnerProductSpace
open GradedMatrixMoritaContractions GradedMatrixMoritaCompletion GradedMatrixMoritaEquivariant

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem rowColumnUnitary_left (b : B)
    (w : InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B) (E := GradedMatrixMoritaRow B) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) :
    rowColumnUnitary (B := B) (interiorModuleTensorOperator (GradedMatrixMoritaColumn.leftAction (B := B))
      ((GradedMatrixMoritaRow.leftAction (B := B)) b) w) = standardLeftMul b (rowColumnUnitary w) := by
  let L := (rowColumnCompleted (B := B)).toContinuousLinearMap
  have h : L.comp (interiorModuleTensorOperator (GradedMatrixMoritaColumn.leftAction (B := B))
      ((GradedMatrixMoritaRow.leftAction (B := B)) b)).toCLM = (standardLeftMul b).toCLM.comp L := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro r x
    change rowColumnUnitary (B := B)
      (interiorModuleTensorOperator (GradedMatrixMoritaColumn.leftAction (B := B))
        (GradedMatrixMoritaRow.leftAction b) (interiorModuleTensorMk
          (GradedMatrixMoritaColumn.leftAction (B := B)) r x)) =
      standardLeftMul b (rowColumnUnitary (B := B) (interiorModuleTensorMk
        (GradedMatrixMoritaColumn.leftAction (B := B)) r x))
    rw [interiorModuleTensorOperator_mk, rowColumnUnitary_mk, rowColumnUnitary_mk]
    apply MulOpposite.unop_injective
    change (∑ j : Fin 2, (GradedMatrixMoritaMatrix.corner b * GradedMatrixMoritaRow.matrix r) 0 j *
      MulOpposite.unop (x j)) = b * (∑ j : Fin 2, GradedMatrixMoritaRow.matrix r 0 j * MulOpposite.unop (x j))
    simp [GradedMatrixMoritaMatrix.corner, CStarMatrix.mul_apply, CStarMatrix.ofMatrix_apply, Fin.sum_univ_two, mul_add, mul_assoc]
  exact DFunLike.congr_fun h w

theorem columnRowUnitary_left (M : GradedMatrixMoritaMatrix B)
    (w : InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B) (E := GradedMatrixMoritaColumn B) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) :
    columnRowUnitary (B := B) (interiorModuleTensorOperator (GradedMatrixMoritaRow.leftAction (B := B))
      ((GradedMatrixMoritaColumn.leftAction (B := B)) M) w) = standardLeftMul M (columnRowUnitary w) := by
  let L := (columnRowCompleted (B := B)).toContinuousLinearMap
  have h : L.comp (interiorModuleTensorOperator (GradedMatrixMoritaRow.leftAction (B := B))
      ((GradedMatrixMoritaColumn.leftAction (B := B)) M)).toCLM = (standardLeftMul M).toCLM.comp L := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x r
    change columnRowUnitary (B := B)
      (interiorModuleTensorOperator (GradedMatrixMoritaRow.leftAction (B := B))
        (GradedMatrixMoritaColumn.leftAction M) (interiorModuleTensorMk
          (GradedMatrixMoritaRow.leftAction (B := B)) x r)) =
      standardLeftMul M (columnRowUnitary (B := B) (interiorModuleTensorMk
        (GradedMatrixMoritaRow.leftAction (B := B)) x r))
    rw [interiorModuleTensorOperator_mk, columnRowUnitary_mk, columnRowUnitary_mk]
    apply MulOpposite.unop_injective
    ext i j
    simp [columnRow, GradedMatrixMoritaColumn.leftAction_apply,
      CStarMatrix.mul_apply, Fin.sum_univ_two, add_mul, mul_assoc]
    rfl
  exact DFunLike.congr_fun h w

section Modules

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

def coefficientModuleEquiv : HilbertModuleEquiv B
    (InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
      (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B)))
      (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) E :=
  (InteriorModuleTensorAssociator.hilbertEquiv
    (B := B) (C := GradedMatrixMoritaMatrix B) (D := B)
    (E := E) (F := GradedMatrixMoritaRow B) (G := GradedMatrixMoritaColumn B)
    (GradedMatrixMoritaRow.leftAction (B := B))
    (GradedMatrixMoritaColumn.leftAction (B := B))).trans
    ((GradedMatrixMoritaTensorUnitary.hilbertEquiv
      (B := B) (C := B) (E := E)
      (F := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := GradedMatrixMoritaRow B) (F := GradedMatrixMoritaColumn B)
        (GradedMatrixMoritaColumn.leftAction (B := B))) (G := Bᵐᵒᵖ)
      (InteriorModuleTensorAssociator.rightRepresentation
        (GradedMatrixMoritaRow.leftAction (B := B))
        (GradedMatrixMoritaColumn.leftAction (B := B)))
      (standardLeftMul (B := B)) (rowColumnUnitary (B := B))
      (rowColumnUnitary_left (B := B))).trans
      (rightStandardInteriorModuleTensorHilbertEquiv (B := B) (E := E)))

@[simp] theorem coefficientModuleEquiv_triple (x : E) (r : GradedMatrixMoritaRow B)
    (y : GradedMatrixMoritaColumn B) :
    coefficientModuleEquiv (interiorModuleTensorMk (GradedMatrixMoritaColumn.leftAction (B := B))
      (interiorModuleTensorMk (GradedMatrixMoritaRow.leftAction (B := B)) x r) y) = rowColumn r y • x := by
  simp only [coefficientModuleEquiv, HilbertModuleEquiv.trans_apply,
    InteriorModuleTensorAssociator.hilbertEquiv_triple]
  simpa only [rowColumnUnitary_mk, rightStandardInteriorModuleTensorHilbertEquiv_mk] using
    congrArg (rightStandardInteriorModuleTensorHilbertEquiv (B := B) (E := E))
      (GradedMatrixMoritaTensorUnitary.hilbertEquiv_mk
        (B := B) (C := B) (E := E)
        (F := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
      (E := GradedMatrixMoritaRow B) (F := GradedMatrixMoritaColumn B)
      (GradedMatrixMoritaColumn.leftAction (B := B))) (G := (B)ᵐᵒᵖ)
        (InteriorModuleTensorAssociator.rightRepresentation
          (GradedMatrixMoritaRow.leftAction (B := B)) (GradedMatrixMoritaColumn.leftAction (B := B)))
        (standardLeftMul (B := B)) (rowColumnUnitary (B := B))
        (rowColumnUnitary_left (B := B)) x
        (interiorModuleTensorMk (GradedMatrixMoritaColumn.leftAction (B := B)) r y))

end Modules

section MatrixModules

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul (GradedMatrixMoritaMatrix B)ᵐᵒᵖ E] [CStarModule (GradedMatrixMoritaMatrix B)ᵐᵒᵖ E]
  [CompleteSpace E]

def matrixModuleEquiv : HilbertModuleEquiv (GradedMatrixMoritaMatrix B)
    (InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
      (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B)))
      (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) E :=
  (InteriorModuleTensorAssociator.hilbertEquiv
    (B := GradedMatrixMoritaMatrix B) (C := B) (D := GradedMatrixMoritaMatrix B)
    (E := E) (F := GradedMatrixMoritaColumn B) (G := GradedMatrixMoritaRow B)
    (GradedMatrixMoritaColumn.leftAction (B := B))
    (GradedMatrixMoritaRow.leftAction (B := B))).trans
    ((GradedMatrixMoritaTensorUnitary.hilbertEquiv
      (B := GradedMatrixMoritaMatrix B) (C := GradedMatrixMoritaMatrix B) (E := E)
      (F := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := GradedMatrixMoritaColumn B) (F := GradedMatrixMoritaRow B)
        (GradedMatrixMoritaRow.leftAction (B := B))) (G := (GradedMatrixMoritaMatrix B)ᵐᵒᵖ)
      (InteriorModuleTensorAssociator.rightRepresentation
        (GradedMatrixMoritaColumn.leftAction (B := B))
        (GradedMatrixMoritaRow.leftAction (B := B)))
      (standardLeftMul (B := GradedMatrixMoritaMatrix B)) (columnRowUnitary (B := B))
      (columnRowUnitary_left (B := B))).trans
      (rightStandardInteriorModuleTensorHilbertEquiv (B := GradedMatrixMoritaMatrix B) (E := E)))

@[simp] theorem matrixModuleEquiv_triple (x : E) (y : GradedMatrixMoritaColumn B)
    (r : GradedMatrixMoritaRow B) :
    matrixModuleEquiv (interiorModuleTensorMk (GradedMatrixMoritaRow.leftAction (B := B))
      (interiorModuleTensorMk (GradedMatrixMoritaColumn.leftAction (B := B)) x y) r) = columnRow y r • x := by
  simp only [matrixModuleEquiv, HilbertModuleEquiv.trans_apply,
    InteriorModuleTensorAssociator.hilbertEquiv_triple]
  simpa only [columnRowUnitary_mk, rightStandardInteriorModuleTensorHilbertEquiv_mk] using
    congrArg (rightStandardInteriorModuleTensorHilbertEquiv (B := GradedMatrixMoritaMatrix B) (E := E))
      (GradedMatrixMoritaTensorUnitary.hilbertEquiv_mk
        (B := GradedMatrixMoritaMatrix B) (C := GradedMatrixMoritaMatrix B) (E := E)
        (F := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
      (E := GradedMatrixMoritaColumn B) (F := GradedMatrixMoritaRow B)
      (GradedMatrixMoritaRow.leftAction (B := B))) (G := (GradedMatrixMoritaMatrix B)ᵐᵒᵖ)
        (InteriorModuleTensorAssociator.rightRepresentation
          (GradedMatrixMoritaColumn.leftAction (B := B)) (GradedMatrixMoritaRow.leftAction (B := B)))
        (standardLeftMul (B := GradedMatrixMoritaMatrix B)) (columnRowUnitary (B := B))
        (columnRowUnitary_left (B := B)) x
        (interiorModuleTensorMk (GradedMatrixMoritaRow.leftAction (B := B)) y r))

end MatrixModules

section CoefficientCycles

variable {Γ A E : Type*} [Group Γ] [NonUnitalCStarAlgebra A] [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {δA : CStarGrading A}
  (β : CStarAlgebraAction Γ B) (c : GradedKasparovCycle α β δA CStarGrading.trivial E)

def coefficientDoubleCycle := GradedMatrixMoritaCycle.matrixToCoefficient β
  (GradedMatrixMoritaCycle.coefficientToMatrix β c)

set_option maxHeartbeats 4800000 in
def coefficientCycleIso : GradedKasparovCycleIso (coefficientDoubleCycle β c) c where
  moduleEquiv := coefficientModuleEquiv (B := B) (E := E)
  grading_intertwine u := by
    let : CStarModule (GradedMatrixMoritaMatrix B)ᵐᵒᵖ (PreHilbertModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) :=
      preModuleTensorCStarModule (B := B) (C := GradedMatrixMoritaMatrix B) (E := E)
        (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))
    let : CStarModule (GradedMatrixMoritaMatrix B)ᵐᵒᵖ (InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) :=
      completionCStarModule (B := GradedMatrixMoritaMatrix B) (E := PreHilbertModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B)))
    let : CStarModule (B)ᵐᵒᵖ (PreHilbertModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) :=
      preModuleTensorCStarModule (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))
    let : CStarModule (B)ᵐᵒᵖ (InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) :=
      completionCStarModule (B := B) (E := PreHilbertModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B)))
    have hRow : ModuleTensorRepresentationGraded
        (δB := (CStarGrading.trivial : CStarGrading B))
        (GradedMatrixMoritaRow.leftAction (B := B)) (GradedMatrixMoritaRow.grading (B := B)) := by
      intro b r
      change GradedMatrixMoritaRow.parity (GradedMatrixMoritaRow.leftAction b r) =
        GradedMatrixMoritaRow.leftAction b (GradedMatrixMoritaRow.parity r)
      exact GradedMatrixMoritaRow.leftAction_graded b r
    have hColumn : ModuleTensorRepresentationGraded
        (δB := (GradedMatrixMoritaMatrix.grading : CStarGrading (GradedMatrixMoritaMatrix B)))
        (GradedMatrixMoritaColumn.leftAction (B := B)) (GradedMatrixMoritaColumn.grading (B := B)) := by
      intro M y
      change GradedMatrixMoritaColumn.parity (GradedMatrixMoritaColumn.leftAction M y) =
        GradedMatrixMoritaColumn.leftAction (GradedMatrixMoritaMatrix.parity M)
          (GradedMatrixMoritaColumn.parity y)
      exact GradedMatrixMoritaColumn.leftAction_graded M y
    let L : (InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) →L[ℂ] E :=
      (coefficientModuleEquiv (B := B) (E := E)).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
    have h : L.comp (coefficientDoubleCycle β c).grading.grading.toContinuousLinearEquiv.toContinuousLinearMap =
        c.grading.grading.toContinuousLinearEquiv.toContinuousLinearMap.comp L := by
      apply InteriorModuleTensorAssociator.left_clm_ext
        (B := B) (C := GradedMatrixMoritaMatrix B) (D := B) (E := E)
        (F := GradedMatrixMoritaRow B) (G := GradedMatrixMoritaColumn B)
        (GradedMatrixMoritaRow.leftAction (B := B)) (GradedMatrixMoritaColumn.leftAction (B := B))
      intro x r y
      change coefficientModuleEquiv (B := B) (E := E)
        (((c.grading.interiorTensor (φ := GradedMatrixMoritaRow.leftAction (B := B))
          (GradedMatrixMoritaRow.grading (B := B)) hRow).interiorTensor
            (φ := GradedMatrixMoritaColumn.leftAction (B := B)) (GradedMatrixMoritaColumn.grading (B := B))
              hColumn).grading
          (interiorModuleTensorMk (B := GradedMatrixMoritaMatrix B) (C := B)
          (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B) (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B)) (interiorModuleTensorMk (B := B) (C := GradedMatrixMoritaMatrix B) (E := E)
            (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B)) x r) y)) = c.grading.grading (coefficientModuleEquiv (B := B) (E := E) (interiorModuleTensorMk (B := GradedMatrixMoritaMatrix B) (C := B)
          (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B) (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B)) (interiorModuleTensorMk (B := B) (C := GradedMatrixMoritaMatrix B) (E := E)
            (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B)) x r) y))
      rw [GradedHilbertModule.interiorTensor_grading_mk,
        GradedHilbertModule.interiorTensor_grading_mk,
        coefficientModuleEquiv_triple, coefficientModuleEquiv_triple, GradedHilbertModule.map_op_smul]
      exact congrArg (fun b : Bᵐᵒᵖ => b • c.grading.grading x) (rowColumn_graded (B := B) r y)
    exact DFunLike.congr_fun h u
  action_intertwine g u := by
    have hRowAction : ModuleTensorRepresentationEquivariant
        (GradedMatrixMoritaRow.leftAction (B := B)) β (rowAction β) := by
      intro g' b r
      change (rowAction β).action g' ((GradedMatrixMoritaRow.leftAction (B := B) b).toCLM r) =
        (GradedMatrixMoritaRow.leftAction (B := B) (β.automorphism g' b)).toCLM
          ((rowAction β).action g' r)
      exact rowRepresentation_equivariant (B := B) β g' b r
    have hColumnAction : ModuleTensorRepresentationEquivariant
        (GradedMatrixMoritaColumn.leftAction (B := B)) (matrixAction β) (columnAction β) := by
      intro g' M x
      change (columnAction β).action g' ((GradedMatrixMoritaColumn.leftAction (B := B) M).toCLM x) =
        (GradedMatrixMoritaColumn.leftAction (B := B) ((matrixAction β).automorphism g' M)).toCLM
          ((columnAction β).action g' x)
      exact columnRepresentation_equivariant (B := B) β g' M x
    let : CStarModule (GradedMatrixMoritaMatrix B)ᵐᵒᵖ (PreHilbertModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) :=
      preModuleTensorCStarModule (B := B) (C := GradedMatrixMoritaMatrix B) (E := E)
        (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))
    let : CStarModule (GradedMatrixMoritaMatrix B)ᵐᵒᵖ (InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) :=
      completionCStarModule (B := GradedMatrixMoritaMatrix B) (E := PreHilbertModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B)))
    let : CStarModule (B)ᵐᵒᵖ (PreHilbertModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) :=
      preModuleTensorCStarModule (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))
    let : CStarModule (B)ᵐᵒᵖ (InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) :=
      completionCStarModule (B := B) (E := PreHilbertModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B)))
    let L : (InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) →L[ℂ] E :=
      (coefficientModuleEquiv (B := B) (E := E)).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
    have h : L.comp ((coefficientDoubleCycle β c).groupAction.action g).toContinuousLinearEquiv.toContinuousLinearMap =
        (c.groupAction.action g).toContinuousLinearEquiv.toContinuousLinearMap.comp L := by
      apply InteriorModuleTensorAssociator.left_clm_ext
        (B := B) (C := GradedMatrixMoritaMatrix B) (D := B) (E := E)
        (F := GradedMatrixMoritaRow B) (G := GradedMatrixMoritaColumn B)
        (GradedMatrixMoritaRow.leftAction (B := B)) (GradedMatrixMoritaColumn.leftAction (B := B))
      intro x r y
      change coefficientModuleEquiv (B := B) (E := E)
        (((c.groupAction.interiorTensor (φ := GradedMatrixMoritaRow.leftAction (B := B))
          (rowAction β) hRowAction).interiorTensor
            (φ := GradedMatrixMoritaColumn.leftAction (B := B)) (columnAction β) hColumnAction).action g
          (interiorModuleTensorMk (B := GradedMatrixMoritaMatrix B) (C := B)
          (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B) (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B)) (interiorModuleTensorMk (B := B) (C := GradedMatrixMoritaMatrix B) (E := E)
            (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B)) x r) y)) = c.groupAction.action g (coefficientModuleEquiv (B := B) (E := E) (interiorModuleTensorMk (B := GradedMatrixMoritaMatrix B) (C := B)
          (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B) (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B)) (interiorModuleTensorMk (B := B) (C := GradedMatrixMoritaMatrix B) (E := E)
            (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B)) x r) y))
      rw [EquivariantHilbertModule.interiorTensor_action_mk,
        EquivariantHilbertModule.interiorTensor_action_mk,
        coefficientModuleEquiv_triple, coefficientModuleEquiv_triple, EquivariantHilbertModule.map_op_smul]
      exact congrArg (fun b : Bᵐᵒᵖ => b • c.groupAction.action g x) (rowColumn_equivariant (B := B) β g r y)
    exact DFunLike.congr_fun h u
  representation_intertwine a u := by
    let : CStarModule (GradedMatrixMoritaMatrix B)ᵐᵒᵖ (PreHilbertModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) :=
      preModuleTensorCStarModule (B := B) (C := GradedMatrixMoritaMatrix B) (E := E)
        (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))
    let : CStarModule (GradedMatrixMoritaMatrix B)ᵐᵒᵖ (InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) :=
      completionCStarModule (B := GradedMatrixMoritaMatrix B) (E := PreHilbertModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B)))
    let : CStarModule (B)ᵐᵒᵖ (PreHilbertModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) :=
      preModuleTensorCStarModule (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))
    let : CStarModule (B)ᵐᵒᵖ (InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) :=
      completionCStarModule (B := B) (E := PreHilbertModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B)))
    let L : (InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) →L[ℂ] E :=
      (coefficientModuleEquiv (B := B) (E := E)).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
    have h : L.comp ((coefficientDoubleCycle β c).representation a).toCLM = (c.representation a).toCLM.comp L := by
      apply InteriorModuleTensorAssociator.left_clm_ext
        (B := B) (C := GradedMatrixMoritaMatrix B) (D := B) (E := E)
        (F := GradedMatrixMoritaRow B) (G := GradedMatrixMoritaColumn B)
        (GradedMatrixMoritaRow.leftAction (B := B)) (GradedMatrixMoritaColumn.leftAction (B := B))
      intro x r y
      change coefficientModuleEquiv (B := B) (E := E)
        (interiorModuleTensorOperator (B := GradedMatrixMoritaMatrix B) (C := B)
          (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B) (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))
          (interiorModuleTensorOperator (B := B) (C := GradedMatrixMoritaMatrix B) (E := E)
            (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B)) (c.representation a))
          (interiorModuleTensorMk (B := GradedMatrixMoritaMatrix B) (C := B)
          (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B) (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))
            (interiorModuleTensorMk (B := B) (C := GradedMatrixMoritaMatrix B) (E := E)
            (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B)) x r) y)) =
        c.representation a (coefficientModuleEquiv (B := B) (E := E)
          (interiorModuleTensorMk (B := GradedMatrixMoritaMatrix B) (C := B)
          (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B) (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))
            (interiorModuleTensorMk (B := B) (C := GradedMatrixMoritaMatrix B) (E := E)
            (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B)) x r) y))
      rw [interiorModuleTensorOperator_mk, interiorModuleTensorOperator_mk,
        coefficientModuleEquiv_triple, coefficientModuleEquiv_triple, (c.representation a).map_op_smul]
    exact DFunLike.congr_fun h u
  operator_intertwine u := by
    let : CStarModule (GradedMatrixMoritaMatrix B)ᵐᵒᵖ (PreHilbertModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) :=
      preModuleTensorCStarModule (B := B) (C := GradedMatrixMoritaMatrix B) (E := E)
        (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))
    let : CStarModule (GradedMatrixMoritaMatrix B)ᵐᵒᵖ (InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) :=
      completionCStarModule (B := GradedMatrixMoritaMatrix B) (E := PreHilbertModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B)))
    let : CStarModule (B)ᵐᵒᵖ (PreHilbertModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) :=
      preModuleTensorCStarModule (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))
    let : CStarModule (B)ᵐᵒᵖ (InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) :=
      completionCStarModule (B := B) (E := PreHilbertModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B)))
    let L : (InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) →L[ℂ] E :=
      (coefficientModuleEquiv (B := B) (E := E)).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
    have h : L.comp (coefficientDoubleCycle β c).operator.toCLM = c.operator.toCLM.comp L := by
      apply InteriorModuleTensorAssociator.left_clm_ext
        (B := B) (C := GradedMatrixMoritaMatrix B) (D := B) (E := E)
        (F := GradedMatrixMoritaRow B) (G := GradedMatrixMoritaColumn B)
        (GradedMatrixMoritaRow.leftAction (B := B)) (GradedMatrixMoritaColumn.leftAction (B := B))
      intro x r y
      change coefficientModuleEquiv (B := B) (E := E)
        (interiorModuleTensorOperator (B := GradedMatrixMoritaMatrix B) (C := B)
          (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B) (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))
          (interiorModuleTensorOperator (B := B) (C := GradedMatrixMoritaMatrix B) (E := E)
            (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B)) (c.operator))
          (interiorModuleTensorMk (B := GradedMatrixMoritaMatrix B) (C := B)
          (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B) (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))
            (interiorModuleTensorMk (B := B) (C := GradedMatrixMoritaMatrix B) (E := E)
            (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B)) x r) y)) =
        c.operator (coefficientModuleEquiv (B := B) (E := E)
          (interiorModuleTensorMk (B := GradedMatrixMoritaMatrix B) (C := B)
          (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B) (E := E) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))
            (interiorModuleTensorMk (B := B) (C := GradedMatrixMoritaMatrix B) (E := E)
            (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B)) x r) y))
      rw [interiorModuleTensorOperator_mk, interiorModuleTensorOperator_mk,
        coefficientModuleEquiv_triple, coefficientModuleEquiv_triple, c.operator.map_op_smul]
    exact DFunLike.congr_fun h u

end CoefficientCycles

section MatrixCycles

variable {Γ A E : Type*} [Group Γ] [NonUnitalCStarAlgebra A] [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul (GradedMatrixMoritaMatrix B)ᵐᵒᵖ E]
  [CStarModule (GradedMatrixMoritaMatrix B)ᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {δA : CStarGrading A}
  (β : CStarAlgebraAction Γ B)
  (c : GradedKasparovCycle α (matrixAction β) δA GradedMatrixMoritaMatrix.grading E)

def matrixDoubleCycle := GradedMatrixMoritaCycle.coefficientToMatrix β
  (GradedMatrixMoritaCycle.matrixToCoefficient β c)

set_option maxHeartbeats 4800000 in
def matrixCycleIso : GradedKasparovCycleIso (matrixDoubleCycle β c) c where
  moduleEquiv := matrixModuleEquiv (B := B) (E := E)
  grading_intertwine u := by
    let : CStarModule (B)ᵐᵒᵖ (PreHilbertModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) :=
      preModuleTensorCStarModule (B := GradedMatrixMoritaMatrix B) (C := B) (E := E)
        (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))
    let : CStarModule (B)ᵐᵒᵖ (InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) :=
      completionCStarModule (B := B) (E := PreHilbertModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B)))
    let : CStarModule (GradedMatrixMoritaMatrix B)ᵐᵒᵖ (PreHilbertModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) :=
      preModuleTensorCStarModule (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))
    let : CStarModule (GradedMatrixMoritaMatrix B)ᵐᵒᵖ (InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) :=
      completionCStarModule (B := GradedMatrixMoritaMatrix B) (E := PreHilbertModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B)))
    have hRow : ModuleTensorRepresentationGraded
        (δB := (CStarGrading.trivial : CStarGrading B))
        (GradedMatrixMoritaRow.leftAction (B := B)) (GradedMatrixMoritaRow.grading (B := B)) := by
      intro b r
      change GradedMatrixMoritaRow.parity (GradedMatrixMoritaRow.leftAction b r) =
        GradedMatrixMoritaRow.leftAction b (GradedMatrixMoritaRow.parity r)
      exact GradedMatrixMoritaRow.leftAction_graded b r
    have hColumn : ModuleTensorRepresentationGraded
        (δB := (GradedMatrixMoritaMatrix.grading : CStarGrading (GradedMatrixMoritaMatrix B)))
        (GradedMatrixMoritaColumn.leftAction (B := B)) (GradedMatrixMoritaColumn.grading (B := B)) := by
      intro M y
      change GradedMatrixMoritaColumn.parity (GradedMatrixMoritaColumn.leftAction M y) =
        GradedMatrixMoritaColumn.leftAction (GradedMatrixMoritaMatrix.parity M)
          (GradedMatrixMoritaColumn.parity y)
      exact GradedMatrixMoritaColumn.leftAction_graded M y
    let L : (InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) →L[ℂ] E :=
      (matrixModuleEquiv (B := B) (E := E)).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
    have h : L.comp (matrixDoubleCycle β c).grading.grading.toContinuousLinearEquiv.toContinuousLinearMap =
        c.grading.grading.toContinuousLinearEquiv.toContinuousLinearMap.comp L := by
      apply InteriorModuleTensorAssociator.left_clm_ext
        (B := GradedMatrixMoritaMatrix B) (C := B) (D := GradedMatrixMoritaMatrix B) (E := E)
        (F := GradedMatrixMoritaColumn B) (G := GradedMatrixMoritaRow B)
        (GradedMatrixMoritaColumn.leftAction (B := B)) (GradedMatrixMoritaRow.leftAction (B := B))
      intro x y r
      change matrixModuleEquiv (B := B) (E := E)
        (((c.grading.interiorTensor (φ := GradedMatrixMoritaColumn.leftAction (B := B))
          (GradedMatrixMoritaColumn.grading (B := B)) hColumn).interiorTensor
            (φ := GradedMatrixMoritaRow.leftAction (B := B)) (GradedMatrixMoritaRow.grading (B := B))
              hRow).grading
          (interiorModuleTensorMk (B := B) (C := GradedMatrixMoritaMatrix B)
          (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B) (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B)) (interiorModuleTensorMk (B := GradedMatrixMoritaMatrix B) (C := B) (E := E)
            (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B)) x y) r)) = c.grading.grading (matrixModuleEquiv (B := B) (E := E) (interiorModuleTensorMk (B := B) (C := GradedMatrixMoritaMatrix B)
          (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B) (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B)) (interiorModuleTensorMk (B := GradedMatrixMoritaMatrix B) (C := B) (E := E)
            (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B)) x y) r))
      rw [GradedHilbertModule.interiorTensor_grading_mk,
        GradedHilbertModule.interiorTensor_grading_mk,
        matrixModuleEquiv_triple, matrixModuleEquiv_triple, GradedHilbertModule.map_op_smul]
      exact congrArg (fun b : (GradedMatrixMoritaMatrix B)ᵐᵒᵖ => b • c.grading.grading x) (columnRow_graded (B := B) y r)
    exact DFunLike.congr_fun h u
  action_intertwine g u := by
    have hRowAction : ModuleTensorRepresentationEquivariant
        (GradedMatrixMoritaRow.leftAction (B := B)) β (rowAction β) := by
      intro g' b r
      change (rowAction β).action g' ((GradedMatrixMoritaRow.leftAction (B := B) b).toCLM r) =
        (GradedMatrixMoritaRow.leftAction (B := B) (β.automorphism g' b)).toCLM
          ((rowAction β).action g' r)
      exact rowRepresentation_equivariant (B := B) β g' b r
    have hColumnAction : ModuleTensorRepresentationEquivariant
        (GradedMatrixMoritaColumn.leftAction (B := B)) (matrixAction β) (columnAction β) := by
      intro g' M x
      change (columnAction β).action g' ((GradedMatrixMoritaColumn.leftAction (B := B) M).toCLM x) =
        (GradedMatrixMoritaColumn.leftAction (B := B) ((matrixAction β).automorphism g' M)).toCLM
          ((columnAction β).action g' x)
      exact columnRepresentation_equivariant (B := B) β g' M x
    let : CStarModule (B)ᵐᵒᵖ (PreHilbertModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) :=
      preModuleTensorCStarModule (B := GradedMatrixMoritaMatrix B) (C := B) (E := E)
        (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))
    let : CStarModule (B)ᵐᵒᵖ (InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) :=
      completionCStarModule (B := B) (E := PreHilbertModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B)))
    let : CStarModule (GradedMatrixMoritaMatrix B)ᵐᵒᵖ (PreHilbertModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) :=
      preModuleTensorCStarModule (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))
    let : CStarModule (GradedMatrixMoritaMatrix B)ᵐᵒᵖ (InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) :=
      completionCStarModule (B := GradedMatrixMoritaMatrix B) (E := PreHilbertModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B)))
    let L : (InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) →L[ℂ] E :=
      (matrixModuleEquiv (B := B) (E := E)).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
    have h : L.comp ((matrixDoubleCycle β c).groupAction.action g).toContinuousLinearEquiv.toContinuousLinearMap =
        (c.groupAction.action g).toContinuousLinearEquiv.toContinuousLinearMap.comp L := by
      apply InteriorModuleTensorAssociator.left_clm_ext
        (B := GradedMatrixMoritaMatrix B) (C := B) (D := GradedMatrixMoritaMatrix B) (E := E)
        (F := GradedMatrixMoritaColumn B) (G := GradedMatrixMoritaRow B)
        (GradedMatrixMoritaColumn.leftAction (B := B)) (GradedMatrixMoritaRow.leftAction (B := B))
      intro x y r
      change matrixModuleEquiv (B := B) (E := E)
        (((c.groupAction.interiorTensor (φ := GradedMatrixMoritaColumn.leftAction (B := B))
          (columnAction β) hColumnAction).interiorTensor
            (φ := GradedMatrixMoritaRow.leftAction (B := B)) (rowAction β) hRowAction).action g
          (interiorModuleTensorMk (B := B) (C := GradedMatrixMoritaMatrix B)
          (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B) (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B)) (interiorModuleTensorMk (B := GradedMatrixMoritaMatrix B) (C := B) (E := E)
            (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B)) x y) r)) = c.groupAction.action g (matrixModuleEquiv (B := B) (E := E) (interiorModuleTensorMk (B := B) (C := GradedMatrixMoritaMatrix B)
          (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B) (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B)) (interiorModuleTensorMk (B := GradedMatrixMoritaMatrix B) (C := B) (E := E)
            (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B)) x y) r))
      rw [EquivariantHilbertModule.interiorTensor_action_mk,
        EquivariantHilbertModule.interiorTensor_action_mk,
        matrixModuleEquiv_triple, matrixModuleEquiv_triple, EquivariantHilbertModule.map_op_smul]
      exact congrArg (fun b : (GradedMatrixMoritaMatrix B)ᵐᵒᵖ => b • c.groupAction.action g x) (columnRow_equivariant (B := B) β g y r)
    exact DFunLike.congr_fun h u
  representation_intertwine a u := by
    let : CStarModule (B)ᵐᵒᵖ (PreHilbertModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) :=
      preModuleTensorCStarModule (B := GradedMatrixMoritaMatrix B) (C := B) (E := E)
        (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))
    let : CStarModule (B)ᵐᵒᵖ (InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) :=
      completionCStarModule (B := B) (E := PreHilbertModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B)))
    let : CStarModule (GradedMatrixMoritaMatrix B)ᵐᵒᵖ (PreHilbertModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) :=
      preModuleTensorCStarModule (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))
    let : CStarModule (GradedMatrixMoritaMatrix B)ᵐᵒᵖ (InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) :=
      completionCStarModule (B := GradedMatrixMoritaMatrix B) (E := PreHilbertModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B)))
    let L : (InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) →L[ℂ] E :=
      (matrixModuleEquiv (B := B) (E := E)).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
    have h : L.comp ((matrixDoubleCycle β c).representation a).toCLM = (c.representation a).toCLM.comp L := by
      apply InteriorModuleTensorAssociator.left_clm_ext
        (B := GradedMatrixMoritaMatrix B) (C := B) (D := GradedMatrixMoritaMatrix B) (E := E)
        (F := GradedMatrixMoritaColumn B) (G := GradedMatrixMoritaRow B)
        (GradedMatrixMoritaColumn.leftAction (B := B)) (GradedMatrixMoritaRow.leftAction (B := B))
      intro x y r
      change matrixModuleEquiv (B := B) (E := E)
        (interiorModuleTensorOperator (B := B) (C := GradedMatrixMoritaMatrix B)
          (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B) (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))
          (interiorModuleTensorOperator (B := GradedMatrixMoritaMatrix B) (C := B) (E := E)
            (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B)) (c.representation a))
          (interiorModuleTensorMk (B := B) (C := GradedMatrixMoritaMatrix B)
          (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B) (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))
            (interiorModuleTensorMk (B := GradedMatrixMoritaMatrix B) (C := B) (E := E)
            (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B)) x y) r)) =
        c.representation a (matrixModuleEquiv (B := B) (E := E)
          (interiorModuleTensorMk (B := B) (C := GradedMatrixMoritaMatrix B)
          (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B) (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))
            (interiorModuleTensorMk (B := GradedMatrixMoritaMatrix B) (C := B) (E := E)
            (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B)) x y) r))
      rw [interiorModuleTensorOperator_mk, interiorModuleTensorOperator_mk,
        matrixModuleEquiv_triple, matrixModuleEquiv_triple, (c.representation a).map_op_smul]
    exact DFunLike.congr_fun h u
  operator_intertwine u := by
    let : CStarModule (B)ᵐᵒᵖ (PreHilbertModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) :=
      preModuleTensorCStarModule (B := GradedMatrixMoritaMatrix B) (C := B) (E := E)
        (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))
    let : CStarModule (B)ᵐᵒᵖ (InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) :=
      completionCStarModule (B := B) (E := PreHilbertModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B)))
    let : CStarModule (GradedMatrixMoritaMatrix B)ᵐᵒᵖ (PreHilbertModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) :=
      preModuleTensorCStarModule (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))
    let : CStarModule (GradedMatrixMoritaMatrix B)ᵐᵒᵖ (InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) :=
      completionCStarModule (B := GradedMatrixMoritaMatrix B) (E := PreHilbertModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B)))
    let L : (InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))) →L[ℂ] E :=
      (matrixModuleEquiv (B := B) (E := E)).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
    have h : L.comp (matrixDoubleCycle β c).operator.toCLM = c.operator.toCLM.comp L := by
      apply InteriorModuleTensorAssociator.left_clm_ext
        (B := GradedMatrixMoritaMatrix B) (C := B) (D := GradedMatrixMoritaMatrix B) (E := E)
        (F := GradedMatrixMoritaColumn B) (G := GradedMatrixMoritaRow B)
        (GradedMatrixMoritaColumn.leftAction (B := B)) (GradedMatrixMoritaRow.leftAction (B := B))
      intro x y r
      change matrixModuleEquiv (B := B) (E := E)
        (interiorModuleTensorOperator (B := B) (C := GradedMatrixMoritaMatrix B)
          (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B) (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))
          (interiorModuleTensorOperator (B := GradedMatrixMoritaMatrix B) (C := B) (E := E)
            (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B)) (c.operator))
          (interiorModuleTensorMk (B := B) (C := GradedMatrixMoritaMatrix B)
          (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B) (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))
            (interiorModuleTensorMk (B := GradedMatrixMoritaMatrix B) (C := B) (E := E)
            (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B)) x y) r)) =
        c.operator (matrixModuleEquiv (B := B) (E := E)
          (interiorModuleTensorMk (B := B) (C := GradedMatrixMoritaMatrix B)
          (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B) (E := E) (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B))) (F := GradedMatrixMoritaRow B) (GradedMatrixMoritaRow.leftAction (B := B))
            (interiorModuleTensorMk (B := GradedMatrixMoritaMatrix B) (C := B) (E := E)
            (F := GradedMatrixMoritaColumn B) (GradedMatrixMoritaColumn.leftAction (B := B)) x y) r))
      rw [interiorModuleTensorOperator_mk, interiorModuleTensorOperator_mk,
        matrixModuleEquiv_triple, matrixModuleEquiv_triple, c.operator.map_op_smul]
    exact DFunLike.congr_fun h u

end MatrixCycles
end BC4lean.KKTheory.GradedMatrixMoritaInverse
