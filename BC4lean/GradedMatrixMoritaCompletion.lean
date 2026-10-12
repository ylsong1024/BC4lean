import BC4lean.GradedMatrixMoritaContractions
import Mathlib.Topology.Algebra.LinearMapCompletion

/-! # Genuine completed matrix Morita contraction unitaries

The proved coefficient forms force the explicit contractions to annihilate
the actual tensor null spaces. They descend isometrically and extend to the
actual interior-tensor completions. Surjectivity is proved using coefficient
approximate units and finite coordinate decompositions; it is not assumed.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace Topology
open Filter

namespace GradedMatrixMoritaCompletion

section EvaluationExtension

variable {B C E F H : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H] [CStarModule Cᵐᵒᵖ H]
  [CompleteSpace E] [CompleteSpace F] [CompleteSpace H]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
  (L : BalancedModuleTensor (E := E) φ →ₗ[ℂ] H)
  (hL : ∀ u v, ⟪L u, L v⟫_(Cᵐᵒᵖ) = moduleTensorInner φ u v)

/-- A form-preserving actual linear map descends through the constructed null quotient. -/
def preLinear : PreHilbertModuleTensor (E := E) φ →ₗ[ℂ] H :=
  (moduleTensorNull φ).liftQ L (by
    intro u hu
    apply (CStarModule.inner_self (A := Cᵐᵒᵖ)).mp
    rw [hL]
    exact (mem_moduleTensorNull_iff φ u).mp hu)

omit [CompleteSpace H] in
theorem preLinear_inner [CompleteSpace H] (u v : PreHilbertModuleTensor (E := E) φ) :
    ⟪preLinear φ L hL u, preLinear φ L hL v⟫_(Cᵐᵒᵖ) = ⟪u, v⟫_(Cᵐᵒᵖ) := by
  induction u using Submodule.Quotient.induction_on with
  | H u =>
    induction v using Submodule.Quotient.induction_on with
    | H v => exact hL u v

def preIsometry : PreHilbertModuleTensor (E := E) φ →ₗᵢ[ℂ] H where
  toLinearMap := preLinear φ L hL
  norm_map' u := by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ), preLinear_inner,
      ← CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ)]

def completedCLM : InteriorModuleTensor (E := E) φ →L[ℂ] H :=
  (preIsometry φ L hL).toContinuousLinearMap.fromCompletion

@[simp] theorem completedCLM_coe (u : PreHilbertModuleTensor (E := E) φ) :
    completedCLM φ L hL (moduleTensorToCompletion φ u) = preIsometry φ L hL u :=
  ContinuousLinearMap.fromCompletion_apply_coe _ u

theorem completedCLM_norm (u : InteriorModuleTensor (E := E) φ) :
    ‖completedCLM φ L hL u‖ = ‖u‖ := by
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih u =>
    change ‖completedCLM φ L hL (moduleTensorToCompletion φ u)‖ =
      ‖moduleTensorToCompletion φ u‖
    rw [completedCLM_coe, (preIsometry φ L hL).norm_map, (moduleTensorToCompletion φ).norm_map]

def completedIsometry : InteriorModuleTensor (E := E) φ →ₗᵢ[ℂ] H where
  toLinearMap := (completedCLM φ L hL).toLinearMap
  norm_map' := completedCLM_norm φ L hL

@[simp] theorem completedIsometry_mk (x : E) (y : F) :
    completedIsometry φ L hL (interiorModuleTensorMk φ x y) = L (moduleTensorMk φ x y) :=
  completedCLM_coe φ L hL (preModuleTensorMk φ x y)

theorem completedIsometry_inner (u v : InteriorModuleTensor (E := E) φ) :
    ⟪completedIsometry φ L hL u, completedIsometry φ L hL v⟫_(Cᵐᵒᵖ) = ⟪u, v⟫_(Cᵐᵒᵖ) := by
  induction u, v using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih u v =>
    change ⟪completedCLM φ L hL (moduleTensorToCompletion φ u),
      completedCLM φ L hL (moduleTensorToCompletion φ v)⟫_(Cᵐᵒᵖ) =
      ⟪moduleTensorToCompletion φ u, moduleTensorToCompletion φ v⟫_(Cᵐᵒᵖ)
    rw [completedCLM_coe, completedCLM_coe]
    exact (preLinear_inner φ L hL u v).trans (hilbertModuleToCompletion_inner u v).symm

end EvaluationExtension

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

open GradedMatrixMoritaContractions

def columnRowCompleted : InteriorModuleTensor (E := GradedMatrixMoritaColumn B)
    (GradedMatrixMoritaRow.leftAction (B := B)) →ₗᵢ[ℂ] (GradedMatrixMoritaMatrix B)ᵐᵒᵖ :=
  completedIsometry (B := B) (C := GradedMatrixMoritaMatrix B)
    (E := GradedMatrixMoritaColumn B) (F := GradedMatrixMoritaRow B)
    (H := (GradedMatrixMoritaMatrix B)ᵐᵒᵖ)
    (GradedMatrixMoritaRow.leftAction (B := B)) columnRowBalanced columnRowBalanced_inner

def rowColumnCompleted : InteriorModuleTensor (E := GradedMatrixMoritaRow B)
    (GradedMatrixMoritaColumn.leftAction (B := B)) →ₗᵢ[ℂ] Bᵐᵒᵖ :=
  completedIsometry (B := GradedMatrixMoritaMatrix B) (C := B)
    (E := GradedMatrixMoritaRow B) (F := GradedMatrixMoritaColumn B) (H := Bᵐᵒᵖ)
    (GradedMatrixMoritaColumn.leftAction (B := B)) rowColumnBalanced rowColumnBalanced_inner

@[simp] theorem columnRowCompleted_mk (x : GradedMatrixMoritaColumn B) (y : GradedMatrixMoritaRow B) :
    columnRowCompleted (interiorModuleTensorMk GradedMatrixMoritaRow.leftAction x y) = columnRow x y :=
  completedIsometry_mk _ _ _ x y
@[simp] theorem rowColumnCompleted_mk (x : GradedMatrixMoritaRow B) (y : GradedMatrixMoritaColumn B) :
    rowColumnCompleted (interiorModuleTensorMk (B := GradedMatrixMoritaMatrix B) (C := B)
      (E := GradedMatrixMoritaRow B) (F := GradedMatrixMoritaColumn B)
      (GradedMatrixMoritaColumn.leftAction (B := B)) x y) = rowColumn x y :=
  completedIsometry_mk (B := GradedMatrixMoritaMatrix B) (C := B)
    (E := GradedMatrixMoritaRow B) (F := GradedMatrixMoritaColumn B) (H := Bᵐᵒᵖ)
    (GradedMatrixMoritaColumn.leftAction (B := B)) rowColumnBalanced rowColumnBalanced_inner x y

def singleRow (j : Fin 2) (b : B) : GradedMatrixMoritaRow B :=
  ⟨MulOpposite.op (CStarMatrix.ofMatrix fun (i k : Fin 2) =>
      if i = 0 then (Pi.single j b : Fin 2 → B) k else 0), by
    intro k
    change (0 : B) = 0
    rfl⟩

theorem rowColumn_corner_single (b u : B) :
    rowColumn (GradedMatrixMoritaRow.cornerRow b) (finiteStandardSingle 0 (MulOpposite.op u)) =
      MulOpposite.op (b * u) := by
  have hentry (N : Matrix (Fin 2) (Fin 2) B) (r s : Fin 2) :
      (CStarMatrix.ofMatrix N) r s = N r s := rfl
  simp [rowColumn, GradedMatrixMoritaRow.matrix_cornerRow, GradedMatrixMoritaMatrix.corner,
    hentry, finiteStandardSingle_apply, Pi.single_apply, Fin.sum_univ_two]

theorem rowColumnCompleted_surjective : Function.Surjective (rowColumnCompleted (B := B)) := by
  intro b
  have hlim : Tendsto (fun u : B => MulOpposite.op (MulOpposite.unop b * u))
      (CStarAlgebra.approximateUnit B) (𝓝 b) :=
    (MulOpposite.continuous_op.tendsto (MulOpposite.unop b)).comp
      ((CStarAlgebra.increasingApproximateUnit B).tendsto_mul_left (MulOpposite.unop b))
  have hrange : IsClosed (Set.range (rowColumnCompleted (B := B))) :=
    (rowColumnCompleted (B := B)).isometry.isClosedEmbedding.isClosed_range
  exact hrange.mem_of_tendsto hlim (Eventually.of_forall fun u =>
    ⟨interiorModuleTensorMk (B := GradedMatrixMoritaMatrix B) (C := B)
      (E := GradedMatrixMoritaRow B) (F := GradedMatrixMoritaColumn B)
      (GradedMatrixMoritaColumn.leftAction (B := B))
      (GradedMatrixMoritaRow.cornerRow (MulOpposite.unop b))
      (finiteStandardSingle 0 (MulOpposite.op u)), by
        rw [rowColumnCompleted_mk, rowColumn_corner_single]⟩)

/-- Finite coordinate products give an actual algebraic tensor representative
of every matrix whose entries have been multiplied by u on the right. -/
theorem columnRow_coordinate_sum (M : GradedMatrixMoritaMatrix B) (u : B) :
    ∑ i : Fin 2, ∑ j : Fin 2,
      columnRow (finiteStandardSingle i (MulOpposite.op (M i j))) (singleRow j u) =
      MulOpposite.op (CStarMatrix.ofMatrix fun i j => M i j * u) := by
  have hcolumn (x : GradedMatrixMoritaColumn B) (y : GradedMatrixMoritaRow B) (r s : Fin 2) :
      MulOpposite.unop (columnRow x y) r s =
        MulOpposite.unop (x r) * GradedMatrixMoritaRow.matrix y 0 s := rfl
  have hrow (j : Fin 2) (b : B) (k : Fin 2) :
      GradedMatrixMoritaRow.matrix (singleRow j b) 0 k = (Pi.single j b : Fin 2 → B) k := rfl
  have htarget (r s : Fin 2) :
      (CStarMatrix.ofMatrix fun i j => M i j * u) r s = M r s * u := rfl
  apply MulOpposite.unop_injective
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [hcolumn, hrow, htarget,
      finiteStandardSingle_apply, Fin.sum_univ_two]

theorem columnRowCompleted_surjective : Function.Surjective (columnRowCompleted (B := B)) := by
  intro M
  have he : Tendsto (fun u : B => fun i j : Fin 2 => MulOpposite.unop M i j * u)
      (CStarAlgebra.approximateUnit B) (𝓝 (fun i j => MulOpposite.unop M i j)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact (CStarAlgebra.increasingApproximateUnit B).tendsto_mul_left (MulOpposite.unop M i j)
  have hlim : Tendsto (fun u : B =>
      MulOpposite.op (CStarMatrix.ofMatrix fun i j => MulOpposite.unop M i j * u))
      (CStarAlgebra.approximateUnit B) (𝓝 M) :=
    ((MulOpposite.continuous_op.comp (CStarMatrix.ofMatrixL (A := B)).continuous).tendsto
      (fun i j => MulOpposite.unop M i j)).comp he
  have hrange : IsClosed (Set.range (columnRowCompleted (B := B))) :=
    (columnRowCompleted (B := B)).isometry.isClosedEmbedding.isClosed_range
  apply hrange.mem_of_tendsto hlim
  exact Eventually.of_forall fun u =>
    ⟨∑ i : Fin 2, ∑ j : Fin 2, interiorModuleTensorMk (B := B) (C := GradedMatrixMoritaMatrix B)
      (E := GradedMatrixMoritaColumn B) (F := GradedMatrixMoritaRow B)
      (GradedMatrixMoritaRow.leftAction (B := B))
      (finiteStandardSingle i (MulOpposite.op (MulOpposite.unop M i j))) (singleRow j u), by
      simp only [map_sum, columnRowCompleted_mk]
      exact columnRow_coordinate_sum (MulOpposite.unop M) u⟩

/-- The actual completed column-row tensor is unitarily the standard matrix module. -/
def columnRowUnitary : HilbertModuleEquiv (GradedMatrixMoritaMatrix B)
    (InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
      (E := GradedMatrixMoritaColumn B) (F := GradedMatrixMoritaRow B)
      (GradedMatrixMoritaRow.leftAction (B := B)))
    (GradedMatrixMoritaMatrix B)ᵐᵒᵖ where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective
    (columnRowCompleted (B := B)) (columnRowCompleted_surjective (B := B))
  inner_map := completedIsometry_inner (B := B) (C := GradedMatrixMoritaMatrix B)
    (E := GradedMatrixMoritaColumn B) (F := GradedMatrixMoritaRow B)
    (H := (GradedMatrixMoritaMatrix B)ᵐᵒᵖ)
    (GradedMatrixMoritaRow.leftAction (B := B)) columnRowBalanced columnRowBalanced_inner

/-- The actual completed row-column tensor is unitarily the standard B module. -/
def rowColumnUnitary : HilbertModuleEquiv B
    (InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
      (E := GradedMatrixMoritaRow B) (F := GradedMatrixMoritaColumn B)
      (GradedMatrixMoritaColumn.leftAction (B := B))) Bᵐᵒᵖ where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective
    (rowColumnCompleted (B := B)) (rowColumnCompleted_surjective (B := B))
  inner_map := completedIsometry_inner (B := GradedMatrixMoritaMatrix B) (C := B)
    (E := GradedMatrixMoritaRow B) (F := GradedMatrixMoritaColumn B) (H := Bᵐᵒᵖ)
    (GradedMatrixMoritaColumn.leftAction (B := B)) rowColumnBalanced rowColumnBalanced_inner

@[simp] theorem columnRowUnitary_mk (x : GradedMatrixMoritaColumn B) (y : GradedMatrixMoritaRow B) :
    columnRowUnitary (B := B)
      (interiorModuleTensorMk (B := B) (C := GradedMatrixMoritaMatrix B)
        (E := GradedMatrixMoritaColumn B) (F := GradedMatrixMoritaRow B)
        (GradedMatrixMoritaRow.leftAction (B := B)) x y) = columnRow x y :=
  columnRowCompleted_mk x y
@[simp] theorem rowColumnUnitary_mk (x : GradedMatrixMoritaRow B) (y : GradedMatrixMoritaColumn B) :
    rowColumnUnitary (B := B)
      (interiorModuleTensorMk (B := GradedMatrixMoritaMatrix B) (C := B)
        (E := GradedMatrixMoritaRow B) (F := GradedMatrixMoritaColumn B)
        (GradedMatrixMoritaColumn.leftAction (B := B)) x y) = rowColumn x y :=
  rowColumnCompleted_mk x y

end GradedMatrixMoritaCompletion
end BC4lean.KKTheory
