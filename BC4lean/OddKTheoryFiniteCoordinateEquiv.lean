import BC4lean.OddKTheoryCountableSumEquiv
import BC4lean.OperatorK1Functoriality

/-! # Actual finite row coordinate unitaries

Reindexing and splitting a finite sum preserve the full coefficient-valued
inner product. These whole unitaries intertwine the actual forced-unitization
matrix actions, including zero coefficient algebras and empty coordinate sets.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace CStarAlgebra
open BC4lean.OperatorKTheory

variable {B ι κ : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

local instance oddContinuationOddKTheoryFiniteCoordinateEquivLocalInstance01 : CompleteSpace (FiniteStandardModule B ι) := finiteStandardModule_complete
local instance oddContinuationOddKTheoryFiniteCoordinateEquivLocalInstance02 : CompleteSpace (FiniteStandardModule B κ) := finiteStandardModule_complete
local instance oddContinuationOddKTheoryFiniteCoordinateEquivLocalInstance03 : CompleteSpace (FiniteStandardModule B (ι ⊕ κ)) := finiteStandardModule_complete
local instance oddContinuationOddKTheoryFiniteCoordinateEquivLocalInstance04 : CompleteSpace (HilbertModuleSum B (FiniteStandardModule B ι)
    (FiniteStandardModule B κ)) := hilbertModuleSum_complete

def oddKTheoryFiniteReindexLinear (e : ι ≃ κ) :
    FiniteStandardModule B ι ≃ₗ[ℂ] FiniteStandardModule B κ where
  toFun x := (WithCStarModule.equiv _ _).symm (fun i => x (e.symm i))
  invFun x := (WithCStarModule.equiv _ _).symm (fun i => x (e i))
  left_inv x := by ext i; exact congrArg x (e.symm_apply_apply i)
  right_inv x := by ext i; exact congrArg x (e.apply_symm_apply i)
  map_add' _ _ := by ext i; rfl
  map_smul' _ _ := by ext i; rfl

omit [PartialOrder B] [StarOrderedRing B] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] in
@[simp] theorem oddKTheoryFiniteReindexLinear_apply (e : ι ≃ κ)
    (x : FiniteStandardModule B ι) (i : κ) :
    oddKTheoryFiniteReindexLinear e x i = x (e.symm i) := rfl

omit [DecidableEq ι] [DecidableEq κ] in
theorem oddKTheoryFiniteReindexLinear_inner (e : ι ≃ κ)
    (x y : FiniteStandardModule B ι) :
    ⟪oddKTheoryFiniteReindexLinear e x, oddKTheoryFiniteReindexLinear e y⟫_(Bᵐᵒᵖ) =
      ⟪x, y⟫_(Bᵐᵒᵖ) := by
  change (∑ i : κ, ⟪x (e.symm i), y (e.symm i)⟫_(Bᵐᵒᵖ)) =
    ∑ i : ι, ⟪x i, y i⟫_(Bᵐᵒᵖ)
  exact e.symm.sum_comp (fun i => ⟪x i, y i⟫_(Bᵐᵒᵖ))

def oddKTheoryFiniteReindexEquiv (e : ι ≃ κ) :
    HilbertModuleEquiv B (FiniteStandardModule B ι) (FiniteStandardModule B κ) where
  linearIsometryEquiv :=
    { toLinearEquiv := oddKTheoryFiniteReindexLinear e
      norm_map' x := by
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ),
          oddKTheoryFiniteReindexLinear_inner]
        exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm }
  inner_map := oddKTheoryFiniteReindexLinear_inner e

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem oddKTheoryFiniteReindexEquiv_apply (e : ι ≃ κ)
    (x : FiniteStandardModule B ι) (i : κ) :
    oddKTheoryFiniteReindexEquiv e x i = x (e.symm i) := rfl

theorem oddKTheoryFiniteReindexEquiv_matrix (e : ι ≃ κ)
    (M : CStarMatrix ι ι (Unitization ℂ B)) (x : FiniteStandardModule B ι) :
    oddKTheoryFiniteReindexEquiv e (unitizedModuleMatrixRepresentation M x) =
      unitizedModuleMatrixRepresentation (CStarMatrix.reindexₐ ℂ (Unitization ℂ B) e M)
        (oddKTheoryFiniteReindexEquiv e x) := by
  ext i
  simp only [oddKTheoryFiniteReindexEquiv_apply, unitizedModuleMatrixRepresentation_apply]
  exact (e.symm.sum_comp (fun j => unitizedStandardLeftMul (M (e.symm i) j) (x j))).symm

def oddKTheoryFiniteSumLinear : FiniteStandardModule B (ι ⊕ κ) ≃ₗ[ℂ]
    HilbertModuleSum B (FiniteStandardModule B ι) (FiniteStandardModule B κ) where
  toFun x := sumMk ((WithCStarModule.equiv _ _).symm (fun i => x (Sum.inl i)))
    ((WithCStarModule.equiv _ _).symm (fun i => x (Sum.inr i)))
  invFun x := (WithCStarModule.equiv _ _).symm (Sum.elim x.fst x.snd)
  left_inv x := by ext i; cases i <;> rfl
  right_inv x := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [PartialOrder B] [StarOrderedRing B] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] in
@[simp] theorem oddKTheoryFiniteSumLinear_fst (x : FiniteStandardModule B (ι ⊕ κ)) (i : ι) :
    (oddKTheoryFiniteSumLinear x).fst i = x (Sum.inl i) := rfl
omit [PartialOrder B] [StarOrderedRing B] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] in
@[simp] theorem oddKTheoryFiniteSumLinear_snd (x : FiniteStandardModule B (ι ⊕ κ)) (i : κ) :
    (oddKTheoryFiniteSumLinear x).snd i = x (Sum.inr i) := rfl

omit [DecidableEq ι] [DecidableEq κ] in
theorem oddKTheoryFiniteSumLinear_inner (x y : FiniteStandardModule B (ι ⊕ κ)) :
    ⟪oddKTheoryFiniteSumLinear x, oddKTheoryFiniteSumLinear y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) := by
  change (∑ i : ι, ⟪x (Sum.inl i), y (Sum.inl i)⟫_(Bᵐᵒᵖ)) +
    (∑ i : κ, ⟪x (Sum.inr i), y (Sum.inr i)⟫_(Bᵐᵒᵖ)) =
    ∑ i : ι ⊕ κ, ⟪x i, y i⟫_(Bᵐᵒᵖ)
  exact (Fintype.sum_sum_type (fun i : ι ⊕ κ => ⟪x i, y i⟫_(Bᵐᵒᵖ))).symm

def oddKTheoryFiniteSumEquiv : HilbertModuleEquiv B (FiniteStandardModule B (ι ⊕ κ))
    (HilbertModuleSum B (FiniteStandardModule B ι) (FiniteStandardModule B κ)) where
  linearIsometryEquiv :=
    { toLinearEquiv := oddKTheoryFiniteSumLinear
      norm_map' x := by
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ), oddKTheoryFiniteSumLinear_inner]
        exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm }
  inner_map := oddKTheoryFiniteSumLinear_inner

theorem oddKTheoryFiniteSumEquiv_matrix
    (M : CStarMatrix ι ι (Unitization ℂ B)) (N : CStarMatrix κ κ (Unitization ℂ B))
    (x : FiniteStandardModule B (ι ⊕ κ)) :
    oddKTheoryFiniteSumEquiv (unitizedModuleMatrixRepresentation (matrixBlockSum M N) x) =
      sumMap (unitizedModuleMatrixRepresentation M) (unitizedModuleMatrixRepresentation N)
        (oddKTheoryFiniteSumEquiv x) := by
  rw [sumMap_apply]
  apply (WithCStarModule.equiv _ _).injective
  apply Prod.ext
  · ext i
    change unitizedModuleMatrixRepresentation (matrixBlockSum M N) x (Sum.inl i) =
      unitizedModuleMatrixRepresentation M
        ((WithCStarModule.equiv Bᵐᵒᵖ (ι → Bᵐᵒᵖ)).symm
          (fun j : ι => x (Sum.inl j))) i
    rw [unitizedModuleMatrixRepresentation_apply, unitizedModuleMatrixRepresentation_apply]
    change (∑ j : ι ⊕ κ,
      unitizedStandardLeftMul (matrixBlockSum M N (Sum.inl i) j) (x j)) =
      ∑ j : ι, unitizedStandardLeftMul (M i j) (x (Sum.inl j))
    rw [Fintype.sum_sum_type]
    change (∑ j : ι, unitizedStandardLeftMul (M i j) (x (Sum.inl j))) +
      (∑ j : κ, unitizedStandardLeftMul (0 : Unitization ℂ B) (x (Sum.inr j))) =
      ∑ j : ι, unitizedStandardLeftMul (M i j) (x (Sum.inl j))
    simp only [map_zero, AdjointableMap.coe_zero_apply, Finset.sum_const_zero, add_zero]
  · ext i
    change unitizedModuleMatrixRepresentation (matrixBlockSum M N) x (Sum.inr i) =
      unitizedModuleMatrixRepresentation N
        ((WithCStarModule.equiv Bᵐᵒᵖ (κ → Bᵐᵒᵖ)).symm
          (fun j : κ => x (Sum.inr j))) i
    rw [unitizedModuleMatrixRepresentation_apply, unitizedModuleMatrixRepresentation_apply]
    change (∑ j : ι ⊕ κ,
      unitizedStandardLeftMul (matrixBlockSum M N (Sum.inr i) j) (x j)) =
      ∑ j : κ, unitizedStandardLeftMul (N i j) (x (Sum.inr j))
    rw [Fintype.sum_sum_type]
    change (∑ j : ι, unitizedStandardLeftMul (0 : Unitization ℂ B) (x (Sum.inl j))) +
      (∑ j : κ, unitizedStandardLeftMul (N i j) (x (Sum.inr j))) =
      ∑ j : κ, unitizedStandardLeftMul (N i j) (x (Sum.inr j))
    simp only [map_zero, AdjointableMap.coe_zero_apply, Finset.sum_const_zero, zero_add]

end BC4lean.KKTheory
