import BC4lean.OperatorK0Functoriality
import BC4lean.UnitizedFiniteModuleOperator
import BC4lean.HilbertModuleEquiv

/-! # Genuine finite matrix coordinates across index universes

An arbitrary finite index type is reindexed to its canonical finite ordinal.
The actual matrix star equivalence and the whole coefficient-form module
unitary preserve matrix actions and coefficient maps. The existing K₀
constructor is used only on that finite ordinal; its Type-0 implementation
is unchanged, and on Type-0 inputs this gives the same stable K₀ class.
-/

noncomputable section
namespace BC4lean.OperatorKTheory

variable {A D ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Fintype ι] [DecidableEq ι]

/-- The canonical finite ordinal presentation is an actual matrix star equivalence. -/
def matrixProjectionToFin (p : MatrixProjection A ι) :
    MatrixProjection A (Fin (Fintype.card ι)) :=
  Projection.map (CStarMatrix.reindexₐ ℂ A (Fintype.equivFin ι)).toStarAlgHom p

/-- Record a projection from any index universe through its genuine finite reindexing. -/
def finiteProjectionOfMatrix (p : MatrixProjection A ι) : FiniteProjection A :=
  FiniteProjection.ofProjection (matrixProjectionToFin p)

/-- Entrywise coefficient maps commute with the actual finite reindexing. -/
theorem matrixProjectionToFin_map (φ : A →⋆ₐ[ℂ] D) (p : MatrixProjection A ι) :
    matrixProjectionToFin (matrixProjectionMap φ p) =
      matrixProjectionMap φ (matrixProjectionToFin p) := by
  apply Subtype.ext
  ext i j
  rfl

/-- The finite projection presentation preserves the actual coefficient homomorphism. -/
theorem finiteProjectionOfMatrix_map (φ : A →⋆ₐ[ℂ] D) (p : MatrixProjection A ι) :
    FiniteProjection.map φ (finiteProjectionOfMatrix p) =
      finiteProjectionOfMatrix (matrixProjectionMap φ p) := by
  change FiniteProjection.ofProjection (matrixProjectionMap φ (matrixProjectionToFin p)) =
    FiniteProjection.ofProjection (matrixProjectionToFin (matrixProjectionMap φ p))
  exact congrArg FiniteProjection.ofProjection (matrixProjectionToFin_map φ p).symm

/-- On the constructor's original index universe, reindexing leaves its K₀ class unchanged. -/
@[simp] theorem k0Projection_finiteProjectionOfMatrix {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : MatrixProjection A ι) :
    k0Projection (finiteProjectionOfMatrix p) = k0Projection (FiniteProjection.ofProjection p) := by
  change k0Projection (FiniteProjection.ofProjection p).toFin =
    k0Projection (FiniteProjection.ofProjection p)
  exact (k0Projection_eq_of_equivalent
    (FiniteProjection.equivalent_toFin (FiniteProjection.ofProjection p))).symm

end BC4lean.OperatorKTheory

namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B ι κ : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The actual coordinate permutation, with its pointwise linear inverse. -/
def finiteMatrixIndexLinearEquiv (e : ι ≃ κ) :
    FiniteStandardModule B ι ≃ₗ[ℂ] FiniteStandardModule B κ where
  toFun x := (WithCStarModule.equiv _ _).symm (fun i => x (e.symm i))
  invFun x := (WithCStarModule.equiv _ _).symm (fun i => x (e i))
  left_inv x := by ext i; exact congrArg x (e.symm_apply_apply i)
  right_inv x := by ext i; exact congrArg x (e.apply_symm_apply i)
  map_add' _ _ := by ext i; rfl
  map_smul' _ _ := by ext i; rfl

omit [PartialOrder B] [StarOrderedRing B] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] in
@[simp] theorem finiteMatrixIndexLinearEquiv_apply (e : ι ≃ κ)
    (x : FiniteStandardModule B ι) (i : κ) :
    finiteMatrixIndexLinearEquiv e x i = x (e.symm i) := rfl

omit [DecidableEq ι] [DecidableEq κ] in
/-- Coordinate permutation preserves the whole coefficient-valued form. -/
theorem finiteMatrixIndexLinearEquiv_inner (e : ι ≃ κ)
    (x y : FiniteStandardModule B ι) :
    ⟪finiteMatrixIndexLinearEquiv e x, finiteMatrixIndexLinearEquiv e y⟫_(Bᵐᵒᵖ) =
      ⟪x, y⟫_(Bᵐᵒᵖ) := by
  change (∑ i : κ, ⟪x (e.symm i), y (e.symm i)⟫_(Bᵐᵒᵖ)) =
    ∑ i : ι, ⟪x i, y i⟫_(Bᵐᵒᵖ)
  exact e.symm.sum_comp (fun i => ⟪x i, y i⟫_(Bᵐᵒᵖ))

/-- The reindexing is a whole Hilbert-module unitary, across independent index universes. -/
def finiteMatrixIndexHilbertEquiv (e : ι ≃ κ) :
    HilbertModuleEquiv B (FiniteStandardModule B ι) (FiniteStandardModule B κ) where
  linearIsometryEquiv :=
    { toLinearEquiv := finiteMatrixIndexLinearEquiv e
      norm_map' x := by
        change ‖finiteMatrixIndexLinearEquiv e x‖ = ‖x‖
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ),
          finiteMatrixIndexLinearEquiv_inner]
        exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm }
  inner_map := finiteMatrixIndexLinearEquiv_inner e

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem finiteMatrixIndexHilbertEquiv_apply (e : ι ≃ κ)
    (x : FiniteStandardModule B ι) (i : κ) :
    finiteMatrixIndexHilbertEquiv e x i = x (e.symm i) := rfl

/-- The actual unitary intertwines forced-unitization matrix actions, including degenerate coefficients. -/
theorem finiteMatrixIndexHilbertEquiv_matrix (e : ι ≃ κ)
    (M : CStarMatrix ι ι (Unitization ℂ B)) (x : FiniteStandardModule B ι) :
    finiteMatrixIndexHilbertEquiv e (unitizedModuleMatrixRepresentation M x) =
      unitizedModuleMatrixRepresentation (CStarMatrix.reindexₐ ℂ (Unitization ℂ B) e M)
        (finiteMatrixIndexHilbertEquiv e x) := by
  ext i
  simp only [finiteMatrixIndexHilbertEquiv_apply, unitizedModuleMatrixRepresentation_apply]
  exact (e.symm.sum_comp (fun j => unitizedStandardLeftMul (M (e.symm i) j) (x j))).symm

end BC4lean.KKTheory
