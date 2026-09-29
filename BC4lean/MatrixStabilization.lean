import BC4lean.OperatorProjections
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.Star.Unitary

/-! # Matrix projections, unitaries, and stabilization

We use Mathlib's C⋆-matrix norm, not the entrywise supremum norm. The order
assumptions are the standard compatible C⋆-order required by that API.
Block sums first use sum-indexed matrices, avoiding arbitrary index choices.
-/

noncomputable section
namespace BC4lean.OperatorKTheory

open scoped Matrix

variable {A : Type*} [CStarAlgebra A]
variable {ι κ : Type*}

/-- Block diagonal sum of C⋆-matrices. -/
def matrixBlockSum (p : CStarMatrix ι ι A) (q : CStarMatrix κ κ A) :
    CStarMatrix (ι ⊕ κ) (ι ⊕ κ) A :=
  CStarMatrix.ofMatrix (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm p) 0 0
    (CStarMatrix.ofMatrix.symm q))

@[simp] theorem matrixBlockSum_star (p : CStarMatrix ι ι A) (q : CStarMatrix κ κ A) :
    star (matrixBlockSum p q) = matrixBlockSum (star p) (star q) := by
  change (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm p) (0 : Matrix ι κ A)
    (0 : Matrix κ ι A) (CStarMatrix.ofMatrix.symm q))ᴴ = _
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero]
  rfl

theorem matrixBlockSum_mul [Fintype ι] [Fintype κ] (p r : CStarMatrix ι ι A) (q s : CStarMatrix κ κ A) :
    matrixBlockSum p q * matrixBlockSum r s = matrixBlockSum (p * r) (q * s) := by
  change Matrix.fromBlocks (CStarMatrix.ofMatrix.symm p) (0 : Matrix ι κ A)
    (0 : Matrix κ ι A) (CStarMatrix.ofMatrix.symm q) *
    Matrix.fromBlocks (CStarMatrix.ofMatrix.symm r) (0 : Matrix ι κ A)
    (0 : Matrix κ ι A) (CStarMatrix.ofMatrix.symm s) =
    Matrix.fromBlocks (CStarMatrix.ofMatrix.symm p * CStarMatrix.ofMatrix.symm r)
      (0 : Matrix ι κ A) (0 : Matrix κ ι A)
      (CStarMatrix.ofMatrix.symm q * CStarMatrix.ofMatrix.symm s)
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

@[simp] theorem matrixBlockSum_one [DecidableEq ι] [DecidableEq κ] :
    matrixBlockSum (1 : CStarMatrix ι ι A) (1 : CStarMatrix κ κ A) = 1 :=
  Matrix.fromBlocks_one

@[simp] theorem matrixBlockSum_zero :
    matrixBlockSum (0 : CStarMatrix ι ι A) (0 : CStarMatrix κ κ A) = 0 :=
  Matrix.fromBlocks_zero

variable [PartialOrder A] [StarOrderedRing A]
variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A matrix projection with the C⋆-matrix norm. -/
abbrev MatrixProjection (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (ι : Type*) [Fintype ι] [DecidableEq ι] := Projection (CStarMatrix ι ι A)

def projectionBlockSum (p : MatrixProjection A ι) (q : MatrixProjection A κ) :
    MatrixProjection A (ι ⊕ κ) :=
  ⟨matrixBlockSum p q, ⟨by
    change matrixBlockSum p.val q.val * matrixBlockSum p.val q.val = matrixBlockSum p.val q.val
    rw [matrixBlockSum_mul]; simp, by
    change star (matrixBlockSum p.val q.val) = matrixBlockSum p.val q.val
    rw [matrixBlockSum_star]; simp⟩⟩

@[simp] theorem projectionBlockSum_coe (p : MatrixProjection A ι) (q : MatrixProjection A κ) :
    (projectionBlockSum p q : CStarMatrix (ι ⊕ κ) (ι ⊕ κ) A) = matrixBlockSum p q := rfl

/-- Projection stabilization adds a zero block. -/
def stabilizeProjection (p : MatrixProjection A ι) : MatrixProjection A (ι ⊕ κ) :=
  projectionBlockSum p Projection.zero

theorem equivalent_blockSum {p r : MatrixProjection A ι} {q s : MatrixProjection A κ}
    (h : Projection.Equivalent p r) (k : Projection.Equivalent q s) :
    Projection.Equivalent (projectionBlockSum p q) (projectionBlockSum r s) := by
  obtain ⟨v, hv, hv'⟩ := h
  obtain ⟨w, hw, hw'⟩ := k
  refine ⟨matrixBlockSum v w, ?_, ?_⟩
  · simp only [matrixBlockSum_star, matrixBlockSum_mul, hv, hw, projectionBlockSum_coe]
  · simp only [matrixBlockSum_star, matrixBlockSum_mul, hv', hw', projectionBlockSum_coe]

theorem equivalent_stabilize {p q : MatrixProjection A ι} (h : Projection.Equivalent p q) :
    Projection.Equivalent (stabilizeProjection (κ := κ) p) (stabilizeProjection q) :=
  equivalent_blockSum h (Projection.equivalent_refl Projection.zero)

/-- Block sum descends to Murray–von Neumann classes at the indicated matrix sizes. -/
def blockSumClasses : Projection.Classes (CStarMatrix ι ι A) →
    Projection.Classes (CStarMatrix κ κ A) →
    Projection.Classes (CStarMatrix (ι ⊕ κ) (ι ⊕ κ) A) :=
  Quotient.map₂ projectionBlockSum (fun _ _ h _ _ k => equivalent_blockSum h k)

/-- A matrix unitary with the operator-norm topology. -/
abbrev MatrixUnitary (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (ι : Type*) [Fintype ι] [DecidableEq ι] := unitary (CStarMatrix ι ι A)

def unitaryBlockSum (u : MatrixUnitary A ι) (v : MatrixUnitary A κ) :
    MatrixUnitary A (ι ⊕ κ) :=
  ⟨matrixBlockSum u v, by
    rw [Unitary.mem_iff]
    constructor
    · rw [matrixBlockSum_star, matrixBlockSum_mul,
        Unitary.star_mul_self_of_mem u.property, Unitary.star_mul_self_of_mem v.property,
        matrixBlockSum_one]
    · rw [matrixBlockSum_star, matrixBlockSum_mul,
        Unitary.mul_star_self_of_mem u.property, Unitary.mul_star_self_of_mem v.property,
        matrixBlockSum_one]⟩

@[simp] theorem unitaryBlockSum_coe (u : MatrixUnitary A ι) (v : MatrixUnitary A κ) :
    (unitaryBlockSum u v : CStarMatrix (ι ⊕ κ) (ι ⊕ κ) A) = matrixBlockSum u v := rfl

/-- Unitary stabilization adds an identity block, unlike projection stabilization. -/
def stabilizeUnitary (u : MatrixUnitary A ι) : MatrixUnitary A (ι ⊕ κ) :=
  unitaryBlockSum u 1

end BC4lean.OperatorKTheory
