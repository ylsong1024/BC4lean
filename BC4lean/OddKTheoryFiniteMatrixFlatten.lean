import BC4lean.OperatorK1Functoriality
import Mathlib.Topology.Algebra.Star.Unitary

/-! # Actual flattening of two by two finite C-star matrix blocks

The block entry formula is bundled as a unital star algebra homomorphism.
It therefore carries genuine nested matrix unitaries and their norm paths
to the actual sum-indexed finite matrix algebra used by `OperatorK1`.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped Matrix CStarAlgebra

variable {A ι : Type*} [CStarAlgebra A] [Fintype ι] [DecidableEq ι]

def oddKTheoryTwoBlockFlatten
    (M : CStarMatrix (Fin 2) (Fin 2) (CStarMatrix ι ι A)) :
    CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A :=
  CStarMatrix.ofMatrix (Matrix.fromBlocks
    (CStarMatrix.ofMatrix.symm (M 0 0)) (CStarMatrix.ofMatrix.symm (M 0 1))
    (CStarMatrix.ofMatrix.symm (M 1 0)) (CStarMatrix.ofMatrix.symm (M 1 1)))

omit [CStarAlgebra A] [Fintype ι] [DecidableEq ι] in
@[simp] theorem oddKTheoryTwoBlockFlatten_inl_inl
    (M : CStarMatrix (Fin 2) (Fin 2) (CStarMatrix ι ι A)) (i j : ι) :
    oddKTheoryTwoBlockFlatten M (.inl i) (.inl j) = M 0 0 i j := rfl

omit [CStarAlgebra A] [Fintype ι] [DecidableEq ι] in
@[simp] theorem oddKTheoryTwoBlockFlatten_inl_inr
    (M : CStarMatrix (Fin 2) (Fin 2) (CStarMatrix ι ι A)) (i j : ι) :
    oddKTheoryTwoBlockFlatten M (.inl i) (.inr j) = M 0 1 i j := rfl

omit [CStarAlgebra A] [Fintype ι] [DecidableEq ι] in
@[simp] theorem oddKTheoryTwoBlockFlatten_inr_inl
    (M : CStarMatrix (Fin 2) (Fin 2) (CStarMatrix ι ι A)) (i j : ι) :
    oddKTheoryTwoBlockFlatten M (.inr i) (.inl j) = M 1 0 i j := rfl

omit [CStarAlgebra A] [Fintype ι] [DecidableEq ι] in
@[simp] theorem oddKTheoryTwoBlockFlatten_inr_inr
    (M : CStarMatrix (Fin 2) (Fin 2) (CStarMatrix ι ι A)) (i j : ι) :
    oddKTheoryTwoBlockFlatten M (.inr i) (.inr j) = M 1 1 i j := rfl

omit [DecidableEq ι] in
theorem oddKTheoryTwoBlockFlatten_mul
    (M N : CStarMatrix (Fin 2) (Fin 2) (CStarMatrix ι ι A)) :
    oddKTheoryTwoBlockFlatten (M * N) =
      oddKTheoryTwoBlockFlatten M * oddKTheoryTwoBlockFlatten N := by
  ext i j
  cases i <;> cases j <;>
    simp only [CStarMatrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      oddKTheoryTwoBlockFlatten_inl_inl, oddKTheoryTwoBlockFlatten_inl_inr,
      oddKTheoryTwoBlockFlatten_inr_inl, oddKTheoryTwoBlockFlatten_inr_inr,
      CStarMatrix.add_apply]

omit [Fintype ι] in
@[simp] theorem oddKTheoryTwoBlockFlatten_one :
    oddKTheoryTwoBlockFlatten (1 : CStarMatrix (Fin 2) (Fin 2) (CStarMatrix ι ι A)) = 1 := by
  ext i j
  cases i <;> cases j <;> simp [CStarMatrix.one_apply]

omit [Fintype ι] [DecidableEq ι] in
theorem oddKTheoryTwoBlockFlatten_smul (z : ℂ)
    (M : CStarMatrix (Fin 2) (Fin 2) (CStarMatrix ι ι A)) :
    oddKTheoryTwoBlockFlatten (z • M) = z • oddKTheoryTwoBlockFlatten M := by
  ext i j
  cases i <;> cases j <;> rfl

def oddKTheoryTwoBlockFlattenHom :
    CStarMatrix (Fin 2) (Fin 2) (CStarMatrix ι ι A) →⋆ₐ[ℂ]
      CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A where
  toFun := oddKTheoryTwoBlockFlatten
  map_one' := oddKTheoryTwoBlockFlatten_one
  map_mul' := oddKTheoryTwoBlockFlatten_mul
  map_zero' := by ext i j; cases i <;> cases j <;> rfl
  map_add' M N := by ext i j; cases i <;> cases j <;> rfl
  commutes' z := by
    rw [Algebra.algebraMap_eq_smul_one, oddKTheoryTwoBlockFlatten_smul,
      oddKTheoryTwoBlockFlatten_one, Algebra.algebraMap_eq_smul_one]
  map_star' M := by
    ext i j
    cases i <;> cases j <;> rfl

def oddKTheoryTwoBlockFlattenUnitary
    (u : unitary (CStarMatrix (Fin 2) (Fin 2) (CStarMatrix ι ι A))) :
    unitary (CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A) :=
  ⟨oddKTheoryTwoBlockFlattenHom (u : _),
    Unitary.map_mem oddKTheoryTwoBlockFlattenHom u.property⟩

local instance oddContinuationOddKTheoryFiniteMatrixFlattenLocalInstance01 :
    PartialOrder A := CStarAlgebra.spectralOrder A
local instance oddContinuationOddKTheoryFiniteMatrixFlattenLocalInstance02 :
    StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

theorem continuous_oddKTheoryTwoBlockFlattenUnitary :
    Continuous (oddKTheoryTwoBlockFlattenUnitary (A := A) (ι := ι)) :=
  ((map_continuous oddKTheoryTwoBlockFlattenHom).comp continuous_subtype_val).subtype_mk _

end BC4lean.KKTheory
