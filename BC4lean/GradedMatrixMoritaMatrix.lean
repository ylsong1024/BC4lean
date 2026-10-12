import BC4lean.GradedHilbertModule
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel

/-! # The actual graded two-by-two matrix coefficient algebra

The grading is conjugation by diag(1,-1) expressed entrywise. This formula
also works over a nonunital B: its scalar signs are complex multipliers and
do not insert a nonexistent identity coefficient into B.
-/

noncomputable section
namespace BC4lean.KKTheory

abbrev GradedMatrixMoritaMatrix (B : Type*) := CStarMatrix (Fin 2) (Fin 2) B

namespace GradedMatrixMoritaMatrix

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def parity (M : GradedMatrixMoritaMatrix B) : GradedMatrixMoritaMatrix B :=
  CStarMatrix.ofMatrix !![M 0 0, -M 0 1; -M 1 0, M 1 1]

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem parity_zero : parity (0 : GradedMatrixMoritaMatrix B) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [parity]

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem parity_add (M N : GradedMatrixMoritaMatrix B) :
    parity (M + N) = parity M + parity N := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [parity, add_comm]

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem parity_smul (c : ℂ) (M : GradedMatrixMoritaMatrix B) :
    parity (c • M) = c • parity M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [parity]

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem parity_star (M : GradedMatrixMoritaMatrix B) :
    parity (star M) = star (parity M) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [parity, CStarMatrix.star_apply]

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem parity_mul (M N : GradedMatrixMoritaMatrix B) :
    parity (M * N) = parity M * parity N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parity, CStarMatrix.mul_apply, Fin.sum_univ_two] <;> abel

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem parity_parity (M : GradedMatrixMoritaMatrix B) : parity (parity M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [parity]

def parityEquiv : GradedMatrixMoritaMatrix B ≃⋆ₐ[ℂ] GradedMatrixMoritaMatrix B where
  toFun := parity
  invFun := parity
  left_inv := parity_parity
  right_inv := parity_parity
  map_add' := parity_add
  map_mul' := parity_mul
  map_smul' := parity_smul
  map_star' := parity_star

def grading : CStarGrading (GradedMatrixMoritaMatrix B) where
  automorphism := parityEquiv
  involutive := parity_parity

/-- The top-left corner inclusion is an actual nonunital star homomorphism. -/
def corner (b : B) : GradedMatrixMoritaMatrix B :=
  CStarMatrix.ofMatrix !![b, 0; 0, 0]

def cornerHom : B →⋆ₙₐ[ℂ] GradedMatrixMoritaMatrix B where
  toFun := corner
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp [corner]
  map_add' b c := by ext i j; fin_cases i <;> fin_cases j <;> simp [corner]
  map_smul' c b := by ext i j; fin_cases i <;> fin_cases j <;> simp [corner]
  map_mul' b c := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [corner, CStarMatrix.mul_apply, Fin.sum_univ_two]
  map_star' b := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [corner, CStarMatrix.star_apply]

omit [PartialOrder B] [StarOrderedRing B] in
theorem cornerHom_injective : Function.Injective (cornerHom (B := B)) := by
  intro b c h
  exact congrArg (fun M : GradedMatrixMoritaMatrix B => M 0 0) h

theorem cornerHom_isometry : Isometry (cornerHom (B := B)) :=
  NonUnitalStarAlgHom.isometry _ cornerHom_injective

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem parity_corner (b : B) : parity (corner b) = corner b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [parity, corner]

end GradedMatrixMoritaMatrix
end BC4lean.KKTheory
