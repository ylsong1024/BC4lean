import BC4lean.MatrixStabilization
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Connected.PathConnected

/-! # Norm homotopy of matrix unitaries

These are path components at a fixed matrix size, not yet the stable group K₁.
The topology is the subspace topology of Mathlib's operator-norm C⋆-matrices.
-/

noncomputable section
namespace BC4lean.OperatorKTheory

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A norm-continuous path of matrix unitaries joins the two endpoints. -/
def UnitaryHomotopic (u v : MatrixUnitary A ι) : Prop := Joined u v

theorem unitaryHomotopic_refl (u : MatrixUnitary A ι) : UnitaryHomotopic u u :=
  Joined.refl u

theorem unitaryHomotopic_symm {u v : MatrixUnitary A ι} (h : UnitaryHomotopic u v) :
    UnitaryHomotopic v u := Joined.symm h

theorem unitaryHomotopic_trans {u v w : MatrixUnitary A ι}
    (h : UnitaryHomotopic u v) (k : UnitaryHomotopic v w) : UnitaryHomotopic u w :=
  Joined.trans h k

theorem unitaryHomotopic_mul {u v w z : MatrixUnitary A ι}
    (h : UnitaryHomotopic u v) (k : UnitaryHomotopic w z) :
    UnitaryHomotopic (u * w) (v * z) := Joined.mul h k

theorem unitaryHomotopic_inv {u v : MatrixUnitary A ι} (h : UnitaryHomotopic u v) :
    UnitaryHomotopic u⁻¹ v⁻¹ := Joined.inv h

/-- Fixed-size norm-path components of the unitary group. -/
abbrev UnitaryHomotopyClasses (A : Type*) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  Quotient (pathSetoid (MatrixUnitary A ι))

omit [PartialOrder A] [StarOrderedRing A] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] in
theorem continuous_matrixBlockSum :
    Continuous (fun x : CStarMatrix ι ι A × CStarMatrix κ κ A =>
      matrixBlockSum x.1 x.2) := by
  exact CStarMatrix.ofMatrixL.continuous.comp
    ((CStarMatrix.ofMatrixL.symm.continuous.comp continuous_fst).matrix_fromBlocks
      continuous_const continuous_const
      (CStarMatrix.ofMatrixL.symm.continuous.comp continuous_snd))

theorem continuous_unitaryBlockSum :
    Continuous (fun x : MatrixUnitary A ι × MatrixUnitary A κ =>
      unitaryBlockSum x.1 x.2) := by
  apply Continuous.subtype_mk
  exact continuous_matrixBlockSum.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))

theorem unitaryHomotopic_blockSum {u v : MatrixUnitary A ι} {w z : MatrixUnitary A κ}
    (h : UnitaryHomotopic u v) (k : UnitaryHomotopic w z) :
    UnitaryHomotopic (unitaryBlockSum u w) (unitaryBlockSum v z) := by
  exact (Joined.prod h k).map
    continuous_unitaryBlockSum

theorem unitaryHomotopic_stabilize {u v : MatrixUnitary A ι}
    (h : UnitaryHomotopic u v) :
    UnitaryHomotopic (stabilizeUnitary (κ := κ) u) (stabilizeUnitary v) :=
  unitaryHomotopic_blockSum h (unitaryHomotopic_refl 1)

/-- Stabilization is well-defined on norm-path components at each size. -/
def stabilizeUnitaryClasses : UnitaryHomotopyClasses A ι →
    UnitaryHomotopyClasses A (ι ⊕ κ) :=
  Quotient.map stabilizeUnitary (fun _ _ h => unitaryHomotopic_stabilize h)

end BC4lean.OperatorKTheory
