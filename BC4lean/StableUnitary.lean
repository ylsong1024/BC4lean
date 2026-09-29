import BC4lean.UnitaryRotation
import BC4lean.MatrixProjectionMap
import Mathlib.Logic.Relation

/-! # Stable norm-homotopy of finite matrix unitaries

The generators are actual norm homotopies (after a change of finite coordinates)
and adjoining identity blocks. No additive or inverse relations are imposed.
-/
noncomputable section
namespace BC4lean.OperatorKTheory
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι κ ρ σ : Type} [Fintype ι] [Fintype κ] [Fintype ρ] [Fintype σ]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ] [DecidableEq σ]

def unitaryReindex (e : ι ≃ κ) (a : MatrixUnitary A ι) : MatrixUnitary A κ :=
  ⟨CStarMatrix.reindexₐ ℂ A e a, Unitary.map_mem (CStarMatrix.reindexₐ ℂ A e) a.property⟩

@[simp] theorem unitaryReindex_apply (e : ι ≃ κ) (a : MatrixUnitary A ι) (i j : κ) :
    (unitaryReindex e a : CStarMatrix κ κ A) i j = (a : CStarMatrix ι ι A) (e.symm i) (e.symm j) := rfl

@[simp] theorem unitaryReindex_refl (a : MatrixUnitary A ι) :
    unitaryReindex (Equiv.refl ι) a = a := by apply Subtype.ext; rfl

@[simp] theorem unitaryReindex_star (e : ι ≃ κ) (a : MatrixUnitary A ι) :
    unitaryReindex e (star a) = star (unitaryReindex e a) := by
  apply Subtype.ext
  exact map_star (CStarMatrix.reindexₐ ℂ A e) (a : CStarMatrix ι ι A)

theorem unitaryReindex_blockSum (e : ι ≃ κ) (f : ρ ≃ σ)
    (a : MatrixUnitary A ι) (b : MatrixUnitary A ρ) :
    unitaryReindex (e.sumCongr f) (unitaryBlockSum a b) =
      unitaryBlockSum (unitaryReindex e a) (unitaryReindex f b) := by
  apply Subtype.ext
  ext i j
  cases i <;> cases j <;> rfl

@[simp] theorem unitaryBlockSum_star (a : MatrixUnitary A ι) (b : MatrixUnitary A κ) :
    star (unitaryBlockSum a b) = unitaryBlockSum (star a) (star b) := by
  apply Subtype.ext
  exact matrixBlockSum_star (a : CStarMatrix ι ι A) (b : CStarMatrix κ κ A)

structure FiniteUnitary (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] where
  Index : Type
  [indexFintype : Fintype Index]
  [indexDecidableEq : DecidableEq Index]
  val : MatrixUnitary A Index
attribute [instance] FiniteUnitary.indexFintype FiniteUnitary.indexDecidableEq

namespace FiniteUnitary

abbrev ofUnitary (a : MatrixUnitary A ι) : FiniteUnitary A := ⟨ι, a⟩
abbrev identity (ι : Type) [Fintype ι] [DecidableEq ι] : FiniteUnitary A := ofUnitary (1 : MatrixUnitary A ι)
abbrev zero : FiniteUnitary A := identity Empty

abbrev blockSum (a b : FiniteUnitary A) : FiniteUnitary A :=
  ofUnitary (unitaryBlockSum a.val b.val)

abbrev adjoint (a : FiniteUnitary A) : FiniteUnitary A := ofUnitary (star a.val)

/-- The geometric moves defining the stable quotient. -/
inductive Move : FiniteUnitary A → FiniteUnitary A → Prop
  | homotopy (a b : FiniteUnitary A) (e : a.Index ≃ b.Index)
      (h : UnitaryHomotopic (unitaryReindex e a.val) b.val) : Move a b
  | stabilize (a : FiniteUnitary A) (κ : Type) [Fintype κ] [DecidableEq κ] :
      Move a (blockSum a (identity κ))

/-- A finite chain of coordinate changes, norm homotopies, and identity stabilizations. -/
def Equivalent : FiniteUnitary A → FiniteUnitary A → Prop := Relation.EqvGen Move

theorem equivalent_refl (a : FiniteUnitary A) : Equivalent a a := .refl _
theorem equivalent_symm {a b : FiniteUnitary A} (h : Equivalent a b) : Equivalent b a := .symm _ _ h
theorem equivalent_trans {a b c : FiniteUnitary A} (h : Equivalent a b) (k : Equivalent b c) :
    Equivalent a c := .trans _ _ _ h k

theorem equivalent_reindex (a b : FiniteUnitary A) (e : a.Index ≃ b.Index)
    (h : unitaryReindex e a.val = b.val) : Equivalent a b :=
  .rel _ _ (.homotopy a b e (h ▸ unitaryHomotopic_refl _))

theorem equivalent_homotopy {a b : MatrixUnitary A ι} (h : UnitaryHomotopic a b) :
    Equivalent (ofUnitary a) (ofUnitary b) :=
  .rel _ _ (.homotopy _ _ (Equiv.refl ι) (by
    change UnitaryHomotopic (unitaryReindex (Equiv.refl ι) a) b
    simpa only [unitaryReindex_refl] using h))

theorem equivalent_stabilize (a : FiniteUnitary A) (κ : Type) [Fintype κ] [DecidableEq κ] :
    Equivalent a (blockSum a (identity κ)) := .rel _ _ (.stabilize a κ)

theorem blockSum_comm (a b : FiniteUnitary A) : Equivalent (blockSum a b) (blockSum b a) := by
  apply equivalent_reindex _ _ (Equiv.sumComm a.Index b.Index)
  apply Subtype.ext
  ext i j
  cases i <;> cases j <;> rfl

theorem blockSum_assoc (a b c : FiniteUnitary A) :
    Equivalent (blockSum (blockSum a b) c) (blockSum a (blockSum b c)) := by
  apply equivalent_reindex _ _ (Equiv.sumAssoc a.Index b.Index c.Index)
  apply Subtype.ext
  ext i j
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;> rfl

theorem zero_blockSum (a : FiniteUnitary A) : Equivalent (blockSum zero a) a := by
  apply equivalent_reindex _ _ (Equiv.emptySum Empty a.Index)
  apply Subtype.ext
  ext i j
  rfl

theorem blockSum_zero (a : FiniteUnitary A) : Equivalent (blockSum a zero) a :=
  equivalent_trans (blockSum_comm a zero) (zero_blockSum a)

/-- Compatibility with a block context is derived from the geometric moves. -/
theorem blockSum_right {a b : FiniteUnitary A} (h : Equivalent a b) (c : FiniteUnitary A) :
    Equivalent (blockSum a c) (blockSum b c) := by
  induction h with
  | refl a => exact equivalent_refl _
  | symm a b h ih => exact equivalent_symm ih
  | trans a b d h k ih ik => exact equivalent_trans ih ik
  | rel a b h =>
    cases h with
    | homotopy b e h =>
      apply Relation.EqvGen.rel
      apply Move.homotopy _ _ (e.sumCongr (Equiv.refl c.Index))
      simpa only [blockSum, ofUnitary, unitaryReindex_blockSum, unitaryReindex_refl] using
        unitaryHomotopic_blockSum h (unitaryHomotopic_refl c.val)
    | stabilize κ =>
      -- Move the new identity block past the fixed context by finite reindexing.
      apply equivalent_trans (equivalent_stabilize (blockSum a c) κ)
      apply equivalent_reindex _ _
        (((Equiv.sumAssoc a.Index c.Index κ).trans
          ((Equiv.refl a.Index).sumCongr (Equiv.sumComm c.Index κ))).trans
          (Equiv.sumAssoc a.Index κ c.Index).symm)
      apply Subtype.ext
      ext i j
      rcases i with (i | i) | i <;> rcases j with (j | j) | j <;> rfl

theorem blockSum_congr {a b c d : FiniteUnitary A}
    (h : Equivalent a b) (k : Equivalent c d) : Equivalent (blockSum a c) (blockSum b d) :=
  equivalent_trans (blockSum_right h c)
    (equivalent_trans (blockSum_comm b c)
      (equivalent_trans (blockSum_right k b) (blockSum_comm d b)))

theorem adjoint_congr {a b : FiniteUnitary A} (h : Equivalent a b) :
    Equivalent (adjoint a) (adjoint b) := by
  induction h with
  | refl a => exact equivalent_refl _
  | symm a b h ih => exact equivalent_symm ih
  | trans a b c h k ih ik => exact equivalent_trans ih ik
  | rel a b h =>
    cases h with
    | homotopy b e h =>
      apply Relation.EqvGen.rel
      apply Move.homotopy (adjoint a) (adjoint b) e
      change UnitaryHomotopic (unitaryReindex e (star a.val)) (star b.val)
      rw [unitaryReindex_star]
      exact unitaryHomotopic_inv h
    | stabilize κ =>
      have eq : adjoint (blockSum a (identity κ)) = blockSum (adjoint a) (identity κ) := by
        change ofUnitary (star (unitaryBlockSum a.val 1)) = ofUnitary (unitaryBlockSum (star a.val) 1)
        rw [unitaryBlockSum_star, star_one]
      rw [eq]
      exact equivalent_stabilize (adjoint a) κ

theorem equivalent_identity (ι : Type) [Fintype ι] [DecidableEq ι] :
    Equivalent (identity (A := A) ι) zero :=
  equivalent_symm (equivalent_trans (equivalent_stabilize zero ι) (zero_blockSum (identity ι)))

theorem adjoint_blockSum (a : FiniteUnitary A) : Equivalent (blockSum (adjoint a) a) zero :=
  equivalent_trans (equivalent_homotopy (unitaryHomotopic_star_blockSum a.val))
    (equivalent_identity (a.Index ⊕ a.Index))

def setoid : Setoid (FiniteUnitary A) := Relation.EqvGen.setoid Move

end FiniteUnitary

/-- The stable unitary norm-homotopy quotient, with arbitrary finite coordinates. -/
abbrev K1 (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :=
  Quotient (FiniteUnitary.setoid (A := A))

namespace K1

def of (a : FiniteUnitary A) : K1 A := Quotient.mk _ a
instance : Zero (K1 A) := ⟨of FiniteUnitary.zero⟩
instance : Add (K1 A) := ⟨Quotient.map₂ FiniteUnitary.blockSum
  (fun _ _ h _ _ k => FiniteUnitary.blockSum_congr h k)⟩
instance : Neg (K1 A) := ⟨Quotient.map FiniteUnitary.adjoint (fun _ _ h => FiniteUnitary.adjoint_congr h)⟩

@[simp] theorem of_blockSum (a b : FiniteUnitary A) : of (FiniteUnitary.blockSum a b) = of a + of b := rfl
@[simp] theorem of_adjoint (a : FiniteUnitary A) : of (FiniteUnitary.adjoint a) = -of a := rfl

theorem of_eq_iff (a b : FiniteUnitary A) : of a = of b ↔ FiniteUnitary.Equivalent a b := Quotient.eq

instance instAddCommGroup : AddCommGroup (K1 A) where
  add_assoc a b c := Quotient.inductionOn₃ a b c fun a b c => Quotient.sound (FiniteUnitary.blockSum_assoc a b c)
  zero_add a := Quotient.inductionOn a fun a => Quotient.sound (FiniteUnitary.zero_blockSum a)
  add_zero a := Quotient.inductionOn a fun a => Quotient.sound (FiniteUnitary.blockSum_zero a)
  add_comm a b := Quotient.inductionOn₂ a b fun a b => Quotient.sound (FiniteUnitary.blockSum_comm a b)
  neg_add_cancel a := Quotient.inductionOn a fun a => Quotient.sound (FiniteUnitary.adjoint_blockSum a)
  nsmul := nsmulRec
  zsmul := zsmulRec

@[simp] theorem of_identity (ι : Type) [Fintype ι] [DecidableEq ι] :
    of (FiniteUnitary.identity (A := A) ι) = 0 := Quotient.sound (FiniteUnitary.equivalent_identity ι)

theorem of_homotopic {a b : MatrixUnitary A ι} (h : UnitaryHomotopic a b) :
    of (FiniteUnitary.ofUnitary a) = of (FiniteUnitary.ofUnitary b) :=
  Quotient.sound (FiniteUnitary.equivalent_homotopy h)

theorem of_stabilize (a : FiniteUnitary A) (κ : Type) [Fintype κ] [DecidableEq κ] :
    of (FiniteUnitary.blockSum a (FiniteUnitary.identity κ)) = of a :=
  Quotient.sound (FiniteUnitary.equivalent_symm (FiniteUnitary.equivalent_stabilize a κ))

end K1
/-- Every stable unitary class has an ordinary finite-matrix representative. -/
theorem K1.exists_finRepresentative (x : K1 A) :
    ∃ (n : ℕ) (a : MatrixUnitary A (Fin n)), K1.of (FiniteUnitary.ofUnitary a) = x := by
  refine Quotient.inductionOn x ?_
  intro a
  let e := Fintype.equivFin a.Index
  refine ⟨Fintype.card a.Index, unitaryReindex e a.val, ?_⟩
  exact Quotient.sound (FiniteUnitary.equivalent_symm
    (FiniteUnitary.equivalent_reindex a (FiniteUnitary.ofUnitary (unitaryReindex e a.val)) e rfl))

end BC4lean.OperatorKTheory
