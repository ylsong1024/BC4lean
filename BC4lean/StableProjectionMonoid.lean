import BC4lean.RectangularEquivalence

/-! # The stable projection monoid

Objects are projections indexed by arbitrary small finite types. Rectangular
Murray–von Neumann witnesses make the quotient independent of the index type.
Addition is actual matrix block sum, not a freely imposed relation.
-/

noncomputable section
open scoped Matrix
namespace BC4lean.OperatorKTheory

universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A finite matrix projection, with its finite index type recorded. -/
structure FiniteProjection (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] where
  Index : Type
  [indexFintype : Fintype Index]
  [indexDecidableEq : DecidableEq Index]
  projection : MatrixProjection A Index

attribute [instance] FiniteProjection.indexFintype FiniteProjection.indexDecidableEq

namespace FiniteProjection

/-- Record the index type of a matrix projection. -/
def ofProjection {ι : Type} [Fintype ι] [DecidableEq ι] (p : MatrixProjection A ι) :
    FiniteProjection A where
  Index := ι
  projection := p

/-- Every object can be represented using a standard finite ordinal. -/
def toFin (p : FiniteProjection A) : FiniteProjection A where
  Index := Fin (Fintype.card p.Index)
  projection := Projection.map
    (CStarMatrix.reindexₐ ℂ A (Fintype.equivFin p.Index)).toStarAlgHom p.projection

/-- Block sum of finite matrix projections. -/
def blockSum (p q : FiniteProjection A) : FiniteProjection A where
  Index := p.Index ⊕ q.Index
  projection := projectionBlockSum p.projection q.projection

/-- The empty matrix represents zero. -/
def zero : FiniteProjection A where
  Index := Empty
  projection := Projection.zero

/-- Equivalence compares different sizes using a rectangular partial isometry. -/
def Equivalent (p q : FiniteProjection A) : Prop := RectEquivalent p.projection q.projection

theorem equivalent_refl (p : FiniteProjection A) : Equivalent p p :=
  rectEquivalent_refl p.projection

theorem equivalent_symm {p q : FiniteProjection A} (h : Equivalent p q) : Equivalent q p :=
  rectEquivalent_symm h

theorem equivalent_trans {p q r : FiniteProjection A}
    (h : Equivalent p q) (k : Equivalent q r) : Equivalent p r := rectEquivalent_trans h k

theorem equivalent_toFin (p : FiniteProjection A) : Equivalent p p.toFin := by
  apply rectEquivalent_of_reindex _ _ (Fintype.equivFin p.Index).symm
  rfl

theorem equivalent_zero {ι : Type} [Fintype ι] [DecidableEq ι] :
    Equivalent (ofProjection (Projection.zero : MatrixProjection A ι)) zero :=
  rectEquivalent_zero

def setoid : Setoid (FiniteProjection A) where
  r := Equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

theorem blockSum_congr {p q r s : FiniteProjection A}
    (h : Equivalent p q) (k : Equivalent r s) : Equivalent (blockSum p r) (blockSum q s) :=
  rectEquivalent_blockSum h k

theorem blockSum_comm (p q : FiniteProjection A) :
    Equivalent (blockSum p q) (blockSum q p) := by
  apply rectEquivalent_of_reindex _ _ (Equiv.sumComm q.Index p.Index)
  ext i j
  cases i <;> cases j <;> rfl

theorem blockSum_assoc (p q r : FiniteProjection A) :
    Equivalent (blockSum (blockSum p q) r) (blockSum p (blockSum q r)) := by
  apply rectEquivalent_of_reindex _ _ (Equiv.sumAssoc p.Index q.Index r.Index).symm
  ext i j
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;> rfl

theorem zero_blockSum (p : FiniteProjection A) : Equivalent (blockSum zero p) p := by
  apply equivalent_symm
  apply rectEquivalent_of_reindex _ _ (Equiv.emptySum Empty p.Index)
  ext i j
  rcases i with i | i
  · exact i.elim
  · rcases j with j | j
    · exact j.elim
    · rfl

theorem blockSum_zero (p : FiniteProjection A) : Equivalent (blockSum p zero) p :=
  equivalent_trans (blockSum_comm p zero) (zero_blockSum p)

end FiniteProjection

/-- Stable Murray–von Neumann classes of finite matrix projections. -/
abbrev StableProjectionMonoid (A : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] := Quotient (FiniteProjection.setoid (A := A))

namespace StableProjectionMonoid

/-- The class represented by a finite matrix projection. -/
def of (p : FiniteProjection A) : StableProjectionMonoid A := Quotient.mk _ p

instance : Zero (StableProjectionMonoid A) := ⟨of FiniteProjection.zero⟩

instance : Add (StableProjectionMonoid A) :=
  ⟨Quotient.map₂ FiniteProjection.blockSum (fun _ _ h _ _ k =>
    FiniteProjection.blockSum_congr h k)⟩

@[simp] theorem of_blockSum (p q : FiniteProjection A) :
    of (FiniteProjection.blockSum p q) = of p + of q := rfl

theorem of_eq_of_equivalent {p q : FiniteProjection A} (h : FiniteProjection.Equivalent p q) :
    of p = of q := Quotient.sound h

theorem of_eq_iff (p q : FiniteProjection A) :
    of p = of q ↔ FiniteProjection.Equivalent p q := Quotient.eq

/-- Block sum gives an additive commutative monoid on the stable classes. -/
instance instAddCommMonoid : AddCommMonoid (StableProjectionMonoid A) where
  add_assoc a b c := Quotient.inductionOn₃ a b c fun p q r =>
    Quotient.sound (FiniteProjection.blockSum_assoc p q r)
  zero_add a := Quotient.inductionOn a fun p => Quotient.sound (FiniteProjection.zero_blockSum p)
  add_zero a := Quotient.inductionOn a fun p => Quotient.sound (FiniteProjection.blockSum_zero p)
  add_comm a b := Quotient.inductionOn₂ a b fun p q =>
    Quotient.sound (FiniteProjection.blockSum_comm p q)
  nsmul := nsmulRec

@[simp] theorem of_zeroProjection {ι : Type} [Fintype ι] [DecidableEq ι] :
    of (FiniteProjection.ofProjection (Projection.zero : MatrixProjection A ι)) = 0 :=
  Quotient.sound FiniteProjection.equivalent_zero

/-- The quotient really identifies zero-padding of a projection. -/
theorem of_stabilize {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (p : MatrixProjection A ι) :
    of (FiniteProjection.ofProjection (stabilizeProjection (κ := κ) p)) =
      of (FiniteProjection.ofProjection p) :=
  Quotient.sound (rectEquivalent_symm (rectEquivalent_stabilize p))

/-- Allowing arbitrary small finite index types adds no extra classes. -/
theorem exists_finRepresentative (x : StableProjectionMonoid A) :
    ∃ (n : ℕ) (p : MatrixProjection A (Fin n)), of (FiniteProjection.ofProjection p) = x := by
  refine Quotient.inductionOn x ?_
  intro p
  exact ⟨Fintype.card p.Index, p.toFin.projection,
    Quotient.sound (FiniteProjection.equivalent_symm (FiniteProjection.equivalent_toFin p))⟩

end StableProjectionMonoid
end BC4lean.OperatorKTheory
