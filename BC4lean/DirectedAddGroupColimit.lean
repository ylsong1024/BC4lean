import Mathlib.Algebra.Colimit.DirectLimit

/-! # Filtered colimits of additive abelian groups

A diagram records its actual groups and transition homomorphisms, including their
identity and composition laws. For a nonempty directed preorder its colimit is
Mathlib's quotient of the disjoint union by eventual equality. In particular,
the universal property below is proved for a constructed additive group.
-/

noncomputable section

universe u v w

namespace BC4lean

/-- An additive-group diagram over a preorder, with its functoriality laws. -/
structure DirectedAddGroupDiagram (ι : Type u) [Preorder ι] where
  obj : ι → Type v
  [group : ∀ i, AddCommGroup (obj i)]
  map : ∀ i j, i ≤ j → obj i →+ obj j
  map_id : ∀ i (x : obj i), map i i le_rfl x = x
  map_comp : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k) (x : obj i),
    map j k hjk (map i j hij x) = map i k (hij.trans hjk) x

attribute [instance] DirectedAddGroupDiagram.group

namespace DirectedAddGroupDiagram

variable {ι : Type u} [Preorder ι] (D : DirectedAddGroupDiagram.{u, v} ι)

instance directedSystem : DirectedSystem D.obj (D.map · · ·) where
  map_self {i} x := D.map_id i x
  map_map {k j i} hij hjk x := D.map_comp i j k hij hjk x

variable [Nonempty ι] [IsDirectedOrder ι]

/-- The actual filtered colimit group, constructed using eventual equality. -/
abbrev Colimit : Type (max u v) := DirectLimit D.obj D.map

/-- The canonical homomorphism from an object into the colimit. -/
def of (i : ι) : D.obj i →+ D.Colimit where
  toFun x := ⟦⟨i, x⟩⟧
  map_zero' := (DirectLimit.zero_def i).symm
  map_add' _ _ := (DirectLimit.add_def ..).symm

/-- The canonical maps commute with every transition homomorphism. -/
@[simp] theorem of_map {i j : ι} (hij : i ≤ j) (x : D.obj i) :
    D.of j (D.map i j hij x) = D.of i x :=
  DirectLimit.mk_apply i j x hij

/-- Every colimit element comes from one object of the diagram. -/
theorem exists_of (z : D.Colimit) : ∃ i x, D.of i x = z := by
  obtain ⟨i, x, hx⟩ := DirectLimit.exists_eq_mk D.map z
  exact ⟨i, x, hx.symm⟩

/-- Equality in the colimit is precisely equality after passage to one common upper bound. -/
theorem of_eq_iff {i j : ι} (x : D.obj i) (y : D.obj j) :
    D.of i x = D.of j y ↔
      ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k), D.map i k hik x = D.map j k hjk y :=
  Quotient.eq

/-- A class vanishes precisely when some transition sends its representative to zero. -/
theorem of_eq_zero_iff {i : ι} (x : D.obj i) :
    D.of i x = 0 ↔ ∃ (j : ι) (hij : i ≤ j), D.map i j hij x = 0 := by
  exact DirectLimit.exists_eq_zero (f := D.map) ⟨i, x⟩

variable {P : Type w} [AddCommGroup P]

/-- A compatible family of additive homomorphisms from the objects of a diagram. -/
def Compatible (g : ∀ i, D.obj i →+ P) : Prop :=
  ∀ i j (hij : i ≤ j) (x : D.obj i), g j (D.map i j hij x) = g i x

/-- Descend a compatible family to the constructed colimit group. -/
def desc (g : ∀ i, D.obj i →+ P) (hg : D.Compatible g) : D.Colimit →+ P where
  toFun := DirectLimit.lift D.map (fun i x => g i x) (fun i j h x => (hg i j h x).symm)
  map_zero' := DirectLimit.lift_zero _ _
  map_add' := DirectLimit.lift_add _ _

@[simp] theorem desc_of (g : ∀ i, D.obj i →+ P) (hg : D.Compatible g)
    (i : ι) (x : D.obj i) : D.desc g hg (D.of i x) = g i x := rfl

/-- Maps out of the colimit are determined by their restrictions to all objects. -/
@[ext] theorem hom_ext {f g : D.Colimit →+ P}
    (h : ∀ i, f.comp (D.of i) = g.comp (D.of i)) : f = g := by
  apply AddMonoidHom.ext
  intro z
  obtain ⟨i, x, rfl⟩ := D.exists_of z
  exact congrArg (fun k : D.obj i →+ P => k x) (h i)

/-- Uniqueness in the universal property of the colimit. -/
theorem desc_unique (g : ∀ i, D.obj i →+ P) (hg : D.Compatible g)
    (f : D.Colimit →+ P) (hf : ∀ i, f.comp (D.of i) = g i) : f = D.desc g hg := by
  apply D.hom_ext
  intro i
  exact hf i

/-- The constructed group satisfies the additive-group colimit universal property. -/
theorem existsUnique_desc (g : ∀ i, D.obj i →+ P) (hg : D.Compatible g) :
    ∃! f : D.Colimit →+ P, ∀ i, f.comp (D.of i) = g i := by
  refine ⟨D.desc g hg, fun _ => rfl, fun f hf => D.desc_unique g hg f hf⟩

/-- Precomposition with the canonical maps gives precisely the compatible families. -/
def descEquiv : (D.Colimit →+ P) ≃ {g : ∀ i, D.obj i →+ P // D.Compatible g} where
  toFun f := ⟨fun i => f.comp (D.of i), fun i j h x => by simp⟩
  invFun g := D.desc g.val g.property
  left_inv f := by
    apply D.hom_ext
    intro i
    rfl
  right_inv g := by
    apply Subtype.ext
    rfl

end DirectedAddGroupDiagram
end BC4lean
