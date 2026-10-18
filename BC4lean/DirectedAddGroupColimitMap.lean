import BC4lean.DirectedAddGroupColimit

/-! # Maps of filtered additive-group colimits

A morphism includes a monotone map of index preorders and actual compatible
homomorphisms of the groups. The induced colimit homomorphism is constructed
using the proved universal property, with representative, identity, composition,
and eventual-equality formulas.
-/

noncomputable section

universe u v uκ vκ uL vL

namespace BC4lean.DirectedAddGroupDiagram

variable {ι : Type u} [Preorder ι] {κ : Type uκ} [Preorder κ]
variable {L : Type uL} [Preorder L]
variable (D : DirectedAddGroupDiagram.{u, v} ι)
variable (E : DirectedAddGroupDiagram.{uκ, vκ} κ)
variable (F : DirectedAddGroupDiagram.{uL, vL} L)

/-- A diagram morphism over a monotone map of index preorders. -/
structure Hom (φ : ι →o κ) where
  app : ∀ i, D.obj i →+ E.obj (φ i)
  naturality : ∀ i j (hij : i ≤ j) (x : D.obj i),
    E.map (φ i) (φ j) (φ.monotone hij) (app i x) = app j (D.map i j hij x)

namespace Hom

variable {D E F}

/-- The identity diagram morphism. -/
def id (D : DirectedAddGroupDiagram.{u, v} ι) : Hom D D (OrderHom.id : ι →o ι) where
  app i := AddMonoidHom.id (D.obj i)
  naturality _ _ _ _ := rfl

/-- Composition of diagram morphisms includes composition of the indexing maps. -/
def comp {φ : ι →o κ} {ψ : κ →o L} (f : Hom D E φ) (g : Hom E F ψ) :
    Hom D F (ψ.comp φ) where
  app i := (g.app (φ i)).comp (f.app i)
  naturality i j hij x := by
    change F.map (ψ (φ i)) (ψ (φ j)) _ (g.app (φ i) (f.app i x)) =
      g.app (φ j) (f.app j (D.map i j hij x))
    rw [g.naturality (φ i) (φ j) (φ.monotone hij), f.naturality i j hij]

variable [Nonempty ι] [IsDirectedOrder ι] [Nonempty κ] [IsDirectedOrder κ]

/-- A genuine homomorphism between the constructed filtered colimit groups. -/
def colimitMap {φ : ι →o κ} (f : Hom D E φ) : D.Colimit →+ E.Colimit :=
  D.desc (fun i => (E.of (φ i)).comp (f.app i)) (by
    intro i j hij x
    change E.of (φ j) (f.app j (D.map i j hij x)) = E.of (φ i) (f.app i x)
    rw [← f.naturality i j hij, E.of_map])

@[simp] theorem colimitMap_of {φ : ι →o κ} (f : Hom D E φ) (i : ι) (x : D.obj i) :
    f.colimitMap (D.of i x) = E.of (φ i) (f.app i x) := rfl

/-- Pointwise equal natural families induce equal colimit homomorphisms. -/
theorem colimitMap_congr {φ : ι →o κ} (f g : Hom D E φ)
    (h : ∀ i (x : D.obj i), f.app i x = g.app i x) : f.colimitMap = g.colimitMap := by
  apply D.hom_ext
  intro i
  apply AddMonoidHom.ext
  intro x
  change E.of (φ i) (f.app i x) = E.of (φ i) (g.app i x)
  rw [h i x]

/-- Diagram maps with possibly different index maps agree on the colimit whenever
their values become equal at a common later target index. -/
theorem colimitMap_eq_of_eventualEq {φ ψ : ι →o κ} (f : Hom D E φ) (g : Hom D E ψ)
    (h : ∀ i (x : D.obj i), ∃ (j : κ) (hφ : φ i ≤ j) (hψ : ψ i ≤ j),
      E.map (φ i) j hφ (f.app i x) = E.map (ψ i) j hψ (g.app i x)) :
    f.colimitMap = g.colimitMap := by
  apply D.hom_ext
  intro i
  apply AddMonoidHom.ext
  intro x
  exact (E.of_eq_iff (f.app i x) (g.app i x)).mpr (h i x)

/-- The identity diagram morphism induces the identity colimit homomorphism. -/
@[simp] theorem id_colimitMap :
    (id D).colimitMap = AddMonoidHom.id D.Colimit := by
  apply D.hom_ext
  intro i
  rfl

variable [Nonempty L] [IsDirectedOrder L]

/-- Composition of diagram morphisms induces composition of colimit homomorphisms. -/
@[simp] theorem comp_colimitMap {φ : ι →o κ} {ψ : κ →o L}
    (f : Hom D E φ) (g : Hom E F ψ) :
    (f.comp g).colimitMap = g.colimitMap.comp f.colimitMap := by
  apply D.hom_ext
  intro i
  rfl

end Hom
end BC4lean.DirectedAddGroupDiagram
