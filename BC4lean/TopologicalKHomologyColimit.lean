import BC4lean.TopologicalKHomologyDiagram
import BC4lean.DirectedAddGroupColimitCofinal

/-! # The topological-side filtered colimit and cofinal indexing independence

The diagram contains the actual full even/odd KK groups of closed invariant
cocompact subspaces. Its colimit is a constructed additive group with a universal
property, not an assumed value for the topological side.
-/

noncomputable section
open Topology
universe uΓ uX uJ

namespace BC4lean.TopologicalKHomology
open ProperActions

variable {Γ : Type uΓ} {X : Type uX} [Group Γ]
  [TopologicalSpace X] [MulAction Γ X]

instance cocompactPiece_nonempty : Nonempty (CocompactPiece Γ X) :=
  ⟨CocompactPiece.empty⟩

instance cocompactPiece_directedOrder : IsDirectedOrder (CocompactPiece Γ X) :=
  ⟨CocompactPiece.directed⟩

variable [Countable Γ] [ContinuousConstSMul Γ X]
  [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]

/-- The genuine directed system used for the topological side. -/
def diagram (p : Bool) : DirectedAddGroupDiagram (CocompactPiece Γ X) where
  obj := pieceGroup p
  map _ _ h := transition p h
  map_id := transition_refl p
  map_comp _ _ _ hST hTU x := transition_trans p hST hTU x

/-- The topological-side group for the chosen ambient proper model. -/
abbrev group (p : Bool) := (diagram (Γ := Γ) (X := X) p).Colimit

/-- The canonical map from a cocompact piece into the topological-side group. -/
def ofPiece (p : Bool) (S : CocompactPiece Γ X) :
    pieceGroup p S →+ group (Γ := Γ) (X := X) p :=
  (diagram p).of S

@[simp] theorem ofPiece_transition (p : Bool) {S T : CocompactPiece Γ X}
    (h : S ≤ T) (x : pieceGroup p S) :
    ofPiece p T (transition p h x) = ofPiece p S x :=
  (diagram p).of_map h x

/-- Equality is detected in a larger closed invariant cocompact piece. -/
theorem ofPiece_eq_iff (p : Bool) {S T : CocompactPiece Γ X}
    (x : pieceGroup p S) (y : pieceGroup p T) :
    ofPiece p S x = ofPiece p T y ↔
      ∃ (U : CocompactPiece Γ X) (hSU : S ≤ U) (hTU : T ≤ U),
        transition p hSU x = transition p hTU y :=
  (diagram p).of_eq_iff x y

/-- The group is characterized by the actual additive colimit universal property. -/
theorem existsUnique_desc (p : Bool) {A : Type*} [AddCommGroup A]
    (f : ∀ S : CocompactPiece Γ X, pieceGroup p S →+ A)
    (hf : ∀ S T (h : S ≤ T) x, f T (transition p h x) = f S x) :
    ∃! F : group (Γ := Γ) (X := X) p →+ A,
      ∀ S, F.comp (ofPiece p S) = f S :=
  (diagram p).existsUnique_desc f hf

variable {J : Type uJ} [Preorder J] [Nonempty J] [IsDirectedOrder J]

/-- A cofinal indexing family computes exactly the same topological-side group.
Pointwise covering alone is not a sufficient hypothesis. -/
def cofinalIndexEquiv (p : Bool) (φ : J →o CocompactPiece Γ X)
    (hφ : ∀ S, ∃ j, S ≤ φ j) :
    ((diagram p).restrict φ).Colimit ≃+ group (Γ := Γ) (X := X) p :=
  (diagram p).cofinalEquiv φ hφ

@[simp] theorem cofinalIndexEquiv_of (p : Bool) (φ : J →o CocompactPiece Γ X)
    (hφ : ∀ S, ∃ j, S ≤ φ j) (j : J) (x : pieceGroup p (φ j)) :
    cofinalIndexEquiv p φ hφ (((diagram p).restrict φ).of j x) = ofPiece p (φ j) x := rfl

end BC4lean.TopologicalKHomology
