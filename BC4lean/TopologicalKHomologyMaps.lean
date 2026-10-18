import BC4lean.TopologicalKHomologyColimit
import BC4lean.DirectedAddGroupColimitMap
import BC4lean.CocompactPieceMap

/-! # Maps of topological K-homology from actual piecewise proper maps

An ambient equivariant map need not be proper. Its restriction from a cocompact
piece to its image is proper, and gives the compatible family used here.
-/

noncomputable section
open Topology TopologicalSpace
open scoped ZeroAtInfty ComplexOrder
universe uΓ u

namespace BC4lean.TopologicalKHomology
open ProperActions KKTheory KKTheory.GroupUniverseParityFunctoriality

variable {Γ : Type uΓ} [Group Γ] [Countable Γ]
variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction Γ X] [MulAction Γ Y] [MulAction Γ Z]
  [ContinuousConstSMul Γ X] [ContinuousConstSMul Γ Y] [ContinuousConstSMul Γ Z]
  [LocallyCompactSpace X] [LocallyCompactSpace Y] [LocallyCompactSpace Z]
  [T2Space X] [T2Space Y] [T2Space Z]
  [SecondCountableTopology X] [SecondCountableTopology Y] [SecondCountableTopology Z]

local instance cZero_separable (W : Type u) [TopologicalSpace W] [T2Space W]
    [LocallyCompactSpace W] [SecondCountableTopology W] : SeparableSpace C₀(W, ℂ) :=
  cZero_separableSpace

/-- A proper equivariant map induces covariance of actual K-homology. -/
def properPushforward (p : Bool) (f : EquivariantMap Γ X Y) (hf : IsProperMap f) :
    spaceGroup p Γ X →+ spaceGroup p Γ Y :=
  sourcePullbackHom.{uΓ,u,u,0,u} p (CZero.properPullback f hf)
    (CZero.properPullback_equivariant f hf)

@[simp] theorem properPushforward_id (p : Bool) :
    properPushforward p (EquivariantMap.id (Γ := Γ) (X := X)) isProperMap_id =
      AddMonoidHom.id (spaceGroup p Γ X) := by
  ext x
  unfold properPushforward sourcePullbackHom
  simp only [AddMonoidHom.mk'_apply, AddMonoidHom.id_apply]
  exact sourcePullback_id.{uΓ,u,0,u} p x

theorem properPushforward_comp (p : Bool) (g : EquivariantMap Γ Y Z)
    (f : EquivariantMap Γ X Y) (hg : IsProperMap g) (hf : IsProperMap f) :
    (properPushforward p g hg).comp (properPushforward p f hf) =
      properPushforward p (g.comp f) (hg.comp hf) := by
  ext x
  unfold properPushforward sourcePullbackHom
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.mk'_apply]
  rw [sourcePullback_comp.{uΓ,u,u,u,0,u} p]
  congr 1

section Pieces
variable [TopologicalSpace Γ] [DiscreteTopology Γ] [ProperSMul Γ X]
  [ProperSMul Γ Y] [ProperSMul Γ Z]

local instance maps_piece_locallyCompact (W : Type u) [TopologicalSpace W] [MulAction Γ W]
    [LocallyCompactSpace W] (S : CocompactPiece Γ W) :
    LocallyCompactSpace S.toInvariantSubset := S.locallyCompact

/-- The map on one piece into any closed cocompact piece containing its image. -/
def boundedMap (p : Bool) (f : EquivariantMap Γ X Y)
    (S : CocompactPiece Γ X) (T : CocompactPiece Γ Y)
    (h : CocompactPiece.map f S ≤ T) : pieceGroup p S →+ pieceGroup p T :=
  properPushforward p (CocompactPiece.mapRestrictionTo f S T h)
    (CocompactPiece.mapRestrictionTo_isProperMap f S T h)

omit [TopologicalSpace Γ] [DiscreteTopology Γ] [ProperSMul Γ X] in
theorem transition_eq_properPushforward (p : Bool) {S T : CocompactPiece Γ X}
    (h : S ≤ T) : transition p h =
      properPushforward p (CocompactPiece.inclusionMap h)
        (CocompactPiece.inclusionMap_isProperMap h) := rfl

omit [ProperSMul Γ X] in
/-- The source and target inclusions give the same actual map on K-homology. -/
theorem boundedMap_naturality (p : Bool) (f : EquivariantMap Γ X Y)
    {S S' : CocompactPiece Γ X} {T T' : CocompactPiece Γ Y}
    (hS : S ≤ S') (hT : T ≤ T') (h : CocompactPiece.map f S ≤ T)
    (h' : CocompactPiece.map f S' ≤ T') :
    (transition p hT).comp (boundedMap p f S T h) =
      (boundedMap p f S' T' h').comp (transition p hS) := by
  rw [transition_eq_properPushforward, transition_eq_properPushforward]
  unfold boundedMap
  rw [properPushforward_comp, properPushforward_comp]
  congr 1

omit [ProperSMul Γ X] in
theorem boundedMap_target (p : Bool) (f : EquivariantMap Γ X Y)
    (S : CocompactPiece Γ X) {T T' : CocompactPiece Γ Y}
    (hT : T ≤ T') (h : CocompactPiece.map f S ≤ T)
    (h' : CocompactPiece.map f S ≤ T') (x : pieceGroup p S) :
    transition p hT (boundedMap p f S T h x) = boundedMap p f S T' h' x := by
  have he := congrArg (fun k : pieceGroup p S →+ pieceGroup p T' => k x)
    (boundedMap_naturality p f (le_refl S) hT h h')
  simpa only [AddMonoidHom.comp_apply, transition_refl] using he

/-- The image pieces and the actual bounded maps form a diagram morphism. -/
def mapDiagram (p : Bool) (f : EquivariantMap Γ X Y) :
    DirectedAddGroupDiagram.Hom (diagram (Γ := Γ) (X := X) p)
      (diagram (Γ := Γ) (X := Y) p)
      ⟨CocompactPiece.map f, fun _ _ h => CocompactPiece.map_mono f h⟩ where
  app S := boundedMap p f S (CocompactPiece.map f S) le_rfl
  naturality S T h x := congrArg (fun k : pieceGroup p S →+
      pieceGroup p (CocompactPiece.map f T) => k x)
    (boundedMap_naturality p f h (CocompactPiece.map_mono f h) le_rfl le_rfl)

/-- Covariance of the constructed topological-side group for all continuous
equivariant maps between the indicated proper spaces. -/
def pushforward (p : Bool) (f : EquivariantMap Γ X Y) :
    group (Γ := Γ) (X := X) p →+ group (Γ := Γ) (X := Y) p :=
  (mapDiagram p f).colimitMap

omit [ProperSMul Γ X] in
@[simp] theorem pushforward_ofPiece (p : Bool) (f : EquivariantMap Γ X Y)
    (S : CocompactPiece Γ X) (x : pieceGroup p S) :
    pushforward p f (ofPiece p S x) =
      ofPiece p (CocompactPiece.map f S)
        (boundedMap p f S (CocompactPiece.map f S) le_rfl x) := rfl

omit [ProperSMul Γ X] in
/-- Any bounding target piece computes the same colimit value. -/
theorem pushforward_ofPiece_bounded (p : Bool) (f : EquivariantMap Γ X Y)
    (S : CocompactPiece Γ X) (T : CocompactPiece Γ Y)
    (h : CocompactPiece.map f S ≤ T) (x : pieceGroup p S) :
    pushforward p f (ofPiece p S x) = ofPiece p T (boundedMap p f S T h x) := by
  rw [pushforward_ofPiece]
  rw [← ofPiece_transition p h]
  rw [boundedMap_target p f S h le_rfl h]

@[simp] theorem pushforward_id (p : Bool) :
    pushforward p (EquivariantMap.id (Γ := Γ) (X := X)) =
      AddMonoidHom.id (group (Γ := Γ) (X := X) p) := by
  apply (diagram p).hom_ext
  intro S
  ext x
  change pieceGroup p S at x
  change pushforward p EquivariantMap.id (ofPiece p S x) = ofPiece p S x
  have h : CocompactPiece.map (EquivariantMap.id (Γ := Γ) (X := X)) S ≤ S :=
    (CocompactPiece.map_id S).le
  rw [pushforward_ofPiece_bounded p EquivariantMap.id S S h]
  unfold boundedMap
  simp only [CocompactPiece.mapRestrictionTo_id, properPushforward_id, AddMonoidHom.id_apply]

omit [ProperSMul Γ X] in
theorem boundedMap_comp (p : Bool) (g : EquivariantMap Γ Y Z)
    (f : EquivariantMap Γ X Y) (S : CocompactPiece Γ X)
    (T : CocompactPiece Γ Y) (U : CocompactPiece Γ Z)
    (hf : CocompactPiece.map f S ≤ T) (hg : CocompactPiece.map g T ≤ U)
    (hgf : CocompactPiece.map (g.comp f) S ≤ U) :
    (boundedMap p g T U hg).comp (boundedMap p f S T hf) =
      boundedMap p (g.comp f) S U hgf := by
  unfold boundedMap
  rw [properPushforward_comp]
  congr 1

omit [ProperSMul Γ X] in
/-- Ambient comparison maps compose on the actual topological-side groups. -/
theorem pushforward_comp (p : Bool) (g : EquivariantMap Γ Y Z)
    (f : EquivariantMap Γ X Y) :
    (pushforward p g).comp (pushforward p f) = pushforward p (g.comp f) := by
  apply (diagram p).hom_ext
  intro S
  ext x
  change pieceGroup p S at x
  let T := CocompactPiece.map f S
  let U := CocompactPiece.map g T
  have hgf : CocompactPiece.map (g.comp f) S ≤ U :=
    (CocompactPiece.map_comp g f S).symm.le
  change pushforward p g (pushforward p f (ofPiece p S x)) =
    pushforward p (g.comp f) (ofPiece p S x)
  rw [pushforward_ofPiece_bounded p f S T le_rfl,
    pushforward_ofPiece_bounded p g T U le_rfl,
    pushforward_ofPiece_bounded p (g.comp f) S U hgf]
  exact congrArg (ofPiece p U) (congrArg
    (fun k : pieceGroup p S →+ pieceGroup p U => k x)
    (boundedMap_comp p g f S T U le_rfl le_rfl hgf))

end Pieces
end BC4lean.TopologicalKHomology
