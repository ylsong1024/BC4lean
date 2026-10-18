import BC4lean.CocompactPieceRepresentatives
import BC4lean.InvariantSubspaceMaps

/-! # Images and proper restrictions of cocompact pieces

An equivariant map from a locally compact space with compact orbit quotient
to a proper discrete-group space is proper. In particular every comparison
map between proper models is proper after restriction to one cocompact piece.
No properness of the comparison map on its whole ambient model is assumed.
-/

noncomputable section
open Topology
open scoped Pointwise

namespace BC4lean.ProperActions

variable {Γ X Y Z : Type*} [Group Γ]
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction Γ X] [MulAction Γ Y] [MulAction Γ Z]

namespace EquivariantMap

/-- The continuous map induced on orbit spaces by an equivariant map. -/
def orbitMap (f : EquivariantMap Γ X Y) :
    Quotient (MulAction.orbitRel Γ X) → Quotient (MulAction.orbitRel Γ Y) :=
  Quotient.map f (by
    rintro a b ⟨g, hg⟩
    exact ⟨g, by simpa only [f.map_smul] using congrArg f hg⟩)

theorem continuous_orbitMap (f : EquivariantMap Γ X Y) : Continuous f.orbitMap :=
  (continuous_quotient_mk'.comp f.continuous).quotient_lift _

@[simp] theorem orbitMap_mk (f : EquivariantMap Γ X Y) (x : X) :
    f.orbitMap (Quotient.mk _ x) = Quotient.mk _ (f x) := rfl

/-- Compactness of the source orbit quotient gives compactness of the image
in the target orbit space. -/
theorem isCompact_quotient_image [CompactSpace (Quotient (MulAction.orbitRel Γ X))]
    (f : EquivariantMap Γ X Y) :
    IsCompact (Quotient.mk (MulAction.orbitRel Γ Y) '' Set.range f) := by
  have he : Quotient.mk (MulAction.orbitRel Γ Y) '' Set.range f = Set.range f.orbitMap := by
    ext q
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨Quotient.mk _ x, rfl⟩
    · rintro ⟨q, rfl⟩
      induction q using Quotient.inductionOn with
      | _ x => exact ⟨f x, ⟨x, rfl⟩, rfl⟩
  rw [he]
  exact isCompact_range f.continuous_orbitMap

variable [TopologicalSpace Γ] [DiscreteTopology Γ]

/-- A map from a cocompact locally compact action to a proper action is
proper. The source need not itself be assumed proper. -/
theorem isProperMap_of_compactOrbit [ContinuousConstSMul Γ X]
    [WeaklyLocallyCompactSpace X]
    [CompactSpace (Quotient (MulAction.orbitRel Γ X))]
    [LocallyCompactSpace Y] [T2Space Y] [ProperSMul Γ Y]
    (f : EquivariantMap Γ X Y) : IsProperMap f := by
  obtain ⟨K, hK, hrep⟩ := exists_compact_orbit_representatives (Γ := Γ) (X := X)
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨f.continuous, fun L hL => ?_⟩
  let F : Set Γ := transporter (f '' K) L
  have hF : F.Finite := finite_transporter (hK.image f.continuous) hL
  have hU : IsCompact (⋃ g ∈ F, g • K) :=
    hF.isCompact_biUnion (fun g _ => hK.smul g)
  apply hU.of_isClosed_subset (hL.isClosed.preimage f.continuous)
  intro x hx
  obtain ⟨g, y, hy, hgy⟩ := hrep x
  have hg : g ∈ F := by
    refine ⟨f x, ?_, hx⟩
    have hm : g • f y ∈ g • (f '' K) := Set.smul_mem_smul_set ⟨y, hy, rfl⟩
    simpa only [← f.map_smul, hgy] using hm
  apply Set.mem_iUnion.mpr ⟨g, ?_⟩
  apply Set.mem_iUnion.mpr ⟨hg, ?_⟩
  simpa only [hgy] using Set.smul_mem_smul_set (a := g) hy

end EquivariantMap

namespace CocompactPiece

/-- Restrict a comparison map to a source cocompact piece, keeping its
ambient target. -/
def ambientRestriction (f : EquivariantMap Γ X Y) (S : CocompactPiece Γ X) :
    EquivariantMap Γ S.toInvariantSubset Y :=
  f.comp S.toInvariantSubset.inclusion

@[simp] theorem ambientRestriction_apply (f : EquivariantMap Γ X Y)
    (S : CocompactPiece Γ X) (x : S.toInvariantSubset) :
    ambientRestriction f S x = f x := rfl

private theorem range_ambientRestriction (f : EquivariantMap Γ X Y)
    (S : CocompactPiece Γ X) : Set.range (ambientRestriction f S) = f '' (S : Set X) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

variable [TopologicalSpace Γ] [DiscreteTopology Γ]
  [ContinuousConstSMul Γ X] [LocallyCompactSpace X]
  [LocallyCompactSpace Y] [T2Space Y] [ProperSMul Γ Y]

theorem ambientRestriction_isProperMap (f : EquivariantMap Γ X Y)
    (S : CocompactPiece Γ X) : IsProperMap (ambientRestriction f S) := by
  let := S.locallyCompact
  let := S.compactSpace_orbit
  exact (ambientRestriction f S).isProperMap_of_compactOrbit

/-- The actual image of a cocompact piece is closed, invariant and cocompact. -/
def map (f : EquivariantMap Γ X Y) (S : CocompactPiece Γ X) : CocompactPiece Γ Y where
  carrier := f '' (S : Set X)
  smul_mem g _ := by
    rintro ⟨x, hx, rfl⟩
    exact ⟨g • x, S.smul_mem g hx, f.map_smul g x⟩
  isClosed_carrier := by
    rw [← range_ambientRestriction f S]
    exact (ambientRestriction_isProperMap f S).isClosed_range
  isCompact_image := by
    let := S.compactSpace_orbit
    rw [← range_ambientRestriction f S]
    exact (ambientRestriction f S).isCompact_quotient_image

@[simp] theorem mem_map (f : EquivariantMap Γ X Y) (S : CocompactPiece Γ X) (y : Y) :
    y ∈ map f S ↔ ∃ x ∈ S, f x = y := Iff.rfl

theorem map_mono (f : EquivariantMap Γ X Y) {S T : CocompactPiece Γ X}
    (h : S ≤ T) : map f S ≤ map f T := Set.image_mono h

@[simp] theorem map_id [T2Space X] [ProperSMul Γ X] (S : CocompactPiece Γ X) :
    map (EquivariantMap.id (Γ := Γ) (X := X)) S = S := by
  apply SetLike.ext
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem map_comp [LocallyCompactSpace Z] [T2Space Z] [ProperSMul Γ Z]
    (g : EquivariantMap Γ Y Z) (f : EquivariantMap Γ X Y) (S : CocompactPiece Γ X) :
    map g (map f S) = map (g.comp f) S := by
  apply SetLike.ext
  intro z
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩

theorem map_comp_le [LocallyCompactSpace Z] [T2Space Z] [ProperSMul Γ Z]
    (g : EquivariantMap Γ Y Z) (f : EquivariantMap Γ X Y)
    {S : CocompactPiece Γ X} {T : CocompactPiece Γ Y} {U : CocompactPiece Γ Z}
    (hf : map f S ≤ T) (hg : map g T ≤ U) : map (g.comp f) S ≤ U := by
  rw [← map_comp g f S]
  exact (map_mono g hf).trans hg

/-- The proper equivariant comparison map with its exact image as target. -/
def mapRestriction (f : EquivariantMap Γ X Y) (S : CocompactPiece Γ X) :
    EquivariantMap Γ S.toInvariantSubset (map f S).toInvariantSubset where
  toFun x := ⟨f x, ⟨x, x.property, rfl⟩⟩
  continuous_toFun := (f.continuous.comp continuous_subtype_val).subtype_mk _
  map_smul' g x := Subtype.ext (f.map_smul g x)

@[simp] theorem mapRestriction_coe (f : EquivariantMap Γ X Y)
    (S : CocompactPiece Γ X) (x : S.toInvariantSubset) :
    (mapRestriction f S x : Y) = f x := rfl

theorem mapRestriction_isProperMap (f : EquivariantMap Γ X Y) (S : CocompactPiece Γ X) :
    IsProperMap (mapRestriction f S) := by
  exact isProperMap_of_comp_of_inj (mapRestriction f S).continuous continuous_subtype_val
    (ambientRestriction_isProperMap f S) Subtype.val_injective

/-- Comparison maps commute with both source and image inclusions. -/
theorem mapRestriction_naturality (f : EquivariantMap Γ X Y)
    {S T : CocompactPiece Γ X} (h : S ≤ T) :
    (inclusionMap (map_mono f h)).comp (mapRestriction f S) =
      (mapRestriction f T).comp (inclusionMap h) := by
  ext x
  rfl

/-- Restrict to any closed cocompact target piece containing the image. -/
def mapRestrictionTo (f : EquivariantMap Γ X Y) (S : CocompactPiece Γ X)
    (T : CocompactPiece Γ Y) (h : map f S ≤ T) :
    EquivariantMap Γ S.toInvariantSubset T.toInvariantSubset :=
  (inclusionMap h).comp (mapRestriction f S)

@[simp] theorem mapRestrictionTo_coe (f : EquivariantMap Γ X Y)
    (S : CocompactPiece Γ X) (T : CocompactPiece Γ Y) (h : map f S ≤ T)
    (x : S.toInvariantSubset) : (mapRestrictionTo f S T h x : Y) = f x := rfl

theorem mapRestrictionTo_isProperMap (f : EquivariantMap Γ X Y)
    (S : CocompactPiece Γ X) (T : CocompactPiece Γ Y) (h : map f S ≤ T) :
    IsProperMap (mapRestrictionTo f S T h) := by
  exact isProperMap_of_comp_of_inj (mapRestrictionTo f S T h).continuous continuous_subtype_val
    (ambientRestriction_isProperMap f S) Subtype.val_injective

/-- Enlarging the source and target pieces preserves the comparison map. -/
theorem mapRestrictionTo_naturality (f : EquivariantMap Γ X Y)
    {S S' : CocompactPiece Γ X} {T T' : CocompactPiece Γ Y}
    (hS : S ≤ S') (hT : T ≤ T') (h : map f S ≤ T) (h' : map f S' ≤ T') :
    (inclusionMap hT).comp (mapRestrictionTo f S T h) =
      (mapRestrictionTo f S' T' h').comp (inclusionMap hS) := by
  ext x
  rfl

/-- Successive bounded comparison maps equal the directly restricted composite. -/
theorem mapRestrictionTo_comp [LocallyCompactSpace Z] [T2Space Z] [ProperSMul Γ Z]
    (g : EquivariantMap Γ Y Z) (f : EquivariantMap Γ X Y)
    (S : CocompactPiece Γ X) (T : CocompactPiece Γ Y) (U : CocompactPiece Γ Z)
    (hf : map f S ≤ T) (hg : map g T ≤ U) (hgf : map (g.comp f) S ≤ U) :
    (mapRestrictionTo g T U hg).comp (mapRestrictionTo f S T hf) =
      mapRestrictionTo (g.comp f) S U hgf := by
  ext x
  rfl

@[simp] theorem mapRestrictionTo_id [T2Space X] [ProperSMul Γ X]
    (S : CocompactPiece Γ X) (h : map (EquivariantMap.id (Γ := Γ) (X := X)) S ≤ S) :
    mapRestrictionTo EquivariantMap.id S S h = EquivariantMap.id := by
  ext x
  rfl

end CocompactPiece
end BC4lean.ProperActions
