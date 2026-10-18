import BC4lean.CocompactPieceMap
import BC4lean.EquivariantHomotopy

/-! # Compact families of equivariant maps on cocompact pieces

The whole image of a compactly parametrized family lies in one actual
closed cocompact target piece. The jointly continuous family, restricted
to one source piece, is proper. In particular these statements apply to
the entire unit interval of an equivariant homotopy.
-/

noncomputable section
open Topology
open scoped Pointwise

namespace BC4lean.ProperActions

variable {Γ P X Y : Type*} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
  [TopologicalSpace P] [CompactSpace P]
  [TopologicalSpace X] [TopologicalSpace Y] [MulAction Γ X] [MulAction Γ Y]
  [ContinuousConstSMul Γ X] [WeaklyLocallyCompactSpace X]
  [CompactSpace (Quotient (MulAction.orbitRel Γ X))]
  [LocallyCompactSpace Y] [T2Space Y] [ProperSMul Γ Y]

/-- A compact family of equivariant maps on a cocompact source is jointly
proper, with the parameter included in the source. -/
theorem isProperMap_compactEquivariantFamily (h : C(P × X, Y))
    (he : ∀ (t : P) (g : Γ) (x : X), h (t, g • x) = g • h (t, x)) :
    IsProperMap h := by
  obtain ⟨K, hK, hrep⟩ := exists_compact_orbit_representatives (Γ := Γ) (X := X)
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨h.continuous, fun L hL => ?_⟩
  let F : Set Γ := transporter (h '' (Set.univ ×ˢ K)) L
  have hF : F.Finite := finite_transporter
    (((isCompact_univ : IsCompact (Set.univ : Set P)).prod hK).image h.continuous) hL
  have hU : IsCompact ((Set.univ : Set P) ×ˢ (⋃ g ∈ F, g • K)) :=
    isCompact_univ.prod (hF.isCompact_biUnion (fun g _ => hK.smul g))
  apply hU.of_isClosed_subset (hL.isClosed.preimage h.continuous)
  rintro ⟨t, x⟩ hx
  obtain ⟨g, y, hy, hgy⟩ := hrep x
  have hg : g ∈ F := by
    refine ⟨h (t, x), ?_, hx⟩
    have hm : g • h (t, y) ∈ g • (h '' (Set.univ ×ˢ K)) :=
      Set.smul_mem_smul_set ⟨(t, y), ⟨Set.mem_univ t, hy⟩, rfl⟩
    simpa only [← he, hgy] using hm
  refine ⟨Set.mem_univ t, Set.mem_iUnion.mpr ⟨g, Set.mem_iUnion.mpr ⟨hg, ?_⟩⟩⟩
  simpa only [hgy] using Set.smul_mem_smul_set (a := g) hy

omit [TopologicalSpace Γ] [DiscreteTopology Γ] [LocallyCompactSpace Y]
  [T2Space Y] [ProperSMul Γ Y] in
/-- The whole family has compact image in the target orbit quotient. -/
theorem isCompact_quotient_image_compactEquivariantFamily (h : C(P × X, Y))
    (he : ∀ (t : P) (g : Γ) (x : X), h (t, g • x) = g • h (t, x)) :
    IsCompact (Quotient.mk (MulAction.orbitRel Γ Y) '' Set.range h) := by
  obtain ⟨K, hK, hrep⟩ := exists_compact_orbit_representatives (Γ := Γ) (X := X)
  have himage : Quotient.mk (MulAction.orbitRel Γ Y) '' Set.range h =
      Quotient.mk (MulAction.orbitRel Γ Y) '' (h '' (Set.univ ×ˢ K)) := by
    ext q
    constructor
    · rintro ⟨_, ⟨⟨t, x⟩, rfl⟩, rfl⟩
      obtain ⟨g, y, hy, hgy⟩ := hrep x
      refine ⟨h (t, y), ⟨(t, y), ⟨Set.mem_univ t, hy⟩, rfl⟩, ?_⟩
      apply Eq.symm
      apply Quotient.sound
      exact ⟨g, by
        change g • h (t, y) = h (t, x)
        rw [← he, hgy]⟩
    · rintro ⟨_, ⟨p, _, rfl⟩, rfl⟩
      exact ⟨h p, ⟨p, rfl⟩, rfl⟩
  rw [himage]
  exact ((isCompact_univ.prod hK).image h.continuous).image continuous_quot_mk

namespace CocompactPiece

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [MulAction Γ X] [MulAction Γ Y] [ContinuousConstSMul Γ X]
  [LocallyCompactSpace X] [LocallyCompactSpace Y] [T2Space Y] [ProperSMul Γ Y]

/-- The actual image of a compact family on one cocompact source piece. -/
def familyMap (S : CocompactPiece Γ X) (h : C(P × S.toInvariantSubset, Y))
    (he : ∀ (t : P) (g : Γ) (x : S.toInvariantSubset), h (t, g • x) = g • h (t, x)) :
    CocompactPiece Γ Y where
  carrier := Set.range h
  smul_mem g _ := by
    rintro ⟨⟨t, x⟩, rfl⟩
    exact ⟨(t, g • x), he t g x⟩
  isClosed_carrier := by
    let := S.locallyCompact
    let := S.compactSpace_orbit
    exact (isProperMap_compactEquivariantFamily h he).isClosed_range
  isCompact_image := by
    let := S.locallyCompact
    let := S.compactSpace_orbit
    exact isCompact_quotient_image_compactEquivariantFamily h he

end CocompactPiece

namespace EquivariantHomotopy

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [MulAction Γ X] [MulAction Γ Y] [ContinuousConstSMul Γ X]
  [LocallyCompactSpace X] [LocallyCompactSpace Y] [T2Space Y] [ProperSMul Γ Y]
  {f₀ f₁ : EquivariantMap Γ X Y}

/-- Restrict a whole equivariant homotopy to a source cocompact piece. -/
def pieceFamily (H : EquivariantHomotopy f₀ f₁) (S : CocompactPiece Γ X) :
    C(unitInterval × S.toInvariantSubset, Y) where
  toFun p := H (p.1, p.2.val)
  continuous_toFun := H.continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

omit [TopologicalSpace Γ] [DiscreteTopology Γ] [ContinuousConstSMul Γ X]
  [LocallyCompactSpace X] [LocallyCompactSpace Y] [T2Space Y] [ProperSMul Γ Y] in
theorem pieceFamily_equivariant (H : EquivariantHomotopy f₀ f₁)
    (S : CocompactPiece Γ X) (t : unitInterval) (g : Γ) (x : S.toInvariantSubset) :
    pieceFamily H S (t, g • x) = g • pieceFamily H S (t, x) := H.prop t g x

theorem pieceFamily_isProperMap (H : EquivariantHomotopy f₀ f₁) (S : CocompactPiece Γ X) :
    IsProperMap (pieceFamily H S) := by
  let := S.locallyCompact
  let := S.compactSpace_orbit
  exact isProperMap_compactEquivariantFamily (pieceFamily H S) (pieceFamily_equivariant H S)

/-- One closed cocompact piece contains every time slice of the restricted
homotopy; its carrier is exactly the whole homotopy image. -/
def imagePiece (H : EquivariantHomotopy f₀ f₁) (S : CocompactPiece Γ X) :
    CocompactPiece Γ Y :=
  S.familyMap (pieceFamily H S) (pieceFamily_equivariant H S)

theorem mem_imagePiece (H : EquivariantHomotopy f₀ f₁) (S : CocompactPiece Γ X)
    (t : unitInterval) (x : S.toInvariantSubset) : H (t, x.val) ∈ imagePiece H S :=
  ⟨(t, x), rfl⟩

theorem map_atTime_le_imagePiece (H : EquivariantHomotopy f₀ f₁)
    (S : CocompactPiece Γ X) (t : unitInterval) :
    CocompactPiece.map (H.atTime t) S ≤ imagePiece H S := by
  rintro y ⟨x, hx, rfl⟩
  exact mem_imagePiece H S t ⟨x, hx⟩

/-- The joint homotopy map with its closed cocompact image as codomain. -/
def pieceFamilyToImage (H : EquivariantHomotopy f₀ f₁) (S : CocompactPiece Γ X) :
    C(unitInterval × S.toInvariantSubset, (imagePiece H S).toInvariantSubset) where
  toFun p := ⟨H (p.1, p.2.val), mem_imagePiece H S p.1 p.2⟩
  continuous_toFun := (pieceFamily H S).continuous.subtype_mk _

@[simp] theorem pieceFamilyToImage_coe (H : EquivariantHomotopy f₀ f₁)
    (S : CocompactPiece Γ X) (p : unitInterval × S.toInvariantSubset) :
    (pieceFamilyToImage H S p : Y) = H (p.1, p.2.val) := rfl

theorem pieceFamilyToImage_isProperMap (H : EquivariantHomotopy f₀ f₁)
    (S : CocompactPiece Γ X) : IsProperMap (pieceFamilyToImage H S) := by
  exact isProperMap_of_comp_of_inj (pieceFamilyToImage H S).continuous continuous_subtype_val
    (pieceFamily_isProperMap H S) Subtype.val_injective

theorem pieceFamilyToImage_equivariant (H : EquivariantHomotopy f₀ f₁)
    (S : CocompactPiece Γ X) (t : unitInterval) (g : Γ) (x : S.toInvariantSubset) :
    pieceFamilyToImage H S (t, g • x) = g • pieceFamilyToImage H S (t, x) :=
  Subtype.ext (H.prop t g x)

theorem map_zero_le_imagePiece (H : EquivariantHomotopy f₀ f₁)
    (S : CocompactPiece Γ X) : CocompactPiece.map f₀ S ≤ imagePiece H S := by
  simpa only [at_zero] using map_atTime_le_imagePiece H S 0

theorem map_one_le_imagePiece (H : EquivariantHomotopy f₀ f₁)
    (S : CocompactPiece Γ X) : CocompactPiece.map f₁ S ≤ imagePiece H S := by
  simpa only [at_one] using map_atTime_le_imagePiece H S 1

/-- The actual equivariant homotopy between the two restricted maps into
one closed cocompact target piece. -/
def restrictToImage (H : EquivariantHomotopy f₀ f₁) (S : CocompactPiece Γ X) :
    EquivariantHomotopy
      (CocompactPiece.mapRestrictionTo f₀ S (imagePiece H S) (map_zero_le_imagePiece H S))
      (CocompactPiece.mapRestrictionTo f₁ S (imagePiece H S) (map_one_le_imagePiece H S)) where
  toHomotopy :=
    { toFun := pieceFamilyToImage H S
      continuous_toFun := (pieceFamilyToImage H S).continuous
      map_zero_left x := Subtype.ext (H.apply_zero x.val)
      map_one_left x := Subtype.ext (H.apply_one x.val) }
  prop' := pieceFamilyToImage_equivariant H S

theorem restrictToImage_isProperMap (H : EquivariantHomotopy f₀ f₁)
    (S : CocompactPiece Γ X) : IsProperMap (restrictToImage H S) :=
  pieceFamilyToImage_isProperMap H S

end EquivariantHomotopy
end BC4lean.ProperActions
