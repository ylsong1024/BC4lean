import BC4lean.EquivariantMaps
import Mathlib.Topology.Maps.OpenQuotient

/-! # Closed invariant cocompact pieces of a given proper space

The indexing construction below is conditional on the ambient space. It does
not construct a universal proper space or select a locally compact model.
-/
namespace BC4lean.ProperActions
open Topology

variable {Γ X : Type*} [Group Γ] [TopologicalSpace X] [MulAction Γ X]

/-- An invariant subset with the induced topology and action. -/
structure InvariantSubset (Γ X : Type*) [Group Γ] [MulAction Γ X] where
  carrier : Set X
  smul_mem : ∀ (g : Γ) {x : X}, x ∈ carrier → g • x ∈ carrier

namespace InvariantSubset
instance instSetLike : SetLike (InvariantSubset Γ X) X where
  coe := carrier
  coe_injective := by rintro ⟨s, hs⟩ ⟨t, ht⟩ rfl; rfl

instance instPartialOrder : PartialOrder (InvariantSubset Γ X) := .ofSetLike _ _

instance instMulAction (s : InvariantSubset Γ X) : MulAction Γ s where
  smul g x := ⟨g • x.val, s.smul_mem g x.property⟩
  one_smul x := Subtype.ext (one_smul Γ x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

omit [TopologicalSpace X] in
@[simp] theorem coe_smul (s : InvariantSubset Γ X) (g : Γ) (x : s) :
    ((g • x : s) : X) = g • (x : X) := rfl

instance instContinuousConstSMul (s : InvariantSubset Γ X) [ContinuousConstSMul Γ X] :
    ContinuousConstSMul Γ s where
  continuous_const_smul g := (continuous_const_smul g).subtype_map (fun _ hx => s.smul_mem g hx)

/-- Inclusion of an invariant subset is equivariant. -/
def inclusion (s : InvariantSubset Γ X) : EquivariantMap Γ s X where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val
  map_smul' _ _ := rfl

/-- The map from the intrinsic orbit space to the ambient orbit space. -/
def orbitInclusion (s : InvariantSubset Γ X) :
    Quotient (MulAction.orbitRel Γ s) → Quotient (MulAction.orbitRel Γ X) :=
  Quotient.map Subtype.val (by
    intro a b h
    obtain ⟨g, hg⟩ := h
    exact ⟨g, congrArg Subtype.val hg⟩)

omit [TopologicalSpace X] in
theorem orbitInclusion_injective (s : InvariantSubset Γ X) :
    Function.Injective s.orbitInclusion := by
  intro a b
  induction a using Quotient.inductionOn with | _ a =>
    induction b using Quotient.inductionOn with | _ b =>
      intro h
      apply Quotient.sound
      obtain ⟨g, hg⟩ := Quotient.exact h
      exact ⟨g, Subtype.ext hg⟩

/-- An invariant subspace's intrinsic orbit topology is its ambient subspace topology. -/
theorem orbitInclusion_isEmbedding (s : InvariantSubset Γ X)
    [ContinuousConstSMul Γ X] : IsEmbedding s.orbitInclusion := by
  apply isEmbedding_of_isOpenQuotientMap_of_isInducing
    (Subtype.val : s → X) s.orbitInclusion
    (Quotient.mk (MulAction.orbitRel Γ s)) (Quotient.mk (MulAction.orbitRel Γ X))
    rfl IsInducing.subtypeVal isQuotientMap_quot_mk
    MulAction.isOpenQuotientMap_quotientMk s.orbitInclusion_injective
  rintro x ⟨_, ⟨y, rfl⟩, h⟩
  obtain ⟨g, hg⟩ := Quotient.exact h.symm
  exact ⟨⟨x, hg ▸ s.smul_mem g y.property⟩, rfl⟩

omit [TopologicalSpace X] in
theorem range_orbitInclusion (s : InvariantSubset Γ X) :
    Set.range s.orbitInclusion = Quotient.mk (MulAction.orbitRel Γ X) '' (s : Set X) := by
  ext q
  constructor
  · rintro ⟨a, rfl⟩
    induction a using Quotient.inductionOn with | _ a => exact ⟨a, a.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Quotient.mk _ ⟨x, hx⟩, rfl⟩

/-- Compactness in the ambient quotient is equivalent to compactness of the intrinsic quotient. -/
theorem compactSpace_orbit_iff (s : InvariantSubset Γ X) [ContinuousConstSMul Γ X] :
    CompactSpace (Quotient (MulAction.orbitRel Γ s)) ↔
      IsCompact (Quotient.mk (MulAction.orbitRel Γ X) '' (s : Set X)) := by
  rw [← s.range_orbitInclusion, ← Set.image_univ,
    ← s.orbitInclusion_isEmbedding.isCompact_iff, isCompact_univ_iff]

end InvariantSubset

/-- Closed invariant subsets with compact quotient, encoded through the ambient orbit space. -/
structure CocompactPiece (Γ X : Type*) [Group Γ] [TopologicalSpace X] [MulAction Γ X]
    extends InvariantSubset Γ X where
  isClosed_carrier : IsClosed carrier
  isCompact_image : IsCompact (Quotient.mk (MulAction.orbitRel Γ X) '' carrier)

namespace CocompactPiece
instance instSetLike : SetLike (CocompactPiece Γ X) X where
  coe s := s.carrier
  coe_injective := by rintro ⟨⟨s, hs⟩, hc, hk⟩ ⟨⟨t, ht⟩, hd, hl⟩ rfl; rfl
instance instPartialOrder : PartialOrder (CocompactPiece Γ X) := .ofSetLike _ _

/-- The empty piece ensures that the indexing type is nonempty. -/
def empty : CocompactPiece Γ X where
  carrier := ∅
  smul_mem _ _ hx := False.elim hx
  isClosed_carrier := isClosed_empty
  isCompact_image := by simp

/-- Finite unions provide upper bounds in the cocompact indexing system. -/
def union (s t : CocompactPiece Γ X) : CocompactPiece Γ X where
  carrier := s.carrier ∪ t.carrier
  smul_mem g _ hx := hx.elim (fun h => Or.inl (s.smul_mem g h))
    (fun h => Or.inr (t.smul_mem g h))
  isClosed_carrier := s.isClosed_carrier.union t.isClosed_carrier
  isCompact_image := by
    rw [Set.image_union]
    exact s.isCompact_image.union t.isCompact_image

theorem le_union_left (s t : CocompactPiece Γ X) : s ≤ s.union t := Set.subset_union_left
theorem le_union_right (s t : CocompactPiece Γ X) : t ≤ s.union t := Set.subset_union_right

theorem directed : Directed (· ≤ · : CocompactPiece Γ X → CocompactPiece Γ X → Prop)
    (fun s => s) := fun s t => ⟨s.union t, le_union_left s t, le_union_right s t⟩

/-- Every piece has compact intrinsic orbit space. -/
theorem compactSpace_orbit (s : CocompactPiece Γ X) [ContinuousConstSMul Γ X] :
    CompactSpace (Quotient (MulAction.orbitRel Γ s.toInvariantSubset)) :=
  s.toInvariantSubset.compactSpace_orbit_iff.mpr s.isCompact_image

/-- Closed pieces of a locally compact ambient space are locally compact. -/
theorem locallyCompact (s : CocompactPiece Γ X) [LocallyCompactSpace X] :
    LocallyCompactSpace s.toInvariantSubset := s.isClosed_carrier.locallyCompactSpace

/-- Compact subsets generate closed cocompact invariant pieces in a proper space. -/
def ofCompact [TopologicalSpace Γ] [ProperSMul Γ X]
    (K : Set X) (hK : IsCompact K) : CocompactPiece Γ X where
  carrier := Quotient.mk (MulAction.orbitRel Γ X) ⁻¹'
    (Quotient.mk (MulAction.orbitRel Γ X) '' K)
  smul_mem g x hx := by
    change Quotient.mk (MulAction.orbitRel Γ X) (g • x) ∈
      Quotient.mk (MulAction.orbitRel Γ X) '' K
    have he (x : X) : Quotient.mk (MulAction.orbitRel Γ X) (g • x) =
        Quotient.mk (MulAction.orbitRel Γ X) x := Quotient.sound ⟨g, rfl⟩
    rw [he]
    exact hx
  isClosed_carrier := (hK.image (show Continuous (Quotient.mk (MulAction.orbitRel Γ X)) from continuous_quot_mk)).isClosed.preimage continuous_quot_mk
  isCompact_image := by
    rw [Set.image_preimage_eq _ Quotient.mk_surjective]
    exact hK.image continuous_quot_mk

theorem subset_ofCompact [TopologicalSpace Γ] [ProperSMul Γ X]
    (K : Set X) (hK : IsCompact K) : K ⊆ (ofCompact (Γ := Γ) K hK : Set X) :=
  fun x hx => ⟨x, hx, rfl⟩

/-- Every point belongs to a closed cocompact invariant piece. -/
theorem covers [TopologicalSpace Γ] [ProperSMul Γ X] (x : X) :
    ∃ s : CocompactPiece Γ X, x ∈ s :=
  ⟨ofCompact {x} isCompact_singleton,
    subset_ofCompact (Γ := Γ) {x} isCompact_singleton (Set.mem_singleton x)⟩

end CocompactPiece
end BC4lean.ProperActions
