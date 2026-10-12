import BC4lean.OddFredholmFullIntervalIndex

/-! # Actual module-isomorphism invariance of the stabilized odd index -/

noncomputable section
namespace BC4lean.KKTheory
open scoped CStarAlgebra

variable {B E N : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup N] [NormedSpace ℂ N] [SMul Bᵐᵒᵖ N] [CStarModule Bᵐᵒᵖ N] [CompleteSpace N]

def oddFredholmEquivSelfAdjoint (u : HilbertModuleEquiv B E N)
    (F : selfAdjoint (AdjointableMap B E E)) : selfAdjoint (AdjointableMap B N N) :=
  ⟨u.transport (F : AdjointableMap B E E), F.property.map u.transportStarAlgEquiv.toStarAlgHom⟩

omit [CompleteSpace E] [CompleteSpace N] in
theorem oddFredholmEquivSelfAdjoint_square_compact (u : HilbertModuleEquiv B E N)
    (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) * (F : AdjointableMap B E E) - 1)) :
    IsModuleCompact ((oddFredholmEquivSelfAdjoint u F : AdjointableMap B N N) *
      (oddFredholmEquivSelfAdjoint u F : AdjointableMap B N N) - 1) := by
  have h := u.transportMap_isModuleCompact u hF
  change IsModuleCompact (u.transport
    ((F : AdjointableMap B E E) * (F : AdjointableMap B E E) - 1)) at h
  simpa only [oddFredholmEquivSelfAdjoint, HilbertModuleEquiv.transport_sub,
    HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_one] using h

/-- A genuine whole module unitary preserves the actual stabilized index.
Different selected absorption choices are compared by the proved doubled path. -/
theorem oddFredholmStabilizedIndex_equiv
    (u : HilbertModuleEquiv B E N) (hE : IsCountablyGeneratedModule B E)
    (hN : IsCountablyGeneratedModule B N) (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) * (F : AdjointableMap B E E) - 1)) :
    oddFredholmStabilizedIndex hE F hF =
      oddFredholmStabilizedIndex hN (oddFredholmEquivSelfAdjoint u F)
        (oddFredholmEquivSelfAdjoint_square_compact u F hF) := by
  let a := (u.sum (HilbertModuleEquiv.refl (B := B) (E := StandardCountableHilbertModule B))).trans
    (standardModuleStabilization hN)
  rw [oddFredholmStabilizedIndex_eq_absorption hE F hF a]
  unfold oddFredholmAbsorbedIndex oddFredholmStabilizedIndex
  have he : oddFredholmTransportSelfAdjoint a
      ⟨oddFredholmStandardAugmentedOperator F, oddFredholmStandardAugmentedOperator_isSelfAdjoint F⟩ =
      oddFredholmStandardStabilizedOperator hN (oddFredholmEquivSelfAdjoint u F) := by
    apply Subtype.ext
    change a.transport (sumMap (F : AdjointableMap B E E) 1) = _
    rw [show a = (u.sum (HilbertModuleEquiv.refl (B := B)
      (E := StandardCountableHilbertModule B))).trans (standardModuleStabilization hN) from rfl,
      oddFredholmTransport_trans, oddFredholmTransport_sum, HilbertModuleEquiv.transport_one]
    rfl
  simp only [he]

/-- The intertwining equation can be used directly with specified endpoint
operators on different actual module carriers. -/
theorem oddFredholmStabilizedIndex_intertwine
    (u : HilbertModuleEquiv B E N) (hE : IsCountablyGeneratedModule B E)
    (hN : IsCountablyGeneratedModule B N) (F : selfAdjoint (AdjointableMap B E E))
    (G : selfAdjoint (AdjointableMap B N N))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) * (F : AdjointableMap B E E) - 1))
    (hG : IsModuleCompact ((G : AdjointableMap B N N) * (G : AdjointableMap B N N) - 1))
    (h : ∀ x, u ((F : AdjointableMap B E E) x) = (G : AdjointableMap B N N) (u x)) :
    oddFredholmStabilizedIndex hE F hF = oddFredholmStabilizedIndex hN G hG := by
  have he : oddFredholmEquivSelfAdjoint u F = G := by
    apply Subtype.ext
    ext x
    rw [oddFredholmEquivSelfAdjoint, HilbertModuleEquiv.transport_apply, h,
      HilbertModuleEquiv.apply_symm_apply]
  simpa only [he] using oddFredholmStabilizedIndex_equiv u hE hN F hF

end BC4lean.KKTheory
