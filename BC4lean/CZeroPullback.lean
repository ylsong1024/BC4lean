import BC4lean.CZeroAlgebra
import BC4lean.InvariantSubspaceMaps
import Mathlib.Topology.Maps.Proper.Basic

/-! # Equivariant pullback and closed-piece restriction on `C₀`

Proper maps preserve vanishing at infinity. Closed inclusions of invariant
cocompact pieces are proper, so their actual restriction homomorphisms compose
contravariantly and commute with the induced group actions.
-/

noncomputable section

open scoped ZeroAtInfty
open Topology

namespace BC4lean.KKTheory.CZero

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]

/-- A proper map as a cocompact continuous map, without separation assumptions. -/
def cocompactMapOfProper (f : X → Y) (hf : IsProperMap f) : CocompactMap X Y where
  toFun := f
  continuous_toFun := hf.continuous
  cocompact_tendsto' := CocompactMap.tendsto_of_forall_preimage
    (fun _ hK => hf.isCompact_preimage hK)

/-- The actual pullback homomorphism induced by a proper map. -/
def properPullback (f : X → Y) (hf : IsProperMap f) :
    C₀(Y, ℂ) →⋆ₙₐ[ℂ] C₀(X, ℂ) :=
  pullback (cocompactMapOfProper f hf)

@[simp] theorem properPullback_apply (f : X → Y) (hf : IsProperMap f)
    (a : C₀(Y, ℂ)) (x : X) : properPullback f hf a x = a (f x) := rfl

@[simp] theorem properPullback_id :
    properPullback (id : X → X) isProperMap_id = NonUnitalStarAlgHom.id ℂ C₀(X, ℂ) := by
  ext a x
  rfl

@[simp] theorem properPullback_comp (g : Y → Z) (f : X → Y)
    (hg : IsProperMap g) (hf : IsProperMap f) :
    properPullback (g ∘ f) (hg.comp hf) = (properPullback f hf).comp (properPullback g hg) := by
  ext a x
  rfl

variable {Γ : Type*} [Group Γ] [MulAction Γ X] [MulAction Γ Y]
  [ContinuousConstSMul Γ X] [ContinuousConstSMul Γ Y]

/-- A proper equivariant map gives an equivariant algebra homomorphism. -/
theorem properPullback_equivariant (f : BC4lean.ProperActions.EquivariantMap Γ X Y)
    (hf : IsProperMap f) (g : Γ) (a : C₀(Y, ℂ)) :
    properPullback f hf ((action Γ).automorphism g a) =
      (action Γ).automorphism g (properPullback f hf a) := by
  ext x
  change a (g⁻¹ • f x) = a (f (g⁻¹ • x))
  rw [f.map_smul]

end BC4lean.KKTheory.CZero

namespace BC4lean.ProperActions.CocompactPiece

variable {Γ X : Type*} [Group Γ] [TopologicalSpace X] [MulAction Γ X]

/-- The inclusion of two closed invariant pieces is a closed embedding. -/
theorem inclusionMap_isClosedEmbedding {S T : CocompactPiece Γ X} (h : S ≤ T) :
    IsClosedEmbedding (inclusionMap h) := by
  apply IsClosedEmbedding.of_comp
    (IsEmbedding.subtypeVal : IsEmbedding (Subtype.val : T.toInvariantSubset → X))
  exact S.isClosed_carrier.isClosedEmbedding_subtypeVal

/-- The inclusion used by the cocompact indexing system is proper. -/
theorem inclusionMap_isProperMap {S T : CocompactPiece Γ X} (h : S ≤ T) :
    IsProperMap (inclusionMap h) := (inclusionMap_isClosedEmbedding h).isProperMap

end BC4lean.ProperActions.CocompactPiece

namespace BC4lean.KKTheory.CZero

open BC4lean.ProperActions

variable {Γ X : Type*} [Group Γ] [TopologicalSpace X] [MulAction Γ X]

/-- Restriction from a larger closed cocompact piece to a smaller one. -/
def pieceRestriction {S T : CocompactPiece Γ X} (h : S ≤ T) :
    C₀(T.toInvariantSubset, ℂ) →⋆ₙₐ[ℂ] C₀(S.toInvariantSubset, ℂ) :=
  properPullback (CocompactPiece.inclusionMap h) (CocompactPiece.inclusionMap_isProperMap h)

@[simp] theorem pieceRestriction_apply {S T : CocompactPiece Γ X} (h : S ≤ T)
    (a : C₀(T.toInvariantSubset, ℂ)) (x : S.toInvariantSubset) :
    pieceRestriction h a x = a (CocompactPiece.inclusionMap h x) := rfl

@[simp] theorem pieceRestriction_refl (S : CocompactPiece Γ X) :
    pieceRestriction (le_refl S) = NonUnitalStarAlgHom.id ℂ C₀(S.toInvariantSubset, ℂ) := by
  ext a x
  rfl

@[simp] theorem pieceRestriction_comp {S T U : CocompactPiece Γ X}
    (hST : S ≤ T) (hTU : T ≤ U) :
    (pieceRestriction hST).comp (pieceRestriction hTU) = pieceRestriction (hST.trans hTU) := by
  ext a x
  rfl

/-- Piece restriction commutes with the genuine `C₀` action. -/
theorem pieceRestriction_equivariant [ContinuousConstSMul Γ X]
    {S T : CocompactPiece Γ X} (h : S ≤ T) (g : Γ) (a : C₀(T.toInvariantSubset, ℂ)) :
    pieceRestriction h ((action Γ).automorphism g a) =
      (action Γ).automorphism g (pieceRestriction h a) :=
  properPullback_equivariant (CocompactPiece.inclusionMap h)
    (CocompactPiece.inclusionMap_isProperMap h) g a

end BC4lean.KKTheory.CZero
