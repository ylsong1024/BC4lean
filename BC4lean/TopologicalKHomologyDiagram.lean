import BC4lean.CZeroPullback
import BC4lean.CZeroSeparability
import BC4lean.GroupUniverseParityFunctoriality

/-! # The actual equivariant K-homology groups and closed-piece transition maps

Both parities are the full Chapter 5 Kasparov groups, with the induced action on
`C₀(S, ℂ)` and trivial action on the scalar coefficient. The module universe is
the space universe, which contains all the source algebra carriers introduced
by the functoriality construction. No KK conclusion is an input hypothesis.
-/

noncomputable section
open scoped ZeroAtInfty ComplexOrder
open Topology TopologicalSpace

universe uΓ uX
namespace BC4lean.TopologicalKHomology
open ProperActions KKTheory KKTheory.GroupUniverseParityGroup
open KKTheory.GroupUniverseParityFunctoriality

variable {Γ : Type uΓ} {X : Type uX} [Group Γ] [TopologicalSpace X]
  [MulAction Γ X] [ContinuousConstSMul Γ X]

/-- The actual full equivariant K-homology group of a space. -/
abbrev spaceGroup (p : Bool) (Γ : Type uΓ) [Group Γ] (X : Type uX)
    [TopologicalSpace X] [MulAction Γ X] [ContinuousConstSMul Γ X] :=
  KKParityGroup.{uΓ,uX,0,uX} p (CZero.action Γ (X := X))
    (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)

/-- Equivariant K-homology of a closed cocompact piece, in either parity. -/
abbrev pieceGroup (p : Bool) (S : CocompactPiece Γ X) :=
  spaceGroup p Γ S.toInvariantSubset

instance piece_secondCountable [SecondCountableTopology X] (S : CocompactPiece Γ X) :
    SecondCountableTopology S.toInvariantSubset :=
  (IsEmbedding.subtypeVal : IsEmbedding (Subtype.val : S.toInvariantSubset → X)).secondCountableTopology

section Transitions
variable [Countable Γ] [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]

local instance piece_locallyCompact (S : CocompactPiece Γ X) :
    LocallyCompactSpace S.toInvariantSubset := S.locallyCompact

local instance piece_algebra_separable (S : CocompactPiece Γ X) :
    SeparableSpace C₀(S.toInvariantSubset, ℂ) := cZero_separableSpace

/-- Closed inclusion induces the forward map on K-homology by actual source
pullback along restriction of functions. -/
def transition (p : Bool) {S T : CocompactPiece Γ X} (h : S ≤ T) :
    pieceGroup p S →+ pieceGroup p T :=
  sourcePullbackHom.{uΓ,uX,uX,0,uX} p (CZero.pieceRestriction h)
    (CZero.pieceRestriction_equivariant h)

/-- Transition along identity inclusion is the identity. -/
@[simp] theorem transition_refl (p : Bool) (S : CocompactPiece Γ X)
    (x : pieceGroup p S) : transition p (le_refl S) x = x := by
  change sourcePullback.{uΓ,uX,uX,0,uX} p (CZero.pieceRestriction (le_refl S)) _ x = x
  simpa only [CZero.pieceRestriction_refl] using sourcePullback_id.{uΓ,uX,0,uX} p x

/-- Transitions compose in the direction of the inclusions. -/
theorem transition_trans (p : Bool) {S T U : CocompactPiece Γ X}
    (hST : S ≤ T) (hTU : T ≤ U) (x : pieceGroup p S) :
    transition p hTU (transition p hST x) = transition p (hST.trans hTU) x := by
  change sourcePullback.{uΓ,uX,uX,0,uX} p (CZero.pieceRestriction hTU) _
    (sourcePullback.{uΓ,uX,uX,0,uX} p (CZero.pieceRestriction hST) _ x) =
    sourcePullback.{uΓ,uX,uX,0,uX} p (CZero.pieceRestriction (hST.trans hTU)) _ x
  rw [sourcePullback_comp.{uΓ,uX,uX,uX,0,uX} p]
  congr 1

end Transitions
end BC4lean.TopologicalKHomology
