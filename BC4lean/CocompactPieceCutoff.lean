import BC4lean.ProperCutoffFunction

/-! # Cutoff functions on actual cocompact pieces

Closed invariant subspaces of a proper discrete action inherit properness:
their compact transporters are contained in compact transporters of the
ambient space. Each Chapter 6 cocompact piece therefore has the actual cutoff
function supplied by the proper cocompact cutoff construction.
-/

noncomputable section

namespace BC4lean.ProperActions

open scoped Pointwise

variable {Γ X : Type*} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
  [TopologicalSpace X] [MulAction Γ X] [LocallyCompactSpace X] [T2Space X]
  [ProperSMul Γ X]

namespace InvariantSubset

/-- A closed invariant subspace of the ambient proper action is proper. -/
theorem proper_of_isClosed (S : InvariantSubset Γ X) (hS : IsClosed (S : Set X)) :
    ProperSMul Γ S := by
  let : LocallyCompactSpace S := hS.locallyCompactSpace
  let : ContinuousSMul Γ S :=
    ⟨continuous_prod_of_discrete_left.mpr (fun g => continuous_const_smul g)⟩
  apply proper_iff_finite_transporters.mpr
  intro K L hK hL
  apply (finite_transporter (Γ := Γ)
    (hK.image (continuous_subtype_val : Continuous (Subtype.val : S → X)))
    (hL.image (continuous_subtype_val : Continuous (Subtype.val : S → X)))).subset
  intro g hg
  obtain ⟨y, hy, hyL⟩ := hg
  obtain ⟨x, hx, hxy⟩ := hy
  refine ⟨(y : X), ?_, ⟨y, hyL, rfl⟩⟩
  refine ⟨(x : X), ⟨x, hx, rfl⟩, ?_⟩
  exact congrArg (fun z : S => (z : X)) hxy

end InvariantSubset

namespace CocompactPiece

/-- The action on an actual closed cocompact piece inherits ambient properness. -/
theorem proper (S : CocompactPiece Γ X) : ProperSMul Γ S.toInvariantSubset :=
  S.toInvariantSubset.proper_of_isClosed S.isClosed_carrier

instance instProperSMul (S : CocompactPiece Γ X) : ProperSMul Γ S.toInvariantSubset :=
  S.proper

/-- Every actual cocompact piece admits a nonnegative compactly supported
continuous cutoff function with the normalized finite orbit sum. -/
theorem exists_cutoffFunction (S : CocompactPiece Γ X) :
    Nonempty (Cutoff.CutoffFunction Γ S.toInvariantSubset) := by
  let : LocallyCompactSpace S.toInvariantSubset := S.locallyCompact
  let : CompactSpace (Quotient (MulAction.orbitRel Γ S.toInvariantSubset)) :=
    S.compactSpace_orbit
  exact Cutoff.exists_cutoffFunction (Γ := Γ) (X := S.toInvariantSubset)

end CocompactPiece
end BC4lean.ProperActions
