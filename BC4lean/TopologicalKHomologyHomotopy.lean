import BC4lean.TopologicalKHomologyMaps
import BC4lean.CocompactPieceMapHomotopy
import BC4lean.CZeroHomotopy
import BC4lean.KasparovSourceHomotopyParity
import BC4lean.LabeledTelescopeCW
import BC4lean.ProbabilityUniversalTarget

/-! # Homotopy and universal proper-model independence

The actual image of a homotopy on one cocompact piece controls all parameters.
It supplies a proper C₀ homotopy; full KK source homotopy invariance then proves
equality of the induced colimit maps. Chapter 4's proved CW uniqueness theorem
provides the comparison equivalence for universal proper models.
-/

noncomputable section
open Topology TopologicalSpace
open scoped ZeroAtInfty ComplexOrder
universe uΓ u

namespace BC4lean.TopologicalKHomology
open ProperActions KKTheory KKTheory.GroupUniverseParityFunctoriality

section General
variable {Γ : Type uΓ} [Group Γ] [Countable Γ]
  {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [MulAction Γ X] [MulAction Γ Y] [ContinuousConstSMul Γ X] [ContinuousConstSMul Γ Y]
  [LocallyCompactSpace X] [LocallyCompactSpace Y] [T2Space X] [T2Space Y]
  [SecondCountableTopology X] [SecondCountableTopology Y]

local instance homotopy_cZero_separable (W : Type u) [TopologicalSpace W] [T2Space W]
    [LocallyCompactSpace W] [SecondCountableTopology W] : SeparableSpace C₀(W, ℂ) :=
  cZero_separableSpace

/-- Proper equivariant homotopies induce equal maps on actual full K-homology. -/
theorem properPushforward_homotopy (p : Bool) {f₀ f₁ : EquivariantMap Γ X Y}
    (H : EquivariantHomotopy f₀ f₁) (hH : IsProperMap H)
    (hf₀ : IsProperMap f₀) (hf₁ : IsProperMap f₁) :
    properPushforward p f₀ hf₀ = properPushforward p f₁ hf₁ := by
  unfold properPushforward
  exact sourcePullbackHom_homotopy p (CZero.properHomotopyPullback H.toHomotopy hH)
    (CZero.properHomotopyPullback_equivariant H hH)
    (CZero.properPullback_equivariant f₀ hf₀)
    (CZero.properPullback_equivariant f₁ hf₁)

section ProperSpaces
variable [TopologicalSpace Γ] [DiscreteTopology Γ] [ProperSMul Γ X] [ProperSMul Γ Y]

local instance homotopy_piece_locallyCompact (W : Type u) [TopologicalSpace W] [MulAction Γ W]
    [LocallyCompactSpace W] (S : CocompactPiece Γ W) :
    LocallyCompactSpace S.toInvariantSubset := S.locallyCompact

omit [ProperSMul Γ X] in
/-- Ambient homotopies give equal colimit maps, without assuming they are globally proper. -/
theorem pushforward_homotopy (p : Bool) {f₀ f₁ : EquivariantMap Γ X Y}
    (H : EquivariantHomotopy f₀ f₁) : pushforward p f₀ = pushforward p f₁ := by
  apply (diagram p).hom_ext
  intro S
  ext x
  change pieceGroup p S at x
  change pushforward p f₀ (ofPiece p S x) = pushforward p f₁ (ofPiece p S x)
  rw [pushforward_ofPiece_bounded p f₀ S (H.imagePiece S) (H.map_zero_le_imagePiece S),
    pushforward_ofPiece_bounded p f₁ S (H.imagePiece S) (H.map_one_le_imagePiece S)]
  apply congrArg (ofPiece p (H.imagePiece S))
  exact congrArg (fun k : pieceGroup p S →+ pieceGroup p (H.imagePiece S) => k x)
    (properPushforward_homotopy p (H.restrictToImage S) (H.restrictToImage_isProperMap S)
      (CocompactPiece.mapRestrictionTo_isProperMap f₀ S _ _)
      (CocompactPiece.mapRestrictionTo_isProperMap f₁ S _ _))

omit [ProperSMul Γ X] in
/-- Existence of an actual equivariant homotopy is sufficient for equality. -/
theorem pushforward_homotopic (p : Bool) {f₀ f₁ : EquivariantMap Γ X Y}
    (h : EquivariantlyHomotopic f₀ f₁) : pushforward p f₀ = pushforward p f₁ := by
  obtain ⟨H⟩ := h
  exact pushforward_homotopy p H

/-- An equivariant homotopy equivalence induces an additive equivalence of the
constructed topological-side groups, with the actual inverse comparison map. -/
def homotopyEquiv (p : Bool) (e : EquivariantHomotopyEquiv Γ X Y) :
    group (Γ := Γ) (X := X) p ≃+ group (Γ := Γ) (X := Y) p where
  toFun := pushforward p e.toMap
  invFun := pushforward p e.invMap
  map_add' := (pushforward p e.toMap).map_add
  left_inv x := by
    have he := congrArg (fun k : group (Γ := Γ) (X := X) p →+
      group (Γ := Γ) (X := X) p => k x) (pushforward_comp p e.invMap e.toMap)
    simpa only [AddMonoidHom.comp_apply, pushforward_homotopic p e.left_inv,
      pushforward_id, AddMonoidHom.id_apply] using he
  right_inv x := by
    have he := congrArg (fun k : group (Γ := Γ) (X := Y) p →+
      group (Γ := Γ) (X := Y) p => k x) (pushforward_comp p e.toMap e.invMap)
    simpa only [AddMonoidHom.comp_apply, pushforward_homotopic p e.right_inv,
      pushforward_id, AddMonoidHom.id_apply] using he

end ProperSpaces
end General

section UniversalModels
variable {Γ : Type u} [Group Γ] [Countable Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
  {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [MulAction Γ X] [MulAction Γ Y] [ContinuousConstSMul Γ X] [ContinuousConstSMul Γ Y]
  [LocallyCompactSpace X] [LocallyCompactSpace Y] [T2Space X] [T2Space Y]
  [SecondCountableTopology X] [SecondCountableTopology Y]

/-- Independence of genuine locally compact second-countable universal proper
CW models, obtained from the fixed-point criterion rather than a supplied
K-homology equivalence. -/
def universalModelEquiv (p : Bool)
    (cX : EquivariantCWComplex (topologicalAction Γ X))
    (cY : EquivariantCWComplex (topologicalAction Γ Y))
    (hX : FixedPointCriterion Γ X) (hY : FixedPointCriterion Γ Y) :
    group (Γ := Γ) (X := X) p ≃+ group (Γ := Γ) (X := Y) p := by
  let := cX.proper
  let := cY.proper
  exact homotopyEquiv p (Classical.choice (cX.fixedPointCriterion_unique cY hX hY))

/-- Every comparison map into a universal CW model induces the same map. -/
theorem universalComparison_unique (p : Bool)
    (cX : EquivariantCWComplex (topologicalAction Γ X))
    (cY : EquivariantCWComplex (topologicalAction Γ Y))
    (hY : FixedPointCriterion Γ Y) (f g : EquivariantMap Γ X Y) :
    letI := cX.proper
    letI := cY.proper
    pushforward p f = pushforward p g := by
  let := cX.proper
  let := cY.proper
  exact pushforward_homotopic p ((cX.homotopyTerminal hY).2 f g)

/-- The canonical topological group uses Chapter 4's actual geometric telescope. -/
abbrev topologicalGroup (p : Bool) (Γ : Type u) [Group Γ] [Countable Γ]
    [TopologicalSpace Γ] [DiscreteTopology Γ] :=
  group (Γ := Γ) (X := LabeledOrbitTelescope.Model Γ) p

/-- Every indicated universal model computes the canonical telescope group. -/
def toCanonicalModelEquiv (p : Bool)
    (cX : EquivariantCWComplex (topologicalAction Γ X)) (hX : FixedPointCriterion Γ X) :
    group (Γ := Γ) (X := X) p ≃+ topologicalGroup p Γ :=
  universalModelEquiv p cX (LabeledOrbitTelescope.equivariantCWComplex Γ)
    hX (LabeledOrbitTelescope.fixedPointCriterion Γ)

end UniversalModels
end BC4lean.TopologicalKHomology
