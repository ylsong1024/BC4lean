import BC4lean.TopologicalKHomologyHomotopy

/-! # Bounded independent signature checks for the original Chapter 6 targets

The expected piece type below spells out the actual full parity KK group,
the induced action on C₀, and the trivial scalar coefficient action. The
remaining checks require the exported maps and proofs at independently written
expected types; no colimit value or K-homology equivalence is supplied as input.

The model checks retain the implementation's common universe `u` for Γ and both
ambient models. They do not assert comparison across different ambient universes.
-/

noncomputable section
open Topology TopologicalSpace
open scoped ZeroAtInfty ComplexOrder

universe uΓ uX uJ v u

namespace BC4lean.Chapter6ExpectedTypes
open ProperActions KKTheory KKTheory.GroupUniverseParityGroup TopologicalKHomology

section Pieces
variable {Γ : Type uΓ} {X : Type uX} [Group Γ] [TopologicalSpace X]
  [MulAction Γ X] [ContinuousConstSMul Γ X]

-- This abbreviation is independent of `pieceGroup`; it uses the underlying KK construction.
private abbrev actualPiece (p : Bool) (S : CocompactPiece Γ X) :=
  KKParityGroup.{uΓ,uX,0,uX} p
    (CZero.action Γ (X := S.toInvariantSubset) :
      CStarAlgebraAction Γ C₀(S.toInvariantSubset, ℂ))
    (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)

-- Target 1: both parities are the actual full KK groups with the stated algebras/actions.
example (p : Bool) (S : CocompactPiece Γ X) :
    pieceGroup p S =
      KKParityGroup.{uΓ,uX,0,uX} p
        (CZero.action Γ (X := S.toInvariantSubset) :
          CStarAlgebraAction Γ C₀(S.toInvariantSubset, ℂ))
        (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) := rfl

variable [Countable Γ] [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]

-- Target 2: function restriction is contravariant, while K-homology goes forward.
example {S T : CocompactPiece Γ X} (h : S ≤ T) :
    C₀(T.toInvariantSubset, ℂ) →⋆ₙₐ[ℂ] C₀(S.toInvariantSubset, ℂ) :=
  CZero.pieceRestriction h

example (p : Bool) {S T : CocompactPiece Γ X} (h : S ≤ T) :
    actualPiece p S →+ actualPiece p T := transition p h

example (p : Bool) (S : CocompactPiece Γ X) (x : actualPiece p S) :
    transition p (le_refl S) x = x := transition_refl p S x

example (p : Bool) {S T U : CocompactPiece Γ X}
    (hST : S ≤ T) (hTU : T ≤ U) (x : actualPiece p S) :
    transition p hTU (transition p hST x) = transition p (hST.trans hTU) x :=
  transition_trans p hST hTU x

-- Target 3: the diagram has the actual KK objects, and `group` is an actual DirectLimit.
example (p : Bool) (S : CocompactPiece Γ X) :
    (diagram (Γ := Γ) (X := X) p).obj S = actualPiece p S := rfl

example (p : Bool) :
    group (Γ := Γ) (X := X) p =
      DirectLimit (diagram (Γ := Γ) (X := X) p).obj
        (diagram (Γ := Γ) (X := X) p).map := rfl

example (p : Bool) {A : Type v} [AddCommGroup A]
    (f : ∀ S : CocompactPiece Γ X, actualPiece p S →+ A)
    (hf : ∀ S T (h : S ≤ T) x, f T (transition p h x) = f S x) :
    ∃! F : group (Γ := Γ) (X := X) p →+ A,
      ∀ S, F.comp (ofPiece p S) = f S :=
  existsUnique_desc p f hf

-- Indexing independence requires the explicit cofinal upper-bound condition.
example (p : Bool) {J : Type uJ} [Preorder J] [Nonempty J] [IsDirectedOrder J]
    (φ : J →o CocompactPiece Γ X) (hφ : ∀ S, ∃ j, S ≤ φ j) :
    ((diagram p).restrict φ).Colimit ≃+ group (Γ := Γ) (X := X) p :=
  cofinalIndexEquiv p φ hφ

example (p : Bool) {J : Type uJ} [Preorder J] [Nonempty J] [IsDirectedOrder J]
    (φ : J →o CocompactPiece Γ X) (hφ : ∀ S, ∃ j, S ≤ φ j)
    (j : J) (x : actualPiece p (φ j)) :
    cofinalIndexEquiv p φ hφ (((diagram p).restrict φ).of j x) = ofPiece p (φ j) x :=
  cofinalIndexEquiv_of p φ hφ j x

end Pieces

section Models
variable {Γ : Type u} [Group Γ] [Countable Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
  {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [MulAction Γ X] [MulAction Γ Y] [ContinuousConstSMul Γ X] [ContinuousConstSMul Γ Y]
  [LocallyCompactSpace X] [LocallyCompactSpace Y] [T2Space X] [T2Space Y]
  [SecondCountableTopology X] [SecondCountableTopology Y]

-- Properness and the comparison equivalence must be derived from the genuine CW models.
example (p : Bool)
    (cX : EquivariantCWComplex (topologicalAction Γ X))
    (cY : EquivariantCWComplex (topologicalAction Γ Y))
    (hX : FixedPointCriterion Γ X) (hY : FixedPointCriterion Γ Y) :
    group (Γ := Γ) (X := X) p ≃+ group (Γ := Γ) (X := Y) p :=
  universalModelEquiv p cX cY hX hY

-- The canonical target is the actual Chapter 4 geometric telescope.
example (p : Bool) (cX : EquivariantCWComplex (topologicalAction Γ X))
    (hX : FixedPointCriterion Γ X) :
    group (Γ := Γ) (X := X) p ≃+
      group (Γ := Γ) (X := LabeledOrbitTelescope.Model Γ) p :=
  toCanonicalModelEquiv p cX hX

-- The comparison homomorphism is independent of the continuous equivariant map chosen.
example (p : Bool)
    (cX : EquivariantCWComplex (topologicalAction Γ X))
    (cY : EquivariantCWComplex (topologicalAction Γ Y))
    (hY : FixedPointCriterion Γ Y) (f g : EquivariantMap Γ X Y) :
    letI := cX.proper
    letI := cY.proper
    pushforward p f = pushforward p g :=
  universalComparison_unique p cX cY hY f g

end Models
end BC4lean.Chapter6ExpectedTypes
