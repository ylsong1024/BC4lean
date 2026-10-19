import BC4lean.AssemblyCutoffNaturality
import BC4lean.KasparovDescentSourcePullbackClass

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Actual compatibility with the Chapter 6 transition homomorphisms

The construction uses concrete cutoff restriction, native parity source
pullback coherence, actual descent naturality and the norm/cycle results.
 The proof uses the exact Chapter 6
transition, whose map is a homomorphism-cycle product, and the proved concrete
descent source-pullback comparison. No compatibility conclusion is an input.
-/

noncomputable section
universe uΓ uX
namespace BC4lean.Assembly
open KKTheory ProperActions
open KKTheory.GroupUniverseParityGroup KKTheory.GroupUniverseParityFunctoriality
open scoped ZeroAtInfty ComplexOrder KasparovDescent

variable (Γ : Type uΓ) [Group Γ] [Countable Γ]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  (X : Type uX) [TopologicalSpace X] [MulAction Γ X]
  [ContinuousConstSMul Γ X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [ProperSMul Γ X]

local instance transition_piece_locallyCompact (S : CocompactPiece Γ X) :
    LocallyCompactSpace S.toInvariantSubset := S.locallyCompact
local instance transition_pieceCoefficient_separable (S : CocompactPiece Γ X) :
    TopologicalSpace.SeparableSpace C₀(S.toInvariantSubset, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

/-- The genuine piece homomorphisms commute with the actual native
topological K-homology transition maps, in both degrees. -/
theorem pieceAssemblyHom_transition (p : Bool) {S T : CocompactPiece Γ X}
    (h : S ≤ T) (x : TopologicalKHomology.pieceGroup p S) :
    pieceAssemblyHom Γ X p T (TopologicalKHomology.transition p h x) =
      pieceAssemblyHom Γ X p S x := by
  have hd :
      KasparovDescent.classHom
          (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
          (CZero.action Γ (X := T.toInvariantSubset)) p
          (TopologicalKHomology.transition p h x) =
        sourcePullback.{0, max uΓ uX, max uΓ uX, uΓ, max uΓ uX} p
          (reducedCrossedMap (CZero.action Γ (X := T.toInvariantSubset))
            (CZero.action Γ (X := S.toInvariantSubset)) (CZero.pieceRestriction h)
            (CZero.pieceRestriction_equivariant h)) (fun _ _ => rfl)
          (KasparovDescent.classHom
            (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
            (CZero.action Γ (X := S.toInvariantSubset)) p x) :=
    KasparovDescent.classHom_sourcePullback
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      (CZero.action Γ (X := S.toInvariantSubset)) (CZero.action Γ (X := T.toInvariantSubset))
      p (CZero.pieceRestriction h) (CZero.pieceRestriction_equivariant h) x
  simp only [pieceAssemblyHom, spaceAssemblyHom, AddMonoidHom.comp_apply]
  rw [hd]
  exact congrArg (reducedScalarKKToAnalyticHom Γ p)
    (cutoffProductHom_pieceRestriction Γ X p h (pieceCutoff Γ X T) (pieceCutoff Γ X S)
      (KasparovDescent.classHom
        (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
        (CZero.action Γ (X := S.toInvariantSubset)) p x))

end BC4lean.Assembly
