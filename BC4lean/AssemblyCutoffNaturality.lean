import BC4lean.AssemblyPieceHom
import BC4lean.ScalarKKNativeNaturality
import BC4lean.CutoffRestrictionNaturality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Actual cutoff-class naturality and native product balancing

The construction imports the genuine crossed-map and cutoff
restriction results. Scalar comparison injectivity
lifts the concrete cutoff K0 restriction theorem to the native coefficient
Kasparov product. The existing parity product balancing law then transports
the actual cutoff product through the actual source pullback map.
-/

noncomputable section
universe uΓ uX
namespace BC4lean.Assembly
open KKTheory ProperActions OperatorKTheory
open KKTheory.GroupUniverseParityGroup KKTheory.GroupUniverseParityFunctoriality
open scoped ZeroAtInfty ComplexOrder KasparovDescent

variable (Γ : Type uΓ) [Group Γ] [Countable Γ]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  (X : Type uX) [TopologicalSpace X] [MulAction Γ X]
  [ContinuousConstSMul Γ X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [ProperSMul Γ X]

local instance cutoffNaturality_piece_locallyCompact (S : CocompactPiece Γ X) :
    LocallyCompactSpace S.toInvariantSubset := S.locallyCompact
local instance cutoffNaturality_pieceCoefficient_separable (S : CocompactPiece Γ X) :
    TopologicalSpace.SeparableSpace C₀(S.toInvariantSubset, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

/-- The actual coefficient product maps the cutoff KK class of the larger
piece to that of the smaller piece; this is proved through the true K0 index. -/
theorem cutoffKKClass_pieceRestriction {S T : CocompactPiece Γ X} (h : S ≤ T)
    (cT : Cutoff.CutoffFunction Γ T.toInvariantSubset)
    (cS : Cutoff.CutoffFunction Γ S.toInvariantSubset) :
    coefficientPushforward.{0, 0, max uΓ uX, max uΓ uX, max uΓ uX} false
      (reducedCrossedMap (CZero.action Γ (X := T.toInvariantSubset))
        (CZero.action Γ (X := S.toInvariantSubset)) (CZero.pieceRestriction h)
        (CZero.pieceRestriction_equivariant h))
      (fun _ _ => rfl) (cutoffKKClass Γ T.toInvariantSubset cT) =
      cutoffKKClass Γ S.toInvariantSubset cS := by
  apply (scalarKKOperatorK0AddEquiv.{max uΓ uX, max uΓ uX}).injective
  let f : ReducedCrossedProduct (CZero.action Γ (X := T.toInvariantSubset)) →⋆ₙₐ[ℂ]
      ReducedCrossedProduct (CZero.action Γ (X := S.toInvariantSubset)) :=
    reducedCrossedMap (CZero.action Γ (X := T.toInvariantSubset))
      (CZero.action Γ (X := S.toInvariantSubset)) (CZero.pieceRestriction h)
      (CZero.pieceRestriction_equivariant h)
  have hn := scalarKKOperatorK0_native_coefficient_natural.{max uΓ uX, max uΓ uX, max uΓ uX}
    (B := ReducedCrossedProduct (CZero.action Γ (X := T.toInvariantSubset)))
    (C := ReducedCrossedProduct (CZero.action Γ (X := S.toInvariantSubset)))
    f (cutoffKKClass Γ T.toInvariantSubset cT)
  have hT : scalarKKOperatorK0AddEquiv.{max uΓ uX, max uΓ uX}
      (cutoffKKClass Γ T.toInvariantSubset cT) = Cutoff.cutoffK0 cT :=
    (scalarKKOperatorK0AddEquiv.{max uΓ uX, max uΓ uX}).apply_symm_apply (Cutoff.cutoffK0 cT)
  have hS : scalarKKOperatorK0AddEquiv.{max uΓ uX, max uΓ uX}
      (cutoffKKClass Γ S.toInvariantSubset cS) = Cutoff.cutoffK0 cS :=
    (scalarKKOperatorK0AddEquiv.{max uΓ uX, max uΓ uX}).apply_symm_apply (Cutoff.cutoffK0 cS)
  exact hn.trans ((congrArg (operatorK0Map f) hT).trans
    ((Cutoff.cutoffK0_pieceRestriction h cT cS).trans hS.symm))

/-- Native middle-algebra balancing proves the exact cutoff-product
restriction identity in both degrees, before the final scalar index. -/
theorem cutoffProductHom_pieceRestriction (p : Bool)
    {S T : CocompactPiece Γ X} (h : S ≤ T)
    (cT : Cutoff.CutoffFunction Γ T.toInvariantSubset)
    (cS : Cutoff.CutoffFunction Γ S.toInvariantSubset)
    (y : KKParityGroup.{0, max uΓ uX, uΓ, max uΓ uX} p
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
        (ReducedCrossedProduct (CZero.action Γ (X := S.toInvariantSubset))))
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
        (ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)))) :
    cutoffProductHom Γ T.toInvariantSubset p cT
      (sourcePullback.{0, max uΓ uX, max uΓ uX, uΓ, max uΓ uX} p
        (reducedCrossedMap (CZero.action Γ (X := T.toInvariantSubset))
          (CZero.action Γ (X := S.toInvariantSubset)) (CZero.pieceRestriction h)
          (CZero.pieceRestriction_equivariant h)) (fun _ _ => rfl) y) =
      cutoffProductHom Γ S.toInvariantSubset p cS y := by
  let f := reducedCrossedMap (CZero.action Γ (X := T.toInvariantSubset))
    (CZero.action Γ (X := S.toInvariantSubset)) (CZero.pieceRestriction h)
    (CZero.pieceRestriction_equivariant h)
  cases p
  · change GroupUniverseCommonParityProduct.product.{0, 0, max uΓ uX, uΓ, max uΓ uX}
      false false (cutoffKKClass Γ T.toInvariantSubset cT)
        (sourcePullback.{0, max uΓ uX, max uΓ uX, uΓ, max uΓ uX} false f (fun _ _ => rfl) y) =
      GroupUniverseCommonParityProduct.product.{0, 0, max uΓ uX, uΓ, max uΓ uX}
        false false (cutoffKKClass Γ S.toInvariantSubset cS) y
    rw [← coefficientPushforward_product_eq_sourcePullback.{0, 0, max uΓ uX, max uΓ uX, uΓ, max uΓ uX}
      false false f (fun _ _ => rfl) (cutoffKKClass Γ T.toInvariantSubset cT) y]
    rw [cutoffKKClass_pieceRestriction Γ X h cT cS]
  · change GroupUniverseCommonParityProduct.product.{0, 0, max uΓ uX, uΓ, max uΓ uX}
      false true (cutoffKKClass Γ T.toInvariantSubset cT)
        (sourcePullback.{0, max uΓ uX, max uΓ uX, uΓ, max uΓ uX} true f (fun _ _ => rfl) y) =
      GroupUniverseCommonParityProduct.product.{0, 0, max uΓ uX, uΓ, max uΓ uX}
        false true (cutoffKKClass Γ S.toInvariantSubset cS) y
    rw [← coefficientPushforward_product_eq_sourcePullback.{0, 0, max uΓ uX, max uΓ uX, uΓ, max uΓ uX}
      false true f (fun _ _ => rfl) (cutoffKKClass Γ T.toInvariantSubset cT) y]
    rw [cutoffKKClass_pieceRestriction Γ X h cT cS]

end BC4lean.Assembly
