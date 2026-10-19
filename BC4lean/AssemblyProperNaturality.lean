import BC4lean.AssemblyPieceHom
import BC4lean.ScalarKKNativeNaturality
import BC4lean.CutoffProperPullbackNaturality
import BC4lean.KasparovDescentSourcePullbackClass
import BC4lean.TopologicalKHomologyMaps

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Genuine assembly naturality for proper equivariant maps

The construction uses the concrete norm, source-pullback and cutoff
naturality results. The map on K-homology
is the actual native homomorphism-cycle product from Chapter 6. The proof
uses actual cutoff proper pullback and native Kasparov product balancing;
neither source-map equality nor descent product compatibility is assumed.
-/

noncomputable section
universe uΓ uX
namespace BC4lean.Assembly
open KKTheory ProperActions OperatorKTheory
open KKTheory.GroupUniverseParityGroup KKTheory.GroupUniverseParityFunctoriality
open scoped ZeroAtInfty ComplexOrder KasparovDescent

variable (Γ : Type uΓ) [Group Γ] [Countable Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
  (X Y : Type uX) [TopologicalSpace X] [TopologicalSpace Y]
  [MulAction Γ X] [MulAction Γ Y]
  [ContinuousConstSMul Γ X] [ContinuousConstSMul Γ Y]
  [LocallyCompactSpace X] [LocallyCompactSpace Y] [T2Space X] [T2Space Y]
  [SecondCountableTopology X] [SecondCountableTopology Y]
  [ProperSMul Γ X] [ProperSMul Γ Y]

local instance sourceCoefficient_separable : TopologicalSpace.SeparableSpace C₀(X, ℂ) :=
  TopologicalKHomology.cZero_separableSpace
local instance targetCoefficient_separable : TopologicalSpace.SeparableSpace C₀(Y, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

theorem cutoffKKClass_properPullback (f : EquivariantMap Γ X Y) (hf : IsProperMap f)
    (cY : Cutoff.CutoffFunction Γ Y) (cX : Cutoff.CutoffFunction Γ X) :
    coefficientPushforward.{0, 0, max uΓ uX, max uΓ uX, max uΓ uX} false
      (reducedCrossedMap (CZero.action Γ (X := Y)) (CZero.action Γ (X := X))
        (CZero.properPullback f hf) (CZero.properPullback_equivariant f hf))
      (fun _ _ => rfl) (cutoffKKClass Γ Y cY) = cutoffKKClass Γ X cX := by
  apply (scalarKKOperatorK0AddEquiv.{max uΓ uX, max uΓ uX}).injective
  let φ : ReducedCrossedProduct (CZero.action Γ (X := Y)) →⋆ₙₐ[ℂ]
      ReducedCrossedProduct (CZero.action Γ (X := X)) :=
    reducedCrossedMap (CZero.action Γ (X := Y)) (CZero.action Γ (X := X))
      (CZero.properPullback f hf) (CZero.properPullback_equivariant f hf)
  have hn := scalarKKOperatorK0_native_coefficient_natural.{max uΓ uX, max uΓ uX, max uΓ uX}
    (B := ReducedCrossedProduct (CZero.action Γ (X := Y)))
    (C := ReducedCrossedProduct (CZero.action Γ (X := X)))
    φ (cutoffKKClass Γ Y cY)
  have hY : scalarKKOperatorK0AddEquiv.{max uΓ uX, max uΓ uX}
      (cutoffKKClass Γ Y cY) = Cutoff.cutoffK0 cY :=
    (scalarKKOperatorK0AddEquiv.{max uΓ uX, max uΓ uX}).apply_symm_apply (Cutoff.cutoffK0 cY)
  have hX : scalarKKOperatorK0AddEquiv.{max uΓ uX, max uΓ uX}
      (cutoffKKClass Γ X cX) = Cutoff.cutoffK0 cX :=
    (scalarKKOperatorK0AddEquiv.{max uΓ uX, max uΓ uX}).apply_symm_apply (Cutoff.cutoffK0 cX)
  exact hn.trans ((congrArg (operatorK0Map φ) hY).trans
    ((Cutoff.cutoffK0_properPullback f hf cY cX).trans hX.symm))

theorem cutoffProductHom_properPullback (p : Bool)
    (f : EquivariantMap Γ X Y) (hf : IsProperMap f)
    (cY : Cutoff.CutoffFunction Γ Y) (cX : Cutoff.CutoffFunction Γ X)
    (y : KKParityGroup.{0, max uΓ uX, uΓ, max uΓ uX} p
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
        (ReducedCrossedProduct (CZero.action Γ (X := X))))
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
        (ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)))) :
    cutoffProductHom Γ Y p cY
      (sourcePullback.{0, max uΓ uX, max uΓ uX, uΓ, max uΓ uX} p
        (reducedCrossedMap (CZero.action Γ (X := Y)) (CZero.action Γ (X := X))
          (CZero.properPullback f hf) (CZero.properPullback_equivariant f hf))
        (fun _ _ => rfl) y) = cutoffProductHom Γ X p cX y := by
  let φ := reducedCrossedMap (CZero.action Γ (X := Y)) (CZero.action Γ (X := X))
    (CZero.properPullback f hf) (CZero.properPullback_equivariant f hf)
  cases p
  · change GroupUniverseCommonParityProduct.product.{0, 0, max uΓ uX, uΓ, max uΓ uX}
      false false (cutoffKKClass Γ Y cY)
        (sourcePullback.{0, max uΓ uX, max uΓ uX, uΓ, max uΓ uX} false φ (fun _ _ => rfl) y) =
      GroupUniverseCommonParityProduct.product.{0, 0, max uΓ uX, uΓ, max uΓ uX}
        false false (cutoffKKClass Γ X cX) y
    rw [← coefficientPushforward_product_eq_sourcePullback.{0, 0, max uΓ uX, max uΓ uX, uΓ, max uΓ uX}
      false false φ (fun _ _ => rfl) (cutoffKKClass Γ Y cY) y]
    rw [cutoffKKClass_properPullback Γ X Y f hf cY cX]
  · change GroupUniverseCommonParityProduct.product.{0, 0, max uΓ uX, uΓ, max uΓ uX}
      false true (cutoffKKClass Γ Y cY)
        (sourcePullback.{0, max uΓ uX, max uΓ uX, uΓ, max uΓ uX} true φ (fun _ _ => rfl) y) =
      GroupUniverseCommonParityProduct.product.{0, 0, max uΓ uX, uΓ, max uΓ uX}
        false true (cutoffKKClass Γ X cX) y
    rw [← coefficientPushforward_product_eq_sourcePullback.{0, 0, max uΓ uX, max uΓ uX, uΓ, max uΓ uX}
      false true φ (fun _ _ => rfl) (cutoffKKClass Γ Y cY) y]
    rw [cutoffKKClass_properPullback Γ X Y f hf cY cX]

/-- Proper equivariant pushforward commutes with the actual assembly formula. -/
theorem spaceAssemblyHom_properPushforward (p : Bool)
    (f : EquivariantMap Γ X Y) (hf : IsProperMap f)
    (cY : Cutoff.CutoffFunction Γ Y) (cX : Cutoff.CutoffFunction Γ X)
    (x : TopologicalKHomology.spaceGroup p Γ X) :
    spaceAssemblyHom Γ Y p cY (TopologicalKHomology.properPushforward p f hf x) =
      spaceAssemblyHom Γ X p cX x := by
  have hd :
      KasparovDescent.classHom (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
          (CZero.action Γ (X := Y)) p (TopologicalKHomology.properPushforward p f hf x) =
        sourcePullback.{0, max uΓ uX, max uΓ uX, uΓ, max uΓ uX} p
          (reducedCrossedMap (CZero.action Γ (X := Y)) (CZero.action Γ (X := X))
            (CZero.properPullback f hf) (CZero.properPullback_equivariant f hf)) (fun _ _ => rfl)
          (KasparovDescent.classHom (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
            (CZero.action Γ (X := X)) p x) :=
    KasparovDescent.classHom_sourcePullback
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      (CZero.action Γ (X := X)) (CZero.action Γ (X := Y)) p
      (CZero.properPullback f hf) (CZero.properPullback_equivariant f hf) x
  simp only [spaceAssemblyHom, AddMonoidHom.comp_apply]
  rw [hd]
  exact congrArg (reducedScalarKKToAnalyticHom Γ p)
    (cutoffProductHom_properPullback Γ X Y p f hf cY cX
      (KasparovDescent.classHom (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
        (CZero.action Γ (X := X)) p x))

end BC4lean.Assembly
