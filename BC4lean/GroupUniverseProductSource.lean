import BC4lean.GroupUniverseProduct
import BC4lean.GradedKasparovProductSourcePullback

/-! # Genuine product source naturality with independent universes

Precomposition preserves the actual generic product criteria. The whole
product cycle unitary and genuine chosen-product full uniqueness descend
this fact to the quotient by one actual arbitrary interval witness.
-/

noncomputable section
universe uΓ uA uA' uB uC uE uF
namespace BC4lean.KKTheory.GroupUniverseProduct
variable {Γ : Type uΓ} {A : Type uA} {A' : Type uA'} {B : Type uB} {C : Type uC}
  [Group Γ] [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace A']
  [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C] [Countable Γ]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}
  (α' : CStarAlgebraAction Γ A') (δA' : CStarGrading A')
  (hα' : α'.PreservesGrading δA') (f : A' →⋆ₙₐ[ℂ] A)
  (hact : ∀ g a, f (α'.automorphism g a) = α.automorphism g (f a))
  (hgrade : ∀ a, f (δA'.automorphism a) = δA.automorphism (f a))

theorem sourcePullback_product
    (x : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE} α β δA δB)
    (y : GradedKasparovHomotopyClass.{uΓ, uB, uC, uF} β γ δB δC) :
    GradedKasparovHomotopyClass.sourcePullback α' δA' hα' f hact hgrade (product x y) =
      product (GradedKasparovHomotopyClass.sourcePullback α' δA' hα' f hact hgrade x) y := by
  refine Quotient.inductionOn₂ x y ?_
  intro c d
  let c' := c.sourcePullback α' δA' hα' f hact hgrade
  have hR := gradedKasparovProductSourcePullback_isProduct α' δA' hα' f hact hgrade
    c.cycle d.cycle (productOperator_isProduct c d)
  have hright := product_mk_eq_of_isProduct c' d hR
  have hiso := GradedKasparovHomotopyClass.mk_eq_of_iso
    (c := (bundledProduct c d).sourcePullback α' δA' hα' f hact hgrade)
    (d := BundledGradedKasparovCycle.of
      (gradedKasparovTensorCycleOfConditions c'.cycle d.cycle (productOperator c d)
        hR.cycleConditions))
    (gradedKasparovProductSourcePullback_cycleIso α' δA' hα' f hact hgrade
      c.cycle d.cycle (productOperator_isProduct c d))
  exact hiso.trans hright.symm

end BC4lean.KKTheory.GroupUniverseProduct
