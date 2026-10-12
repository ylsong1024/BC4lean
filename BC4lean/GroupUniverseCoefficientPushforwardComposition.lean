import BC4lean.GroupUniverseCoefficientPushforward

/-! # Actual nonunital coefficient composition across independent universes

The product of two standard homomorphism cycles is computed by genuine
source pullback, the actual left identity theorem, and full product
uniqueness. The extra intermediate coefficient carrier is retained by a
whole Hilbert-module ULift unitary. Associativity then proves composition
of the independently defined product maps, with precisely that lift.
-/

noncomputable section
universe uΓ uA uB uC uD uE
namespace BC4lean.KKTheory.GroupUniverseCoefficientPushforward

section Hom
variable {Γ : Type uΓ} {B : Type uB} {C : Type uC} {D : Type uD} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C]
  [TopologicalSpace.SeparableSpace D] [Countable Γ]
  {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C} {η : CStarAlgebraAction Γ D}
  {δB : CStarGrading B} {δC : CStarGrading C} {δD : CStarGrading D}
  (hβ : β.PreservesGrading δB) (hγ : γ.PreservesGrading δC) (hη : η.PreservesGrading δD)
  (f : B →⋆ₙₐ[ℂ] C) (g : C →⋆ₙₐ[ℂ] D)
  (hactf : ∀ k b, f (β.automorphism k b) = γ.automorphism k (f b))
  (hgradef : ∀ b, f (δB.automorphism b) = δC.automorphism (f b))
  (hactg : ∀ k c, g (γ.automorphism k c) = η.automorphism k (g c))
  (hgradeg : ∀ c, g (δC.automorphism c) = δD.automorphism (g c))

omit [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B] [Countable Γ] in
theorem homClass_sourcePullback_identity :
    homClass hβ hγ f hactf hgradef =
      GradedKasparovHomotopyClass.sourcePullback β δB hβ f hactf hgradef
        (GroupUniverseProduct.identity γ δC hγ) := rfl

omit [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C] [Countable Γ] in
theorem homClass_sourcePullback_composition :
    GradedKasparovHomotopyClass.sourcePullback β δB hβ f hactf hgradef
      (homClass hγ hη g hactg hgradeg) =
    homClass hβ hη (g.comp f)
      (fun k b => by change g (f (β.automorphism k b)) = η.automorphism k (g (f b)); rw [hactf, hactg])
      (fun b => by change g (f (δB.automorphism b)) = δD.automorphism (g (f b)); rw [hgradef, hgradeg]) :=
  GradedKasparovHomotopyClass.mk_eq_of_iso
    (gradedStandardModuleHomCompositionPullbackIso β γ η δB δC δD hβ hγ hη
      f g hactf hgradef hactg hgradeg)

omit [PartialOrder B] [StarOrderedRing B] in
theorem homClass_product :
    GroupUniverseProduct.product (homClass hβ hγ f hactf hgradef)
      (homClass hγ hη g hactg hgradeg) =
    GradedKasparovHomotopyClass.ulift.{uΓ, uB, uD, uD, uC}
      (homClass hβ hη (g.comp f)
        (fun k b => by change g (f (β.automorphism k b)) = η.automorphism k (g (f b)); rw [hactf, hactg])
        (fun b => by change g (f (δB.automorphism b)) = δD.automorphism (g (f b)); rw [hgradef, hgradeg])) := by
  calc
    _ = GradedKasparovHomotopyClass.ulift.{uΓ, uB, uD, max uC uD, uC}
        (GroupUniverseProduct.product (homClass hβ hγ f hactf hgradef)
          (homClass hγ hη g hactg hgradeg)) :=
      (GradedKasparovHomotopyClass.ulift_eq_self.{uΓ, uB, uD, uD, uC} _).symm
    _ = GroupUniverseProduct.product (homClass hβ hγ f hactf hgradef)
        (GradedKasparovHomotopyClass.ulift.{uΓ, uC, uD, uD, uC}
          (homClass hγ hη g hactg hgradeg)) :=
      GroupUniverseProduct.product_ulift_second.{uΓ, uB, uC, uD, uC, uD, uC} _ _
    _ = GradedKasparovHomotopyClass.sourcePullback β δB hβ f hactf hgradef
        (GroupUniverseProduct.product (GroupUniverseProduct.identity γ δC hγ)
          (GradedKasparovHomotopyClass.ulift.{uΓ, uC, uD, uD, uC}
            (homClass hγ hη g hactg hgradeg))) := by
      rw [homClass_sourcePullback_identity hβ hγ f hactf hgradef]
      exact (GroupUniverseProduct.sourcePullback_product β δB hβ f hactf hgradef _ _).symm
    _ = GradedKasparovHomotopyClass.sourcePullback β δB hβ f hactf hgradef
        (GradedKasparovHomotopyClass.ulift.{uΓ, uC, uD, uD, uC}
          (homClass hγ hη g hactg hgradeg)) := by
      rw [GroupUniverseProduct.product_left_identity hγ]
    _ = GradedKasparovHomotopyClass.ulift.{uΓ, uB, uD, uD, uC}
        (GradedKasparovHomotopyClass.sourcePullback β δB hβ f hactf hgradef
          (homClass hγ hη g hactg hgradeg)) :=
      (GradedKasparovHomotopyClass.ulift_sourcePullback β δB hβ f hactf hgradef _).symm
    _ = _ := congrArg (GradedKasparovHomotopyClass.ulift.{uΓ, uB, uD, uD, uC})
      (homClass_sourcePullback_composition hβ hγ hη f g hactf hgradef hactg hgradeg)

end Hom

section Composition
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} [Group Γ]
  [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C] [TopologicalSpace.SeparableSpace D] [Countable Γ]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C} {η : CStarAlgebraAction Γ D}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C} {δD : CStarGrading D}
  (hβ : β.PreservesGrading δB) (hγ : γ.PreservesGrading δC) (hη : η.PreservesGrading δD)
  (f : B →⋆ₙₐ[ℂ] C) (g : C →⋆ₙₐ[ℂ] D)
  (hactf : ∀ k b, f (β.automorphism k b) = γ.automorphism k (f b))
  (hgradef : ∀ b, f (δB.automorphism b) = δC.automorphism (f b))
  (hactg : ∀ k c, g (γ.automorphism k c) = η.automorphism k (g c))
  (hgradeg : ∀ c, g (δC.automorphism c) = δD.automorphism (g c))

theorem coefficientPushforward_comp
    (x : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE} α β δA δB) :
    coefficientPushforward hγ hη g hactg hgradeg
      (coefficientPushforward hβ hγ f hactf hgradef x) =
    GradedKasparovHomotopyClass.ulift.{uΓ, uA, uD, max uE uD, uC}
      (coefficientPushforward hβ hη (g.comp f)
        (fun k b => by change g (f (β.automorphism k b)) = η.automorphism k (g (f b)); rw [hactf, hactg])
        (fun b => by change g (f (δB.automorphism b)) = δD.automorphism (g (f b)); rw [hgradef, hgradeg]) x) := by
  unfold coefficientPushforward
  rw [GroupUniverseProduct.product_assoc,
    homClass_product hβ hγ hη f g hactf hgradef hactg hgradeg]
  exact (GroupUniverseProduct.product_ulift_second.{uΓ, uA, uB, uD, uE, uD, uC} _ _).symm

theorem coefficientPushforward_comp_eq_self
    (x : GradedKasparovHomotopyClass.{uΓ, uA, uB, max uE uC} α β δA δB) :
    coefficientPushforward hγ hη g hactg hgradeg
      (coefficientPushforward hβ hγ f hactf hgradef x) =
    coefficientPushforward hβ hη (g.comp f)
      (fun k b => by change g (f (β.automorphism k b)) = η.automorphism k (g (f b)); rw [hactf, hactg])
      (fun b => by change g (f (δB.automorphism b)) = δD.automorphism (g (f b)); rw [hgradef, hgradeg]) x := by
  rw [coefficientPushforward_comp hβ hγ hη f g hactf hgradef hactg hgradeg]
  exact GradedKasparovHomotopyClass.ulift_eq_self.{uΓ, uA, uD, max uE uD, uC} _

end Composition
end BC4lean.KKTheory.GroupUniverseCoefficientPushforward
