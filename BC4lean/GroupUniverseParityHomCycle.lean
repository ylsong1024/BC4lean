import BC4lean.GroupUniverseCommonParityProduct
import BC4lean.GroupUniverseCoefficientPushforwardComposition

/-! # Actual ambient even homomorphism cycles

An equivariant nonunital homomorphism has its genuine zero-operator
standard target-module cycle. Whole lifts place it in a chosen ambient
universe. Its actual product is the composed homomorphism cycle, by the
already proved full source-pullback/product/unit construction.
-/

noncomputable section
universe uΓ uA uB uC uE uF v w
namespace BC4lean.KKTheory.GroupUniverseParityHomCycle

section Lift
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

theorem ulift_ulift (x : GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α β δA δB) :
    GradedKasparovHomotopyClass.ulift.{uΓ,uA,uB,max uE v,w}
      (GradedKasparovHomotopyClass.ulift.{uΓ,uA,uB,uE,v} x) =
    GradedKasparovHomotopyClass.ulift.{uΓ,uA,uB,uE,max v w} x := by
  refine Quotient.inductionOn x ?_
  intro c
  let d : BundledGradedKasparovCycle.{uΓ,uA,uB,max uE v} α β δA δB := c.ulift
  exact GradedKasparovHomotopyClass.mk_eq_of_iso
    (((c.cycle.uliftIso : GradedKasparovCycleIso c.cycle d.cycle).trans
      (d.cycle.uliftIso : GradedKasparovCycleIso d.cycle
        (d.ulift : BundledGradedKasparovCycle.{uΓ,uA,uB,max (max uE v) w} α β δA δB).cycle)).symm.trans
      (c.cycle.uliftIso : GradedKasparovCycleIso c.cycle
        (c.ulift : BundledGradedKasparovCycle.{uΓ,uA,uB,max uE (max v w)} α β δA δB).cycle))

end Lift

section Hom
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

def homClass (f : A →⋆ₙₐ[ℂ] B)
    (hact : ∀ k a, f (α.automorphism k a) = β.automorphism k (f a)) :
    KasparovHomotopyClass.{uΓ,uA,uB,max uB v} α β :=
  GroupUniverseEvenBridge.evenClass
    (GradedKasparovHomotopyClass.ulift.{uΓ,uA,uB,uB,v}
      (GroupUniverseCoefficientPushforward.homClass α.preservesGrading_trivial
        β.preservesGrading_trivial f hact (fun _ => rfl)))

omit [PartialOrder A] [StarOrderedRing A] [TopologicalSpace.SeparableSpace A] in
@[simp] theorem gradedClass_homClass (f : A →⋆ₙₐ[ℂ] B)
    (hact : ∀ k a, f (α.automorphism k a) = β.automorphism k (f a)) :
    GroupUniverseEvenBridge.gradedClass (homClass.{uΓ,uA,uB,v} f hact) =
    GradedKasparovHomotopyClass.ulift.{uΓ,uA,uB,uB,v}
      (GroupUniverseCoefficientPushforward.homClass α.preservesGrading_trivial
        β.preservesGrading_trivial f hact (fun _ => rfl)) :=
  GroupUniverseEvenBridge.gradedClass_evenClass _

end Hom

section Composition
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

omit [PartialOrder A] [StarOrderedRing A] in
/-- Composition in a common actual module universe comes from true raw
homomorphism-cycle products and genuine full uniqueness. -/
theorem homClass_product (f : A →⋆ₙₐ[ℂ] B) (g : B →⋆ₙₐ[ℂ] C)
    (hactf : ∀ k a, f (α.automorphism k a) = β.automorphism k (f a))
    (hactg : ∀ k b, g (β.automorphism k b) = γ.automorphism k (g b)) :
    GroupUniverseParityProduct.evenProduct
      (homClass.{uΓ,uA,uB,max v (max uA (max uB uC))} f hactf)
      (homClass.{uΓ,uB,uC,max v (max uA (max uB uC))} g hactg) =
    homClass.{uΓ,uA,uC,max v (max uA (max uB uC))} (g.comp f)
      (fun k a => by change g (f (α.automorphism k a)) = _; rw [hactf, hactg]; rfl) := by
  apply GroupUniverseEvenBridge.gradedClass_injective
  rw [GroupUniverseParityProduct.gradedClass_evenProduct, gradedClass_homClass,
    gradedClass_homClass, gradedClass_homClass,
    ← GroupUniverseProduct.product_ulift_first, ← GroupUniverseProduct.product_ulift_second,
    GradedKasparovHomotopyClass.ulift_eq_self]
  have hprod :
      GroupUniverseProduct.product.{uΓ,uA,uB,uC,uB,uC}
        (GroupUniverseCoefficientPushforward.homClass
          α.preservesGrading_trivial β.preservesGrading_trivial f hactf (fun _ => rfl))
        (GroupUniverseCoefficientPushforward.homClass
          β.preservesGrading_trivial γ.preservesGrading_trivial g hactg (fun _ => rfl)) =
      GradedKasparovHomotopyClass.ulift.{uΓ,uA,uC,uC,uB}
        (GroupUniverseCoefficientPushforward.homClass
          α.preservesGrading_trivial γ.preservesGrading_trivial (g.comp f)
          (fun k a => by change g (f (α.automorphism k a)) = _; rw [hactf, hactg]; rfl)
          (fun _ => rfl)) :=
    GroupUniverseCoefficientPushforward.homClass_product.{uΓ,uA,uB,uC}
      (β := α) (γ := β) (η := γ)
      α.preservesGrading_trivial β.preservesGrading_trivial γ.preservesGrading_trivial
      f g hactf (fun _ => rfl) hactg (fun _ => rfl)
  exact (congrArg
    (GradedKasparovHomotopyClass.ulift.{uΓ,uA,uC,max uB uC,max v (max uA (max uB uC))})
    hprod).trans
      (ulift_ulift.{uΓ,uA,uC,uC,uB,max v (max uA (max uB uC))} _)

end Composition
end BC4lean.KKTheory.GroupUniverseParityHomCycle
