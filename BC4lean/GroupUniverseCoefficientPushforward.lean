import BC4lean.GroupUniverseProductSource
import BC4lean.GroupUniverseProductLift
import BC4lean.GradedStandardModuleHomCycle
import BC4lean.GradedKasparovCompactSecondProduct

/-! # Actual coefficient pushforward with independent universes

A graded equivariant nonunital map B → C gives its actual compact standard
C-module homomorphism cycle. Multiplication by this cycle defines the
pushforward, independently of any K-theory comparison. A module in uE is
sent to the genuine completed tensor in max(uE,uC). Full product uniqueness
identifies its representative with the actual first-factor operator F⊗1;
all four connection laws and localized positivity come from the proved
compact-second product criterion. Identity uses the actual module lift
when its standard coefficient module lives in a larger universe.
-/

noncomputable section
universe uΓ uA uB uC uD uE
namespace BC4lean.KKTheory.GroupUniverseCoefficientPushforward

section Hom
variable {Γ : Type uΓ} {B : Type uB} {C : Type uC} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C]
  {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  {δB : CStarGrading B} {δC : CStarGrading C}

def homClass (hβ : β.PreservesGrading δB) (hγ : γ.PreservesGrading δC)
    (f : B →⋆ₙₐ[ℂ] C)
    (hact : ∀ g b, f (β.automorphism g b) = γ.automorphism g (f b))
    (hgrade : ∀ b, f (δB.automorphism b) = δC.automorphism (f b)) :
    GradedKasparovHomotopyClass.{uΓ, uB, uC, uC} β γ δB δC :=
  GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
    (gradedStandardModuleHomCycle β γ δB δC hβ hγ f hact hgrade))

theorem homClass_identity (hβ : β.PreservesGrading δB) :
    homClass hβ hβ (NonUnitalStarAlgHom.id ℂ B) (fun _ _ => rfl) (fun _ => rfl) =
      GroupUniverseProduct.identity β δB hβ :=
  GradedKasparovHomotopyClass.mk_eq_of_iso (gradedStandardModuleHomIdentityIso β δB hβ)

end Hom

section Pushforward
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} [Group Γ]
  [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C] [Countable Γ]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}

def coefficientPushforward (hβ : β.PreservesGrading δB) (hγ : γ.PreservesGrading δC)
    (f : B →⋆ₙₐ[ℂ] C)
    (hact : ∀ g b, f (β.automorphism g b) = γ.automorphism g (f b))
    (hgrade : ∀ b, f (δB.automorphism b) = δC.automorphism (f b))
    (x : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE} α β δA δB) :
    GradedKasparovHomotopyClass.{uΓ, uA, uC, max uE uC} α γ δA δC :=
  GroupUniverseProduct.product x (homClass hβ hγ f hact hgrade)

theorem coefficientPushforward_add (hβ : β.PreservesGrading δB) (hγ : γ.PreservesGrading δC)
    (f : B →⋆ₙₐ[ℂ] C)
    (hact : ∀ g b, f (β.automorphism g b) = γ.automorphism g (f b))
    (hgrade : ∀ b, f (δB.automorphism b) = δC.automorphism (f b))
    (x y : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE} α β δA δB) :
    coefficientPushforward hβ hγ f hact hgrade (x + y) =
      coefficientPushforward hβ hγ f hact hgrade x +
        coefficientPushforward hβ hγ f hact hgrade y :=
  GroupUniverseProduct.add_product x y (homClass hβ hγ f hact hgrade)

theorem coefficientPushforward_identity (hβ : β.PreservesGrading δB)
    (x : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE} α β δA δB) :
    coefficientPushforward hβ hβ (NonUnitalStarAlgHom.id ℂ B)
      (fun _ _ => rfl) (fun _ => rfl) x =
      GradedKasparovHomotopyClass.ulift.{uΓ, uA, uB, uE, uB} x := by
  change GroupUniverseProduct.product x
    (homClass hβ hβ (NonUnitalStarAlgHom.id ℂ B)
      (fun _ _ => rfl) (fun _ => rfl)) = _
  rw [homClass_identity]
  calc
    _ = GradedKasparovHomotopyClass.ulift.{uΓ, uA, uB, max uE uB, uB}
        (GroupUniverseProduct.product x (GroupUniverseProduct.identity β δB hβ)) :=
      (GradedKasparovHomotopyClass.ulift_eq_self.{uΓ, uA, uB, uE, uB} _).symm
    _ = GroupUniverseProduct.product
        (GradedKasparovHomotopyClass.ulift.{uΓ, uA, uB, uE, uB} x)
        (GroupUniverseProduct.identity β δB hβ) :=
      GroupUniverseProduct.product_ulift_first.{uΓ, uA, uB, uB, uE, uB, uB} _ _
    _ = _ := GroupUniverseProduct.product_right_identity hβ _

theorem coefficientPushforward_identity_eq_self (hβ : β.PreservesGrading δB)
    (x : GradedKasparovHomotopyClass.{uΓ, uA, uB, max uE uB} α β δA δB) :
    coefficientPushforward hβ hβ (NonUnitalStarAlgHom.id ℂ B)
      (fun _ _ => rfl) (fun _ => rfl) x = x := by
  rw [coefficientPushforward_identity]
  exact GradedKasparovHomotopyClass.ulift_eq_self.{uΓ, uA, uB, uE, uB} x

theorem coefficientPushforward_mk_tensor (hβ : β.PreservesGrading δB)
    (hγ : γ.PreservesGrading δC) (f : B →⋆ₙₐ[ℂ] C)
    (hact : ∀ g b, f (β.automorphism g b) = γ.automorphism g (f b))
    (hgrade : ∀ b, f (δB.automorphism b) = δC.automorphism (f b))
    (c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB) :
    coefficientPushforward hβ hγ f hact hgrade (GradedKasparovHomotopyClass.mk c) =
      GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
        (gradedKasparovCompactSecondProduct c.cycle
          (gradedStandardModuleHomCycle β γ δB δC hβ hγ f hact hgrade)
          (gradedStandardModuleHomCycle_representation_compact
            β γ δB δC hβ hγ f hact hgrade))) := by
  exact GroupUniverseProduct.product_mk_eq_of_isProduct c
    (BundledGradedKasparovCycle.of (gradedStandardModuleHomCycle β γ δB δC hβ hγ f hact hgrade))
    (gradedKasparovCompactSecondProduct_isProduct c.cycle _ rfl
      (gradedStandardModuleHomCycle_representation_compact β γ δB δC hβ hγ f hact hgrade))

end Pushforward
end BC4lean.KKTheory.GroupUniverseCoefficientPushforward
