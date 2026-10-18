import BC4lean.KasparovSourceHomotopy
import BC4lean.GroupUniverseParityMapCoherence

/-! # Source homotopy invariance of the genuine parity groups

The even and odd maps agree with actual graded representation pullback.
The full interval witnesses constructed for point-norm source homotopies
therefore prove equality on both full parity quotients.
-/

noncomputable section
universe uΓ uA uB uC u
namespace BC4lean.KKTheory.GroupUniverseParityFunctoriality
open GroupUniverseParityGroup BC4lean.OperatorKTheory

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC}
  [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  {f₀ f₁ : A →⋆ₙₐ[ℂ] B}

/-- Genuinely equivariant point-norm homotopies induce equal source maps
on each even or odd full Kasparov group. -/
theorem sourcePullback_homotopy (p : Bool) (h : StarHomotopy f₀ f₁)
    (hact : ∀ t g a, h.toFun t (α.automorphism g a) = β.automorphism g (h.toFun t a))
    (hact₀ : ∀ g a, f₀ (α.automorphism g a) = β.automorphism g (f₀ a))
    (hact₁ : ∀ g a, f₁ (α.automorphism g a) = β.automorphism g (f₁ a))
    (x : KKParityGroup.{uΓ,uB,uC,max u (max uA (max uB uC))} p β γ) :
    sourcePullback.{uΓ,uA,uB,uC,u} p f₀ hact₀ x =
      sourcePullback.{uΓ,uA,uB,uC,u} p f₁ hact₁ x := by
  cases p
  · apply GroupUniverseEvenBridge.gradedClass_injective
    exact (sourcePullback_graded_even.{uΓ,uA,uB,uC,u} f₀ hact₀ x).trans
      ((GradedKasparovHomotopyClass.sourcePullback_homotopy
        α.preservesGrading_trivial h hact (fun _ _ => rfl)
        hact₀ hact₁ (fun _ => rfl) (fun _ => rfl)
        (GroupUniverseEvenBridge.gradedClass x)).trans
          (sourcePullback_graded_even.{uΓ,uA,uB,uC,u} f₁ hact₁ x).symm)
  · apply GroupUniverseCliffordCoordinateBridge.gradedOddClass_injective
    exact (sourcePullback_graded_odd.{uΓ,uA,uB,uC,u} f₀ hact₀ x).trans
      ((GradedKasparovHomotopyClass.sourcePullback_homotopy
        α.preservesGrading_trivial h hact (fun _ _ => rfl)
        hact₀ hact₁ (fun _ => rfl) (fun _ => rfl)
        (GroupUniverseCliffordCoordinateBridge.gradedOddClass x)).trans
          (sourcePullback_graded_odd.{uΓ,uA,uB,uC,u} f₁ hact₁ x).symm)

/-- The induced additive homomorphisms themselves are homotopy invariant. -/
theorem sourcePullbackHom_homotopy (p : Bool) (h : StarHomotopy f₀ f₁)
    (hact : ∀ t g a, h.toFun t (α.automorphism g a) = β.automorphism g (h.toFun t a))
    (hact₀ : ∀ g a, f₀ (α.automorphism g a) = β.automorphism g (f₀ a))
    (hact₁ : ∀ g a, f₁ (α.automorphism g a) = β.automorphism g (f₁ a)) :
    sourcePullbackHom.{uΓ,uA,uB,uC,u} (γ := γ) p f₀ hact₀ =
      sourcePullbackHom.{uΓ,uA,uB,uC,u} (γ := γ) p f₁ hact₁ := by
  ext x
  exact sourcePullback_homotopy.{uΓ,uA,uB,uC,u} p h hact hact₀ hact₁ x

end BC4lean.KKTheory.GroupUniverseParityFunctoriality
