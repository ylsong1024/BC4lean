import BC4lean.GroupUniverseParityMapCoherence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The native even source map on concrete representatives

The native parity source map is the existing
homomorphism-cycle product. Its proved graded coherence identifies that
specific map with actual representation precomposition. The raw conversion
below keeps the actual module, grading, action and Fredholm operator.
-/

noncomputable section
universe uΓ uA uA' uB uE u
namespace BC4lean.KKTheory.NativeSourcePullback

variable {Γ : Type uΓ} {A : Type uA} {A' : Type uA'} {B : Type uB}
  [Group Γ] [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  (α' : CStarAlgebraAction Γ A') (f : A' →⋆ₙₐ[ℂ] A)
  (hf : ∀ g a, f (α'.automorphism g a) = α.automorphism g (f a))

/-- Actual source precomposition in the ordinary even picture, through the
proved identity-on-data trivial-grading conversions. -/
def evenCycle {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
    (c : KasparovCycle α β E) : KasparovCycle α' β E :=
  ((GradedKasparovCycle.ofKasparovCycle c).sourcePullback α' CStarGrading.trivial
    α'.preservesGrading_trivial f hf (fun _ => rfl)).toKasparovCycle

section NativeClass
variable [Countable Γ] [PartialOrder A] [StarOrderedRing A]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace A']
  [TopologicalSpace.SeparableSpace B]

/-- The already-defined native source homomorphism product has the actual raw
precomposition representative. No alternate source map is substituted. -/
theorem even_mk
    (c : BundledKasparovCycle.{uΓ,uA,uB,max u (max uA' (max uA uB))} α β) :
    GroupUniverseParityFunctoriality.sourcePullback.{uΓ,uA',uA,uB,u} false f hf
        (KasparovHomotopyClass.mk c) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of (evenCycle α' f hf c.cycle)) := by
  apply GroupUniverseEvenBridge.gradedClass_injective
  let d : GradedKasparovCycle α' β CStarGrading.trivial CStarGrading.trivial c.carrier :=
    (GradedKasparovCycle.ofKasparovCycle c.cycle).sourcePullback
      α' CStarGrading.trivial α'.preservesGrading_trivial f hf (fun _ => rfl)
  have hn : GroupUniverseEvenBridge.gradedClass
      (GroupUniverseParityFunctoriality.sourcePullback.{uΓ,uA',uA,uB,u} false f hf
        (KasparovHomotopyClass.mk c)) =
      GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of d) :=
    GroupUniverseParityFunctoriality.sourcePullback_graded_even.{uΓ,uA',uA,uB,u}
      (Γ := Γ) (A := A') (B := A) (C := B) (α := α') (β := α) (γ := β)
      f hf (KasparovHomotopyClass.mk c)
  have hconvert : GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of d) =
      GroupUniverseEvenBridge.gradedClass
        (KasparovHomotopyClass.mk (BundledKasparovCycle.of (evenCycle α' f hf c.cycle))) :=
    (congrArg
      (fun k : GradedKasparovCycle α' β CStarGrading.trivial CStarGrading.trivial c.carrier =>
        GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of k))
      (GradedKasparovCycle.ofKasparovCycle_toKasparovCycle d)).symm
  exact hn.trans hconvert

end NativeClass
end BC4lean.KKTheory.NativeSourcePullback
