import BC4lean.GradedKasparovSourcePullbackClass

/-! # Actual identity and composition laws for source pullback

The laws first use genuine identity-on-vectors whole-cycle unitaries.
They then descend through the actual single-full-witness quotient. The sum
law is supplied by the separate actual source-pullback/direct-sum unitary.
-/

noncomputable section
universe uΓ uA uA' uA'' uB uE
namespace BC4lean.KKTheory

variable {Γ : Type uΓ} {A : Type uA} {A' : Type uA'} {A'' : Type uA''} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A'] [NonUnitalCStarAlgebra A'']
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

section Raw
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

def GradedKasparovCycle.sourcePullbackIdentityIso
    (c : GradedKasparovCycle α β δA δB E) (hα : α.PreservesGrading δA) :
    GradedKasparovCycleIso
      (c.sourcePullback α δA hα (NonUnitalStarAlgHom.id ℂ A) (fun _ _ => rfl) (fun _ => rfl)) c where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

def GradedKasparovCycle.sourcePullbackCompositionIso
    (c : GradedKasparovCycle α β δA δB E)
    (α' : CStarAlgebraAction Γ A') (δA' : CStarGrading A') (hα' : α'.PreservesGrading δA')
    (f : A' →⋆ₙₐ[ℂ] A)
    (hactf : ∀ g a, f (α'.automorphism g a) = α.automorphism g (f a))
    (hgradef : ∀ a, f (δA'.automorphism a) = δA.automorphism (f a))
    (α'' : CStarAlgebraAction Γ A'') (δA'' : CStarGrading A'') (hα'' : α''.PreservesGrading δA'')
    (g : A'' →⋆ₙₐ[ℂ] A')
    (hactg : ∀ k a, g (α''.automorphism k a) = α'.automorphism k (g a))
    (hgradeg : ∀ a, g (δA''.automorphism a) = δA'.automorphism (g a)) :
    GradedKasparovCycleIso
      ((c.sourcePullback α' δA' hα' f hactf hgradef).sourcePullback α'' δA'' hα'' g hactg hgradeg)
      (c.sourcePullback α'' δA'' hα'' (f.comp g)
        (fun k a => by change f (g (α''.automorphism k a)) = α.automorphism k (f (g a)); rw [hactg, hactf])
        (fun a => by change f (g (δA''.automorphism a)) = δA.automorphism (f (g a)); rw [hgradeg, hgradef])) where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

end Raw

namespace GradedKasparovHomotopyClass
variable [TopologicalSpace.SeparableSpace B]

@[simp] theorem sourcePullback_id (hα : α.PreservesGrading δA)
    (x : GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α β δA δB) :
    sourcePullback α δA hα (NonUnitalStarAlgHom.id ℂ A) (fun _ _ => rfl) (fun _ => rfl) x = x := by
  refine Quotient.inductionOn x ?_
  intro c
  exact mk_eq_of_iso (c.cycle.sourcePullbackIdentityIso hα)

theorem sourcePullback_comp
    (α' : CStarAlgebraAction Γ A') (δA' : CStarGrading A') (hα' : α'.PreservesGrading δA')
    (f : A' →⋆ₙₐ[ℂ] A)
    (hactf : ∀ g a, f (α'.automorphism g a) = α.automorphism g (f a))
    (hgradef : ∀ a, f (δA'.automorphism a) = δA.automorphism (f a))
    (α'' : CStarAlgebraAction Γ A'') (δA'' : CStarGrading A'') (hα'' : α''.PreservesGrading δA'')
    (g : A'' →⋆ₙₐ[ℂ] A')
    (hactg : ∀ k a, g (α''.automorphism k a) = α'.automorphism k (g a))
    (hgradeg : ∀ a, g (δA''.automorphism a) = δA'.automorphism (g a))
    (x : GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α β δA δB) :
    sourcePullback α'' δA'' hα'' g hactg hgradeg
      (sourcePullback α' δA' hα' f hactf hgradef x) =
      sourcePullback α'' δA'' hα'' (f.comp g)
        (fun k a => by change f (g (α''.automorphism k a)) = α.automorphism k (f (g a)); rw [hactg, hactf])
        (fun a => by change f (g (δA''.automorphism a)) = δA.automorphism (f (g a)); rw [hgradeg, hgradef]) x := by
  refine Quotient.inductionOn x ?_
  intro c
  exact mk_eq_of_iso (c.cycle.sourcePullbackCompositionIso α' δA' hα' f hactf hgradef
    α'' δA'' hα'' g hactg hgradeg)

end GradedKasparovHomotopyClass
end BC4lean.KKTheory
