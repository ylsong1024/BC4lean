import BC4lean.KasparovDescentClass
import BC4lean.KasparovDescentSourcePullback
import BC4lean.NativeEvenSourcePullback
import BC4lean.NativeOddSourcePullback

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Source naturality for the actual native parity descent maps

The construction imports the concrete crossed maps, reduced source
representations, cycle and full-homotopy descent.
 No naturality statement, product
compatibility law, or raw cycle isomorphism is assumed as input.

The existing native source map is the homomorphism-cycle product used in
Chapter 6. Its proved graded parity coherence identifies its representatives
with actual source precomposition. On the actual descent module, equality of
the two reduced source representations gives a genuine identity-module cycle
isomorphism. These two concrete calculations prove class naturality.

The common input module universe is `max u (max uA' (max uA uB))`.
After descent it is enlarged by `max uΓ uB`; the native target source map is
used in that same actual universe. When both source algebras are in universe
`uX`, the coefficient is ℂ, and `u = uX`, this is exactly the Chapter 6
transition from module universe `uX` to `max uΓ uX`.
-/

noncomputable section
universe uΓ uA uA' uB uE u
namespace BC4lean.KKTheory.KasparovDescent

open scoped KasparovDescent

variable {Γ : Type uΓ} {A : Type uA} {A' : Type uA'} {B : Type uB}
  [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra A'] [PartialOrder A'] [StarOrderedRing A']
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]

variable (β : CStarAlgebraAction Γ B) (α : CStarAlgebraAction Γ A)
  (α' : CStarAlgebraAction Γ A')

section Raw
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- On the actual same descent module, ordinary even source precomposition
is intertwined by the identity coefficient-form unitary. -/
def evenCycleSourcePullbackIso (f : A' →⋆ₙₐ[ℂ] A)
    (hf : ∀ g a, f (α'.automorphism g a) = α.automorphism g (f a))
    (c : KasparovCycle α β E) :
    KasparovCycleIso
      (evenCycle β α' (NativeSourcePullback.evenCycle α' f hf c))
      (NativeSourcePullback.evenCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α')) (reducedCrossedMap α' α f hf)
        (fun _ _ => rfl) (evenCycle β α c)) where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine z x := by
    change reducedSourceRepresentation β E α' c.groupAction (c.representation.comp f)
        (representation_comp_equivariant β E α α' c.groupAction c.representation
          c.representation_equivariant f hf) z x =
      reducedSourceRepresentation β E α c.groupAction c.representation
        c.representation_equivariant (reducedCrossedMap α' α f hf z) x
    exact congrArg
      (fun ρ : ReducedCrossedProduct α' →⋆ₙₐ[ℂ]
        AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) => ρ z x)
      (reducedSourceRepresentation_comp β E α α' c.groupAction c.representation
        c.representation_equivariant f hf)
  operator_intertwine _ := rfl

/-- The actual ungraded odd source precomposition has the same identity-module
intertwiner; its completed source action equality is proved, not assumed. -/
def oddCycleSourcePullbackIso (f : A' →⋆ₙₐ[ℂ] A)
    (hf : ∀ g a, f (α'.automorphism g a) = α.automorphism g (f a))
    (c : OddKasparovCycle α β E) :
    OddKasparovCycleIso
      (oddCycle β α' (NativeSourcePullback.oddCycle α' f hf c))
      (NativeSourcePullback.oddCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α')) (reducedCrossedMap α' α f hf)
        (fun _ _ => rfl) (oddCycle β α c)) where
  moduleEquiv := HilbertModuleEquiv.refl
  action_intertwine _ _ := rfl
  representation_intertwine z x := by
    change reducedSourceRepresentation β E α' c.groupAction (c.representation.comp f)
        (representation_comp_equivariant β E α α' c.groupAction c.representation
          c.representation_equivariant f hf) z x =
      reducedSourceRepresentation β E α c.groupAction c.representation
        c.representation_equivariant (reducedCrossedMap α' α f hf z) x
    exact congrArg
      (fun ρ : ReducedCrossedProduct α' →⋆ₙₐ[ℂ]
        AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) => ρ z x)
      (reducedSourceRepresentation_comp β E α α' c.groupAction c.representation
        c.representation_equivariant f hf)
  operator_intertwine _ := rfl

end Raw

variable [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace A']

/-- Naturality for the existing native parity source homomorphism, including
the precise carrier universes required by its actual homomorphism-cycle
product. No general compatibility of descent with products is used. -/
theorem classHom_sourcePullback (p : Bool) (f : A' →⋆ₙₐ[ℂ] A)
    (hf : ∀ g a, f (α'.automorphism g a) = α.automorphism g (f a))
    (x : GroupUniverseParityGroup.KKParityGroup.{uΓ,uA,uB,
      max u (max uA' (max uA uB))} p α β) :
    classHom β α' p
        (GroupUniverseParityFunctoriality.sourcePullbackHom.{uΓ,uA',uA,uB,u}
          p f hf x) =
      GroupUniverseParityFunctoriality.sourcePullbackHom.{0,max uΓ uA',max uΓ uA,
        max uΓ uB,max u uΓ} p (reducedCrossedMap α' α f hf) (fun _ _ => rfl)
        (classHom β α p x) := by
  cases p
  · dsimp only [GroupUniverseParityGroup.KKParityGroup] at x
    change evenClass β α'
        (GroupUniverseParityFunctoriality.sourcePullback.{uΓ,uA',uA,uB,u}
          false f hf x) =
      GroupUniverseParityFunctoriality.sourcePullback.{0,max uΓ uA',max uΓ uA,
        max uΓ uB,max u uΓ} false (reducedCrossedMap α' α f hf) (fun _ _ => rfl)
        (evenClass β α x)
    refine Quotient.inductionOn' x ?_
    intro c
    have hs := NativeSourcePullback.even_mk.{uΓ,uA,uA',uB,u}
      (Γ := Γ) (A := A) (A' := A') (B := B) (α := α) (β := β) α' f hf c
    have ht := NativeSourcePullback.even_mk.{0,max uΓ uA,max uΓ uA',max uΓ uB,max u uΓ}
      (Γ := Unit) (A := ReducedCrossedProduct α) (A' := ReducedCrossedProduct α')
      (B := ReducedCrossedProduct β)
      (α := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α)))
      (β := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β)))
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α'))
      (reducedCrossedMap α' α f hf) (fun _ _ => rfl) (bundledEvenCycle β α c)
    exact (congrArg (evenClass β α') hs).trans
      ((KasparovHomotopyClass.mk_eq_of_iso
        (evenCycleSourcePullbackIso β α α' f hf c.cycle)).trans ht.symm)
  · dsimp only [GroupUniverseParityGroup.KKParityGroup] at x
    change oddClass β α'
        (GroupUniverseParityFunctoriality.sourcePullback.{uΓ,uA',uA,uB,u}
          true f hf x) =
      GroupUniverseParityFunctoriality.sourcePullback.{0,max uΓ uA',max uΓ uA,
        max uΓ uB,max u uΓ} true (reducedCrossedMap α' α f hf) (fun _ _ => rfl)
        (oddClass β α x)
    refine Quotient.inductionOn' x ?_
    intro c
    have hs := NativeSourcePullback.odd_mk.{uΓ,uA',uA,uB,u}
      (Γ := Γ) (A := A) (A' := A') (B := B) (α := α) (β := β) α' f hf c
    have ht := NativeSourcePullback.odd_mk.{0,max uΓ uA',max uΓ uA,max uΓ uB,max u uΓ}
      (Γ := Unit) (A := ReducedCrossedProduct α) (A' := ReducedCrossedProduct α')
      (B := ReducedCrossedProduct β)
      (α := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α)))
      (β := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β)))
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α'))
      (reducedCrossedMap α' α f hf) (fun _ _ => rfl) (bundledOddCycle β α c)
    exact (congrArg (oddClass β α') hs).trans
      ((OddKK.mk_eq_of_iso (oddCycleSourcePullbackIso β α α' f hf c.cycle)).trans ht.symm)

end BC4lean.KKTheory.KasparovDescent
