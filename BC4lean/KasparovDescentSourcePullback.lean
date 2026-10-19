import BC4lean.KasparovDescentGradedCycle
import BC4lean.ReducedCrossedProductMap
import BC4lean.GradedKasparovSourcePullback

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Concrete reduced descent commutes with actual source precomposition

The construction imports the concrete reduced crossed map, source
representation and fully graded descended cycle.


The given equivariant nonunital source homomorphism is precomposed with the
original representation. Its actual reduced source representation equals
composition with the constructed reduced crossed map: both maps agree on
every genuine generator and hence on the completed algebra. The same dense
generator argument transports the original source grading. Finally the
identity of the actual descended coefficient module intertwines every part
of the two genuine graded raw cycles.

No completed representation, source-naturality field, or cycle isomorphism
is assumed. The original representations may be degenerate.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent CStarAlgebra

variable {Γ A A' B : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra A'] [PartialOrder A'] [StarOrderedRing A']
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable (β : CStarAlgebraAction Γ B) (E : Type*)
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  (α : CStarAlgebraAction Γ A) (α' : CStarAlgebraAction Γ A')

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder A'] [StarOrderedRing A']
  [StarOrderedRing B] [CompleteSpace E] in
/-- Actual representation precomposition preserves the given equivariance law. -/
theorem representation_comp_equivariant
    (U : EquivariantHilbertModule β E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))
    (f : A' →⋆ₙₐ[ℂ] A)
    (hf : ∀ g a, f (α'.automorphism g a) = α.automorphism g (f a)) :
    ∀ g a, U.conjugateOperator g ((π.comp f) a) =
      (π.comp f) (α'.automorphism g a) := by
  intro g a
  change U.conjugateOperator g (π (f a)) = π (f (α'.automorphism g a))
  rw [hf g a]
  exact hπ g (f a)

/-- The two actual completed source homomorphisms agree on the concrete
regular generators; the reduced crossed homomorphism extensionality theorem
then supplies equality on the genuine completion. -/
theorem reducedSourceRepresentation_comp
    (U : EquivariantHilbertModule β E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))
    (f : A' →⋆ₙₐ[ℂ] A)
    (hf : ∀ g a, f (α'.automorphism g a) = α.automorphism g (f a)) :
    reducedSourceRepresentation β E α' U (π.comp f)
        (representation_comp_equivariant β E α α' U π hπ f hf) =
      (reducedSourceRepresentation β E α U π hπ).comp
        (reducedCrossedMap α' α f hf) := by
  apply reducedCrossedHom_ext α'
  intro a g
  let p : ReducedCrossedProduct α' :=
    ⟨reducedCrossedGenerator α' a g, reducedCrossedGenerator_mem α' a g⟩
  let q : ReducedCrossedProduct α :=
    ⟨reducedCrossedGenerator α (f a) g, reducedCrossedGenerator_mem α (f a) g⟩
  let r : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) :=
    sourceGenerator β E U π (f a) g
  have hs : reducedSourceRepresentation β E α' U (π.comp f)
      (representation_comp_equivariant β E α α' U π hπ f hf) p = r :=
    reducedSourceRepresentation_generator β E α' U (π.comp f)
      (representation_comp_equivariant β E α α' U π hπ f hf) a g
  have hm : reducedCrossedMap α' α f hf p = q :=
    reducedCrossedMap_generator α' α f hf a g
  have ht : reducedSourceRepresentation β E α U π hπ q = r :=
    reducedSourceRepresentation_generator β E α U π hπ (f a) g
  exact hs.trans
    ((congrArg
      (fun w : ReducedCrossedProduct α => reducedSourceRepresentation β E α U π hπ w) hm).trans ht).symm

/-- The original graded homomorphism law is preserved by the actual crossed
map, first on finite generators and then by actual reduced-norm density. -/
theorem reducedCrossedMap_graded
    (δA : CStarGrading A) (δA' : CStarGrading A')
    (hα : α.PreservesGrading δA) (hα' : α'.PreservesGrading δA')
    (f : A' →⋆ₙₐ[ℂ] A)
    (hf : ∀ g a, f (α'.automorphism g a) = α.automorphism g (f a))
    (hgrade : ∀ a, f (δA'.automorphism a) = δA.automorphism (f a))
    (z : ReducedCrossedProduct α') :
    reducedCrossedMap α' α f hf
        ((reducedCrossedProductGrading α' δA' hα').automorphism z) =
      (reducedCrossedProductGrading α δA hα).automorphism
        (reducedCrossedMap α' α f hf z) := by
  let φ := reducedCrossedMap α' α f hf
  let σ := (reducedCrossedProductGrading α δA hα).automorphism
  let σ' := (reducedCrossedProductGrading α' δA' hα').automorphism
  have hfinite : ∀ b : AlgebraicCrossedProduct α',
      φ (σ' (algebraicToReducedCrossed α' b)) =
        σ (φ (algebraicToReducedCrossed α' b)) := by
    intro b
    induction b using AlgebraicCrossedProduct.induction_on α' with
    | zero => simp only [map_zero]
    | single g a =>
      change reducedCrossedMap α' α f hf
          ((reducedCrossedProductGrading α' δA' hα').automorphism
            (algebraicToReducedCrossed α' (AlgebraicCrossedProduct.single α' g a))) =
        (reducedCrossedProductGrading α δA hα).automorphism
          (reducedCrossedMap α' α f hf
            (algebraicToReducedCrossed α' (AlgebraicCrossedProduct.single α' g a)))
      rw [crossedGrading_single, reducedCrossedMap_algebraic,
        AlgebraicCrossedProduct.map_single, reducedCrossedMap_algebraic,
        AlgebraicCrossedProduct.map_single, crossedGrading_single, hgrade a]
    | add b d ihb ihd =>
      simpa only [map_add] using congrArg₂ (· + ·) ihb ihd
  exact (algebraicToReducedCrossed_denseRange α').induction_on z
    (isClosed_eq
      ((map_continuous φ).comp (StarAlgEquiv.isometry σ').continuous)
      ((StarAlgEquiv.isometry σ).continuous.comp (map_continuous φ))) hfinite

variable [Countable Γ] [TopologicalSpace.SeparableSpace B]
  {δA : CStarGrading A} {δB : CStarGrading B}

/-- Descent of the native raw source pullback is genuinely isomorphic to the
native source pullback of the actual descended graded cycle. The same module,
its semilinear grading, its Unit action and Fredholm operator are retained. -/
def gradedCycleSourcePullbackIso
    (δA' : CStarGrading A') (hα' : α'.PreservesGrading δA')
    (f : A' →⋆ₙₐ[ℂ] A)
    (hf : ∀ g a, f (α'.automorphism g a) = α.automorphism g (f a))
    (hgrade : ∀ a, f (δA'.automorphism a) = δA.automorphism (f a))
    (c : GradedKasparovCycle α β δA δB E) :
    GradedKasparovCycleIso
      (gradedCycle β α' (c.sourcePullback α' δA' hα' f hf hgrade))
      ((gradedCycle β α c).sourcePullback
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α'))
        (reducedCrossedProductGrading α' δA' hα') (fun _ _ => rfl)
        (reducedCrossedMap α' α f hf) (fun _ _ => rfl)
        (reducedCrossedMap_graded α α' δA δA'
          c.sourceAction_preservesGrading hα' f hf hgrade)) where
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

end BC4lean.KKTheory.KasparovDescent
