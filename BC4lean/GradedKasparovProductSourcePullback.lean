import BC4lean.GradedKasparovSourcePullback
import BC4lean.GradedKasparovProductCriterion

/-! # Genuine product criteria respect source precomposition

An actual graded-equivariant nonunital source homomorphism precomposes the
first representation. The actual tensor module, grading, action, first
operator and connection remain the same. All localized cycle and positivity
conditions are the original conditions at the image of the source element.
The resulting whole product cycle is the actual precomposed product cycle.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ A A' B C E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}
  (α' : CStarAlgebraAction Γ A') (δA' : CStarGrading A')
  (hα' : α'.PreservesGrading δA') (f : A' →⋆ₙₐ[ℂ] A)
  (hact : ∀ g a, f (α'.automorphism g a) = α.automorphism g (f a))
  (hgrade : ∀ a, f (δA'.automorphism a) = δA.automorphism (f a))
  (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F)

theorem gradedKasparovProductSourcePullback_conditions
    {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)}
    (hR : GradedKasparovTensorOperatorConditions c d R) :
    GradedKasparovTensorOperatorConditions (c.sourcePullback α' δA' hα' f hact hgrade) d R where
  operator_odd := hR.operator_odd
  selfadjoint_mod_compact a := hR.selfadjoint_mod_compact (f a)
  square_mod_compact a := hR.square_mod_compact (f a)
  commutator_compact a := by
    change IsModuleCompact (R * gradedKasparovTensorRepresentation c d (f a) -
      gradedKasparovTensorRepresentation c d (f (δA'.automorphism a)) * R)
    rw [hgrade]
    exact hR.commutator_compact (f a)
  equivariance_mod_compact g a := hR.equivariance_mod_compact g (f a)

@[simp] theorem gradedKasparovProductSourcePullback_positivityOperator
    (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) (a : A') :
    gradedKasparovProductPositivityOperator (c.sourcePullback α' δA' hα' f hact hgrade) d R a =
      gradedKasparovProductPositivityOperator c d R (f a) := rfl

/-- A genuine product for arbitrary original cycles remains a genuine
product after precomposition with an actual graded-equivariant source hom. -/
theorem gradedKasparovProductSourcePullback_isProduct
    {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)}
    (hR : IsGradedKasparovProductOperator c d R) :
    IsGradedKasparovProductOperator (c.sourcePullback α' δA' hα' f hact hgrade) d R where
  cycleConditions := gradedKasparovProductSourcePullback_conditions α' δA' hα' f hact hgrade c d
    hR.cycleConditions
  connection := {
    even := fun x hx => hR.connection.even x hx
    even_adjoint := fun x hx => hR.connection.even_adjoint x hx
    odd := fun x hx => hR.connection.odd x hx
    odd_adjoint := fun x hx => hR.connection.odd_adjoint x hx
  }
  positivity a := hR.positivity (f a)

/-- The actual product cycle after source precomposition is intertwined
with the source precomposition of the original whole product cycle. -/
def gradedKasparovProductSourcePullback_cycleIso
    {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)}
    (hR : IsGradedKasparovProductOperator c d R) :
    GradedKasparovCycleIso
      ((gradedKasparovTensorCycleOfConditions c d R hR.cycleConditions).sourcePullback
        α' δA' hα' f hact hgrade)
      (gradedKasparovTensorCycleOfConditions (c.sourcePullback α' δA' hα' f hact hgrade) d R
        (gradedKasparovProductSourcePullback_isProduct α' δA' hα' f hact hgrade c d hR).cycleConditions) where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

end BC4lean.KKTheory
