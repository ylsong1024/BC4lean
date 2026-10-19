import BC4lean.GroupUniverseParityMapCoherence

/-! # Native odd source pullback on actual cycle representatives

Precomposition keeps the complete Hilbert module, equivariant action and
Fredholm operator. The same identity module map compares its Clifford
expansion with the existing graded source pullback. The native parity map
therefore has this concrete representative, by its established graded
coherence theorem and the injective Clifford-coordinate bridge.


-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

noncomputable section
universe uΓ uA' uA uB uE u
namespace BC4lean.KKTheory.NativeSourcePullback

variable {Γ : Type uΓ} {A' : Type uA'} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A'] [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

section Raw

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- The actual odd cycle obtained by precomposing the representation. -/
def oddCycle (α' : CStarAlgebraAction Γ A') (f : A' →⋆ₙₐ[ℂ] A)
    (hf : ∀ g a, f (α'.automorphism g a) = α.automorphism g (f a))
    (c : OddKasparovCycle α β E) : OddKasparovCycle α' β E where
  countablyGenerated := c.countablyGenerated
  groupAction := c.groupAction
  representation := c.representation.comp f
  representation_equivariant g a := by
    change c.groupAction.conjugateOperator g (c.representation (f a)) =
      c.representation (f (α'.automorphism g a))
    rw [hf]
    exact c.representation_equivariant g (f a)
  operator := c.operator
  selfadjoint_mod_compact a := c.selfadjoint_mod_compact (f a)
  square_mod_compact a := c.square_mod_compact (f a)
  commutator_compact a := c.commutator_compact (f a)
  equivariance_mod_compact g a := c.equivariance_mod_compact g (f a)

@[simp] theorem oddCycle_representation (α' : CStarAlgebraAction Γ A')
    (f : A' →⋆ₙₐ[ℂ] A)
    (hf : ∀ g a, f (α'.automorphism g a) = α.automorphism g (f a))
    (c : OddKasparovCycle α β E) (a : A') :
    (oddCycle α' f hf c).representation a = c.representation (f a) := rfl

@[simp] theorem oddCycle_operator (α' : CStarAlgebraAction Γ A')
    (f : A' →⋆ₙₐ[ℂ] A)
    (hf : ∀ g a, f (α'.automorphism g a) = α.automorphism g (f a))
    (c : OddKasparovCycle α β E) :
    (oddCycle α' f hf c).operator = c.operator := rfl

/-- Clifford expansion commutes with actual precomposition through the
identity equivalence of the whole Clifford pair module. -/
def oddCycle_cliffordExpansionIso (α' : CStarAlgebraAction Γ A')
    (f : A' →⋆ₙₐ[ℂ] A)
    (hf : ∀ g a, f (α'.automorphism g a) = α.automorphism g (f a))
    (c : OddKasparovCycle α β E) :
    GradedKasparovCycleIso (oddCycle α' f hf c).cliffordExpansion
      (c.cliffordExpansion.sourcePullback α' CStarGrading.trivial
        α'.preservesGrading_trivial f hf (fun _ => rfl)) where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

end Raw

section Classes

variable [Countable Γ] [PartialOrder A] [StarOrderedRing A]
  [TopologicalSpace.SeparableSpace A'] [TopologicalSpace.SeparableSpace A]
  [TopologicalSpace.SeparableSpace B]

/-- The existing native odd pullback is represented by the same complete
module and Fredholm operator with representation precomposed by `f`. -/
theorem odd_mk (α' : CStarAlgebraAction Γ A') (f : A' →⋆ₙₐ[ℂ] A)
    (hf : ∀ g a, f (α'.automorphism g a) = α.automorphism g (f a))
    (c : BundledOddKasparovCycle.{uΓ,uA,uB,max u (max uA' (max uA uB))} α β) :
    GroupUniverseParityFunctoriality.sourcePullback.{uΓ,uA',uA,uB,u}
      true f hf (OddKK.mk c) =
    OddKK.mk (BundledOddKasparovCycle.of (oddCycle α' f hf c.cycle)) := by
  apply GroupUniverseCliffordCoordinateBridge.gradedOddClass_injective
  rw [GroupUniverseParityFunctoriality.sourcePullback_graded_odd]
  simp only [GroupUniverseCliffordCoordinateBridge.gradedOddClass_mk]
  exact (GradedKasparovHomotopyClass.mk_eq_of_iso
    (oddCycle_cliffordExpansionIso α' f hf c.cycle)).symm

end Classes

end BC4lean.KKTheory.NativeSourcePullback
