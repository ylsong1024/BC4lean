import BC4lean.KasparovCycle

/-! # Even equivariant Kasparov cycles over graded C⋆-algebras

Both algebra gradings are explicit involutive star automorphisms. The group
actions preserve them, the Hilbert-module grading twists the coefficient
action, and the representation intertwines the source and module gradings.
The Fredholm operator is odd. The commutator uses the source grading:
`F φ(a) - φ(grade_A a) F`. The other three localized compact defects retain
their ordinary formulas. Completeness and countable generation are required.

As for `KasparovCycle`, the algebras may be nonunital and representations may
be degenerate. Separability of the algebras and countability and discreteness
of the group are ambient assumptions in ordinary equivariant KK-theory; the
raw cycle laws hold without them. This file proves that the existing raw
definition is exactly the specialization to trivial algebra gradings.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ A B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- Genuine even graded cycle data on a specified complete Hilbert module.
Every compactness condition uses the actual module compact operators. -/
structure GradedKasparovCycle (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B)
    (δA : CStarGrading A) (δB : CStarGrading B)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
    [CStarModule Bᵐᵒᵖ E] [CompleteSpace E] where
  sourceAction_preservesGrading : α.PreservesGrading δA
  coefficientAction_preservesGrading : β.PreservesGrading δB
  countablyGenerated : IsCountablyGeneratedModule B E
  grading : GradedHilbertModule δB E
  groupAction : EquivariantHilbertModule β E
  grading_preserved : groupAction.PreservesGrading grading
  representation : A →⋆ₙₐ[ℂ] AdjointableMap B E E
  representation_graded : ∀ a x,
    grading.grading (representation a x) = representation (δA.automorphism a) (grading.grading x)
  representation_equivariant : ∀ g a,
    groupAction.conjugateOperator g (representation a) = representation (α.automorphism g a)
  operator : AdjointableMap B E E
  operator_odd : grading.IsOdd grading operator
  selfadjoint_mod_compact : ∀ a,
    IsModuleCompact ((operator - star operator) * representation a)
  square_mod_compact : ∀ a,
    IsModuleCompact ((operator * operator - 1) * representation a)
  commutator_compact : ∀ a,
    IsModuleCompact (operator * representation a - representation (δA.automorphism a) * operator)
  equivariance_mod_compact : ∀ g a,
    IsModuleCompact ((groupAction.conjugateOperator g operator - operator) * representation a)

namespace GradedKasparovCycle

variable {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

/-- Exact degeneracy uses the graded commutator appropriate to the source. -/
def IsDegenerate (c : GradedKasparovCycle α β δA δB E) : Prop :=
  (∀ a, (c.operator - star c.operator) * c.representation a = 0) ∧
  (∀ a, (c.operator * c.operator - 1) * c.representation a = 0) ∧
  (∀ a, c.operator * c.representation a -
    c.representation (δA.automorphism a) * c.operator = 0) ∧
  (∀ g a, (c.groupAction.conjugateOperator g c.operator - c.operator) *
    c.representation a = 0)

/-- A degenerate graded cycle graded-commutes with its representation. -/
theorem graded_commutes_of_isDegenerate (c : GradedKasparovCycle α β δA δB E)
    (h : c.IsDegenerate) (a : A) :
    c.operator * c.representation a = c.representation (δA.automorphism a) * c.operator :=
  sub_eq_zero.mp (h.2.2.1 a)

/-- Even elements of the source algebra act by even module operators. -/
theorem representation_even_of_even (c : GradedKasparovCycle α β δA δB E)
    (a : A) (ha : δA.automorphism a = a) :
    c.grading.IsEven c.grading (c.representation a) := by
  intro x
  rw [c.representation_graded, ha]

/-- Odd elements of the source algebra act by odd module operators. -/
theorem representation_odd_of_odd (c : GradedKasparovCycle α β δA δB E)
    (a : A) (ha : δA.automorphism a = -a) :
    c.grading.IsOdd c.grading (c.representation a) := by
  intro x
  rw [c.representation_graded, ha, map_neg, AdjointableMap.coe_neg_apply]

/-- An existing cycle is a graded cycle for the trivial source and
coefficient gradings, with its actual module and operator unchanged. -/
def ofKasparovCycle (c : KasparovCycle α β E) :
    GradedKasparovCycle α β CStarGrading.trivial CStarGrading.trivial E where
  sourceAction_preservesGrading := α.preservesGrading_trivial
  coefficientAction_preservesGrading := β.preservesGrading_trivial
  countablyGenerated := c.countablyGenerated
  grading := c.grading
  groupAction := c.groupAction
  grading_preserved := c.grading_preserved
  representation := c.representation
  representation_graded := c.representation_even
  representation_equivariant := c.representation_equivariant
  operator := c.operator
  operator_odd := c.operator_odd
  selfadjoint_mod_compact := c.selfadjoint_mod_compact
  square_mod_compact := c.square_mod_compact
  commutator_compact := c.commutator_compact
  equivariance_mod_compact := c.equivariance_mod_compact

/-- The trivial algebra-grading specialization gives exactly the existing
raw even cycle laws. -/
def toKasparovCycle
    (c : GradedKasparovCycle α β CStarGrading.trivial CStarGrading.trivial E) :
    KasparovCycle α β E where
  countablyGenerated := c.countablyGenerated
  grading := c.grading
  groupAction := c.groupAction
  grading_preserved := c.grading_preserved
  representation := c.representation
  representation_even := c.representation_graded
  representation_equivariant := c.representation_equivariant
  operator := c.operator
  operator_odd := c.operator_odd
  selfadjoint_mod_compact := c.selfadjoint_mod_compact
  square_mod_compact := c.square_mod_compact
  commutator_compact := c.commutator_compact
  equivariance_mod_compact := c.equivariance_mod_compact

@[simp] theorem toKasparovCycle_ofKasparovCycle (c : KasparovCycle α β E) :
    (ofKasparovCycle c).toKasparovCycle = c := by cases c; rfl

@[simp] theorem ofKasparovCycle_toKasparovCycle
    (c : GradedKasparovCycle α β CStarGrading.trivial CStarGrading.trivial E) :
    ofKasparovCycle c.toKasparovCycle = c := by cases c; rfl

/-- Exact equivalence of the old raw cycle type and the trivial algebra
grading specialization; neither direction assumes a parity equivalence. -/
def trivialEquiv : KasparovCycle α β E ≃
    GradedKasparovCycle α β CStarGrading.trivial CStarGrading.trivial E where
  toFun := ofKasparovCycle
  invFun := toKasparovCycle
  left_inv := toKasparovCycle_ofKasparovCycle
  right_inv := ofKasparovCycle_toKasparovCycle

@[simp] theorem toKasparovCycle_isDegenerate_iff
    (c : GradedKasparovCycle α β CStarGrading.trivial CStarGrading.trivial E) :
    c.toKasparovCycle.IsDegenerate ↔ c.IsDegenerate := Iff.rfl

@[simp] theorem ofKasparovCycle_isDegenerate_iff (c : KasparovCycle α β E) :
    (ofKasparovCycle c).IsDegenerate ↔ c.IsDegenerate := Iff.rfl

end GradedKasparovCycle
end BC4lean.KKTheory
