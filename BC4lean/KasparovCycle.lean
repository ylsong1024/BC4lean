import BC4lean.CompactModuleOperator
import BC4lean.EquivariantHilbertModule
import BC4lean.CountablyGeneratedModule

/-! # Even equivariant Kasparov cycles for trivially graded algebras

The coefficient and source algebras here are complex, possibly nonunital, and
trivially graded. The module is genuinely Z/2-graded. Representations may be
degenerate. Equivariance of the Fredholm operator is required only modulo
compact module operators after multiplication by the representation.

For applications to ordinary KK-theory, A and B are separable and the acting
group is countable and discrete. Those restrictions are not needed to state
the raw cycle conditions. This file constructs cycle data; a homotopy quotient,
the group laws, Kasparov products and the K-theory comparison are separate
mathematical constructions and are not asserted here.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ A B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- The compactness conditions for an even equivariant Kasparov cycle over
trivially graded A and B, on a specified complete right Hilbert B-module E. -/
structure KasparovCycle (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
    [CStarModule Bᵐᵒᵖ E] [CompleteSpace E] where
  countablyGenerated : IsCountablyGeneratedModule B E
  grading : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E
  groupAction : EquivariantHilbertModule β E
  grading_preserved : groupAction.PreservesGrading grading
  representation : A →⋆ₙₐ[ℂ] AdjointableMap B E E
  representation_even : ∀ a, grading.IsEven grading (representation a)
  representation_equivariant : ∀ g a,
    groupAction.conjugateOperator g (representation a) = representation (α.automorphism g a)
  operator : AdjointableMap B E E
  operator_odd : grading.IsOdd grading operator
  selfadjoint_mod_compact : ∀ a,
    IsModuleCompact ((operator - star operator) * representation a)
  square_mod_compact : ∀ a,
    IsModuleCompact ((operator * operator - 1) * representation a)
  commutator_compact : ∀ a,
    IsModuleCompact (operator * representation a - representation a * operator)
  equivariance_mod_compact : ∀ g a,
    IsModuleCompact ((groupAction.conjugateOperator g operator - operator) * representation a)

namespace KasparovCycle

variable {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

/-- Degeneracy is exact vanishing of every cycle defect. It is stronger than
compactness; its class vanishing in KK requires an actual homotopy proof. -/
def IsDegenerate (c : KasparovCycle α β E) : Prop :=
  (∀ a, (c.operator - star c.operator) * c.representation a = 0) ∧
  (∀ a, (c.operator * c.operator - 1) * c.representation a = 0) ∧
  (∀ a, c.operator * c.representation a - c.representation a * c.operator = 0) ∧
  (∀ g a, (c.groupAction.conjugateOperator g c.operator - c.operator) *
    c.representation a = 0)

/-- A degenerate cycle has vanishing commutator with its representation. -/
theorem commutes_of_isDegenerate (c : KasparovCycle α β E) (h : c.IsDegenerate) (a : A) :
    c.operator * c.representation a = c.representation a * c.operator :=
  sub_eq_zero.mp (h.2.2.1 a)

/-- A zero representation with zero operator is a degenerate even cycle on any
countably generated equivariant graded Hilbert module. -/
def zeroRepresentation
    (hE : IsCountablyGeneratedModule B E)
    (γ : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E)
    (U : EquivariantHilbertModule β E) (hU : U.PreservesGrading γ) :
    KasparovCycle α β E where
  countablyGenerated := hE
  grading := γ
  groupAction := U
  grading_preserved := hU
  representation := 0
  representation_even := by intro a x; simp
  representation_equivariant := by intro g a; exact U.conjugateOperator_zero g
  operator := 0
  operator_odd := by intro x; simp
  selfadjoint_mod_compact := by intro a; simpa using IsModuleCompact.zero (B := B) (E := E) (F := E)
  square_mod_compact := by intro a; simpa using IsModuleCompact.zero (B := B) (E := E) (F := E)
  commutator_compact := by intro a; simpa using IsModuleCompact.zero (B := B) (E := E) (F := E)
  equivariance_mod_compact := by intro g a; simpa using IsModuleCompact.zero (B := B) (E := E) (F := E)

/-- The zero-representation example satisfies exact degeneracy. -/
theorem zeroRepresentation_isDegenerate
    (hE : IsCountablyGeneratedModule B E)
    (γ : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E)
    (U : EquivariantHilbertModule β E) (hU : U.PreservesGrading γ) :
    (zeroRepresentation (α := α) hE γ U hU).IsDegenerate := by
  constructor
  · intro a; simp [zeroRepresentation]
  constructor
  · intro a; simp [zeroRepresentation]
  constructor
  · intro a; simp [zeroRepresentation]
  · intro g a; simp [zeroRepresentation]

end KasparovCycle

/-- The ungraded Fredholm picture of an odd equivariant Kasparov cycle for
trivially graded A and B. Its identification with the Clifford-graded picture
is a further theorem, not part of this data structure. -/
structure OddKasparovCycle (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
    [CStarModule Bᵐᵒᵖ E] [CompleteSpace E] where
  countablyGenerated : IsCountablyGeneratedModule B E
  groupAction : EquivariantHilbertModule β E
  representation : A →⋆ₙₐ[ℂ] AdjointableMap B E E
  representation_equivariant : ∀ g a,
    groupAction.conjugateOperator g (representation a) = representation (α.automorphism g a)
  operator : AdjointableMap B E E
  selfadjoint_mod_compact : ∀ a,
    IsModuleCompact ((operator - star operator) * representation a)
  square_mod_compact : ∀ a,
    IsModuleCompact ((operator * operator - 1) * representation a)
  commutator_compact : ∀ a,
    IsModuleCompact (operator * representation a - representation a * operator)
  equivariance_mod_compact : ∀ g a,
    IsModuleCompact ((groupAction.conjugateOperator g operator - operator) * representation a)

namespace OddKasparovCycle

variable {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

/-- Exact vanishing of every defect in the odd-cycle picture. -/
def IsDegenerate (c : OddKasparovCycle α β E) : Prop :=
  (∀ a, (c.operator - star c.operator) * c.representation a = 0) ∧
  (∀ a, (c.operator * c.operator - 1) * c.representation a = 0) ∧
  (∀ a, c.operator * c.representation a - c.representation a * c.operator = 0) ∧
  (∀ g a, (c.groupAction.conjugateOperator g c.operator - c.operator) *
    c.representation a = 0)

/-- A degenerate odd cycle commutes with its representation. -/
theorem commutes_of_isDegenerate (c : OddKasparovCycle α β E) (h : c.IsDegenerate) (a : A) :
    c.operator * c.representation a = c.representation a * c.operator :=
  sub_eq_zero.mp (h.2.2.1 a)

/-- The zero representation/operator is a degenerate odd cycle. -/
def zeroRepresentation (hE : IsCountablyGeneratedModule B E)
    (U : EquivariantHilbertModule β E) : OddKasparovCycle α β E where
  countablyGenerated := hE
  groupAction := U
  representation := 0
  representation_equivariant := by intro g a; exact U.conjugateOperator_zero g
  operator := 0
  selfadjoint_mod_compact := by intro a; simpa using IsModuleCompact.zero (B := B) (E := E) (F := E)
  square_mod_compact := by intro a; simpa using IsModuleCompact.zero (B := B) (E := E) (F := E)
  commutator_compact := by intro a; simpa using IsModuleCompact.zero (B := B) (E := E) (F := E)
  equivariance_mod_compact := by intro g a; simpa using IsModuleCompact.zero (B := B) (E := E) (F := E)

/-- All defects of the odd zero-representation example vanish exactly. -/
theorem zeroRepresentation_isDegenerate (hE : IsCountablyGeneratedModule B E)
    (U : EquivariantHilbertModule β E) :
    (zeroRepresentation (α := α) hE U).IsDegenerate := by
  constructor
  · intro a; simp [zeroRepresentation]
  constructor
  · intro a; simp [zeroRepresentation]
  constructor
  · intro a; simp [zeroRepresentation]
  · intro g a; simp [zeroRepresentation]

end OddKasparovCycle
end BC4lean.KKTheory
