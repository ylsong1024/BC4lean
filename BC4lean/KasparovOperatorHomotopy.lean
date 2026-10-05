import BC4lean.KasparovCycle
import Mathlib.Topology.Path

/-! # Operator homotopies on a fixed Kasparov module

This file studies norm-continuous paths of Fredholm operators while the Hilbert
module, grading, representation and group action remain fixed. Every point of
the path satisfies oddness and all four compactness conditions, and therefore
defines a raw Kasparov cycle.

This is operator homotopy groundwork. No identification with homotopies over
an interval coefficient algebra, homotopy quotient, or KK group is asserted.
-/

noncomputable section
namespace BC4lean.KKTheory

open unitInterval

variable {Γ A B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace KasparovCycle

/-- The exact raw-cycle requirements for an operator on the fixed graded,
represented equivariant module underlying `c`. -/
structure OperatorConditions (c : KasparovCycle α β E)
    (T : AdjointableMap B E E) : Prop where
  operator_odd : c.grading.IsOdd c.grading T
  selfadjoint_mod_compact : ∀ a,
    IsModuleCompact ((T - star T) * c.representation a)
  square_mod_compact : ∀ a,
    IsModuleCompact ((T * T - 1) * c.representation a)
  commutator_compact : ∀ a,
    IsModuleCompact (T * c.representation a - c.representation a * T)
  equivariance_mod_compact : ∀ g a,
    IsModuleCompact ((c.groupAction.conjugateOperator g T - T) * c.representation a)

/-- The operator of a raw cycle satisfies its fixed-module operator conditions. -/
theorem operatorConditions (c : KasparovCycle α β E) :
    c.OperatorConditions c.operator where
  operator_odd := c.operator_odd
  selfadjoint_mod_compact := c.selfadjoint_mod_compact
  square_mod_compact := c.square_mod_compact
  commutator_compact := c.commutator_compact
  equivariance_mod_compact := c.equivariance_mod_compact

/-- Replace the Fredholm operator while retaining the complete fixed module data. -/
def withOperator (c : KasparovCycle α β E) (T : AdjointableMap B E E)
    (hT : c.OperatorConditions T) : KasparovCycle α β E :=
  { c with
    operator := T
    operator_odd := hT.operator_odd
    selfadjoint_mod_compact := hT.selfadjoint_mod_compact
    square_mod_compact := hT.square_mod_compact
    commutator_compact := hT.commutator_compact
    equivariance_mod_compact := hT.equivariance_mod_compact }

@[simp] theorem withOperator_operator (c : KasparovCycle α β E)
    (T : AdjointableMap B E E) (hT : c.OperatorConditions T) :
    (c.withOperator T hT).operator = T := rfl

@[simp] theorem withOperator_grading (c : KasparovCycle α β E)
    (T : AdjointableMap B E E) (hT : c.OperatorConditions T) :
    (c.withOperator T hT).grading = c.grading := rfl

@[simp] theorem withOperator_representation (c : KasparovCycle α β E)
    (T : AdjointableMap B E E) (hT : c.OperatorConditions T) :
    (c.withOperator T hT).representation = c.representation := rfl

@[simp] theorem withOperator_groupAction (c : KasparovCycle α β E)
    (T : AdjointableMap B E E) (hT : c.OperatorConditions T) :
    (c.withOperator T hT).groupAction = c.groupAction := rfl

@[simp] theorem withOperator_self (c : KasparovCycle α β E) :
    c.withOperator c.operator c.operatorConditions = c := by
  cases c
  rfl

end KasparovCycle

/-- An operator-norm-continuous path satisfying the raw Kasparov conditions on
one fixed graded, represented equivariant Hilbert module. The two endpoint
operators need not be the operator originally stored in `c`. -/
structure KasparovOperatorHomotopy (c : KasparovCycle α β E)
    (T₀ T₁ : AdjointableMap B E E) where
  path : Path T₀ T₁
  conditions : ∀ t : I, c.OperatorConditions (path t)

namespace KasparovOperatorHomotopy

variable {c : KasparovCycle α β E} {T₀ T₁ T₂ : AdjointableMap B E E}

/-- Equality of paths determines equality of fixed-module operator homotopies. -/
@[ext] theorem ext {h k : KasparovOperatorHomotopy c T₀ T₁}
    (hp : h.path = k.path) : h = k := by
  cases h
  cases k
  cases hp
  rfl

/-- Every parameter determines an actual raw Kasparov cycle. -/
def cycleAt (h : KasparovOperatorHomotopy c T₀ T₁) (t : I) : KasparovCycle α β E :=
  c.withOperator (h.path t) (h.conditions t)

@[simp] theorem cycleAt_operator (h : KasparovOperatorHomotopy c T₀ T₁) (t : I) :
    (h.cycleAt t).operator = h.path t := rfl

@[simp] theorem cycleAt_grading (h : KasparovOperatorHomotopy c T₀ T₁) (t : I) :
    (h.cycleAt t).grading = c.grading := rfl

@[simp] theorem cycleAt_representation (h : KasparovOperatorHomotopy c T₀ T₁) (t : I) :
    (h.cycleAt t).representation = c.representation := rfl

@[simp] theorem cycleAt_groupAction (h : KasparovOperatorHomotopy c T₀ T₁) (t : I) :
    (h.cycleAt t).groupAction = c.groupAction := rfl

/-- Continuity here is the operator-norm topology on adjointable maps. -/
theorem continuous_operator (h : KasparovOperatorHomotopy c T₀ T₁) :
    Continuous (fun t : I => (h.cycleAt t).operator) := h.path.continuous

/-- The same path is norm-continuous as a path of bounded complex-linear maps. -/
theorem continuous_toCLM (h : KasparovOperatorHomotopy c T₀ T₁) :
    Continuous (fun t : I => (h.path t).toCLM) :=
  AdjointableMap.toCLM_isometry.continuous.comp h.path.continuous

@[simp] theorem source_operator (h : KasparovOperatorHomotopy c T₀ T₁) :
    (h.cycleAt 0).operator = T₀ := h.path.source

@[simp] theorem target_operator (h : KasparovOperatorHomotopy c T₀ T₁) :
    (h.cycleAt 1).operator = T₁ := h.path.target

/-- The initial operator satisfies the raw-cycle conditions on the fixed module. -/
theorem source_conditions (h : KasparovOperatorHomotopy c T₀ T₁) :
    c.OperatorConditions T₀ := by
  simpa only [Path.source] using h.conditions 0

/-- The terminal operator satisfies the raw-cycle conditions on the fixed module. -/
theorem target_conditions (h : KasparovOperatorHomotopy c T₀ T₁) :
    c.OperatorConditions T₁ := by
  simpa only [Path.target] using h.conditions 1

/-- The initial cycle is reconstructed with the initial operator and fixed data. -/
@[simp] theorem source_cycleAt (h : KasparovOperatorHomotopy c T₀ T₁) :
    h.cycleAt 0 = c.withOperator T₀ h.source_conditions := by
  simp only [cycleAt, Path.source]

/-- The terminal cycle is reconstructed with the terminal operator and fixed data. -/
@[simp] theorem target_cycleAt (h : KasparovOperatorHomotopy c T₀ T₁) :
    h.cycleAt 1 = c.withOperator T₁ h.target_conditions := by
  simp only [cycleAt, Path.target]

/-- A constant admissible operator gives a fixed-module operator homotopy. -/
def constant (c : KasparovCycle α β E) (T : AdjointableMap B E E)
    (hT : c.OperatorConditions T) : KasparovOperatorHomotopy c T T where
  path := Path.refl T
  conditions _ := hT

/-- The reflexive operator homotopy of any raw cycle. -/
def refl (c : KasparovCycle α β E) :
    KasparovOperatorHomotopy c c.operator c.operator :=
  constant c c.operator c.operatorConditions

@[simp] theorem constant_cycleAt (c : KasparovCycle α β E)
    (T : AdjointableMap B E E) (hT : c.OperatorConditions T) (t : I) :
    (constant c T hT).cycleAt t = c.withOperator T hT := rfl

@[simp] theorem refl_cycleAt (c : KasparovCycle α β E) (t : I) :
    (refl c).cycleAt t = c := by
  exact c.withOperator_self

/-- Reverse the operator path, keeping the fixed module data. -/
def symm (h : KasparovOperatorHomotopy c T₀ T₁) :
    KasparovOperatorHomotopy c T₁ T₀ where
  path := h.path.symm
  conditions t := h.conditions (unitInterval.symm t)

@[simp] theorem symm_path (h : KasparovOperatorHomotopy c T₀ T₁) :
    h.symm.path = h.path.symm := rfl

@[simp] theorem symm_cycleAt (h : KasparovOperatorHomotopy c T₀ T₁) (t : I) :
    h.symm.cycleAt t = h.cycleAt (unitInterval.symm t) := rfl

@[simp] theorem symm_symm (h : KasparovOperatorHomotopy c T₀ T₁) :
    h.symm.symm = h := ext (Path.symm_symm h.path)

/-- Concatenate operator paths whose middle operator agrees. All raw-cycle
conditions persist because the new path has the union of the original ranges. -/
def trans (h : KasparovOperatorHomotopy c T₀ T₁)
    (k : KasparovOperatorHomotopy c T₁ T₂) : KasparovOperatorHomotopy c T₀ T₂ where
  path := h.path.trans k.path
  conditions t := by
    have ht : (h.path.trans k.path) t ∈ Set.range (h.path.trans k.path) :=
      Set.mem_range_self t
    rw [Path.trans_range] at ht
    rcases ht with ⟨s, hs⟩ | ⟨s, hs⟩
    · rw [← hs]
      exact h.conditions s
    · rw [← hs]
      exact k.conditions s

@[simp] theorem trans_path (h : KasparovOperatorHomotopy c T₀ T₁)
    (k : KasparovOperatorHomotopy c T₁ T₂) :
    (h.trans k).path = h.path.trans k.path := rfl

end KasparovOperatorHomotopy
end BC4lean.KKTheory
