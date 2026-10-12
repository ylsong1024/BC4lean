import BC4lean.KasparovCycle
import Mathlib.Topology.Path

/-! # Actual operator paths on a fixed odd cycle

All four localized compact defects are retained; odd cycles do not require
a module grading. These operator paths will be realized as actual interval
cycles and used for the inverse rotation.
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

namespace OddKasparovCycle

/-- The exact raw-cycle requirements for an operator on the fixed,
represented equivariant module underlying `c`. -/
structure OperatorConditions (c : OddKasparovCycle α β E)
    (T : AdjointableMap B E E) : Prop where
  selfadjoint_mod_compact : ∀ a,
    IsModuleCompact ((T - star T) * c.representation a)
  square_mod_compact : ∀ a,
    IsModuleCompact ((T * T - 1) * c.representation a)
  commutator_compact : ∀ a,
    IsModuleCompact (T * c.representation a - c.representation a * T)
  equivariance_mod_compact : ∀ g a,
    IsModuleCompact ((c.groupAction.conjugateOperator g T - T) * c.representation a)

/-- The operator of a raw cycle satisfies its fixed-module operator conditions. -/
theorem operatorConditions (c : OddKasparovCycle α β E) :
    c.OperatorConditions c.operator where
  selfadjoint_mod_compact := c.selfadjoint_mod_compact
  square_mod_compact := c.square_mod_compact
  commutator_compact := c.commutator_compact
  equivariance_mod_compact := c.equivariance_mod_compact

/-- Replace the Fredholm operator while retaining the complete fixed module data. -/
def withOperator (c : OddKasparovCycle α β E) (T : AdjointableMap B E E)
    (hT : c.OperatorConditions T) : OddKasparovCycle α β E :=
  { c with
    operator := T
    selfadjoint_mod_compact := hT.selfadjoint_mod_compact
    square_mod_compact := hT.square_mod_compact
    commutator_compact := hT.commutator_compact
    equivariance_mod_compact := hT.equivariance_mod_compact }

@[simp] theorem withOperator_operator (c : OddKasparovCycle α β E)
    (T : AdjointableMap B E E) (hT : c.OperatorConditions T) :
    (c.withOperator T hT).operator = T := rfl

@[simp] theorem withOperator_representation (c : OddKasparovCycle α β E)
    (T : AdjointableMap B E E) (hT : c.OperatorConditions T) :
    (c.withOperator T hT).representation = c.representation := rfl

@[simp] theorem withOperator_groupAction (c : OddKasparovCycle α β E)
    (T : AdjointableMap B E E) (hT : c.OperatorConditions T) :
    (c.withOperator T hT).groupAction = c.groupAction := rfl

@[simp] theorem withOperator_self (c : OddKasparovCycle α β E) :
    c.withOperator c.operator c.operatorConditions = c := by
  cases c
  rfl

end OddKasparovCycle

/-- An operator-norm-continuous path satisfying the raw Kasparov conditions on
one fixed graded, represented equivariant Hilbert module. The two endpoint
operators need not be the operator originally stored in `c`. -/
structure OddKasparovOperatorHomotopy (c : OddKasparovCycle α β E)
    (T₀ T₁ : AdjointableMap B E E) where
  path : Path T₀ T₁
  conditions : ∀ t : I, c.OperatorConditions (path t)

namespace OddKasparovOperatorHomotopy

variable {c : OddKasparovCycle α β E} {T₀ T₁ T₂ : AdjointableMap B E E}

/-- Equality of paths determines equality of fixed-module operator homotopies. -/
@[ext] theorem ext {h k : OddKasparovOperatorHomotopy c T₀ T₁}
    (hp : h.path = k.path) : h = k := by
  cases h
  cases k
  cases hp
  rfl

/-- Every parameter determines an actual raw Kasparov cycle. -/
def cycleAt (h : OddKasparovOperatorHomotopy c T₀ T₁) (t : I) : OddKasparovCycle α β E :=
  c.withOperator (h.path t) (h.conditions t)

@[simp] theorem cycleAt_operator (h : OddKasparovOperatorHomotopy c T₀ T₁) (t : I) :
    (h.cycleAt t).operator = h.path t := rfl

@[simp] theorem cycleAt_representation (h : OddKasparovOperatorHomotopy c T₀ T₁) (t : I) :
    (h.cycleAt t).representation = c.representation := rfl

@[simp] theorem cycleAt_groupAction (h : OddKasparovOperatorHomotopy c T₀ T₁) (t : I) :
    (h.cycleAt t).groupAction = c.groupAction := rfl

/-- Continuity here is the operator-norm topology on adjointable maps. -/
theorem continuous_operator (h : OddKasparovOperatorHomotopy c T₀ T₁) :
    Continuous (fun t : I => (h.cycleAt t).operator) := h.path.continuous

/-- The same path is norm-continuous as a path of bounded complex-linear maps. -/
theorem continuous_toCLM (h : OddKasparovOperatorHomotopy c T₀ T₁) :
    Continuous (fun t : I => (h.path t).toCLM) :=
  AdjointableMap.toCLM_isometry.continuous.comp h.path.continuous

@[simp] theorem source_operator (h : OddKasparovOperatorHomotopy c T₀ T₁) :
    (h.cycleAt 0).operator = T₀ := h.path.source

@[simp] theorem target_operator (h : OddKasparovOperatorHomotopy c T₀ T₁) :
    (h.cycleAt 1).operator = T₁ := h.path.target

/-- The initial operator satisfies the raw-cycle conditions on the fixed module. -/
theorem source_conditions (h : OddKasparovOperatorHomotopy c T₀ T₁) :
    c.OperatorConditions T₀ := by
  simpa only [Path.source] using h.conditions 0

/-- The terminal operator satisfies the raw-cycle conditions on the fixed module. -/
theorem target_conditions (h : OddKasparovOperatorHomotopy c T₀ T₁) :
    c.OperatorConditions T₁ := by
  simpa only [Path.target] using h.conditions 1

/-- The initial cycle is reconstructed with the initial operator and fixed data. -/
@[simp] theorem source_cycleAt (h : OddKasparovOperatorHomotopy c T₀ T₁) :
    h.cycleAt 0 = c.withOperator T₀ h.source_conditions := by
  simp only [cycleAt, Path.source]

/-- The terminal cycle is reconstructed with the terminal operator and fixed data. -/
@[simp] theorem target_cycleAt (h : OddKasparovOperatorHomotopy c T₀ T₁) :
    h.cycleAt 1 = c.withOperator T₁ h.target_conditions := by
  simp only [cycleAt, Path.target]


end OddKasparovOperatorHomotopy
end BC4lean.KKTheory
