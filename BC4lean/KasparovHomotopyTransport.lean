import BC4lean.KasparovCycleTransport
import BC4lean.KasparovOperatorHomotopy

/-! # Unitary transport of norm-continuous operator homotopies

An actual Hilbert-module unitary transports a fixed-module operator path to
the transported cycle's module. Conjugation is isometric in the operator norm,
and every transported operator satisfies oddness and all four compactness
conditions. This gives actual endpoint operators and cycle isomorphisms.
-/

noncomputable section
namespace BC4lean.KKTheory

open unitInterval

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

namespace HilbertModuleEquiv

/-- Unitary conjugation is an isometry for the actual operator norm. -/
theorem transport_isometry (u : HilbertModuleEquiv B E F) : Isometry u.transport := by
  change Isometry u.transportStarAlgEquiv
  exact AddMonoidHomClass.isometry_of_norm u.transportStarAlgEquiv u.transport_norm

/-- In particular, conjugation transports norm-continuous operator paths. -/
theorem transport_continuous (u : HilbertModuleEquiv B E F) : Continuous u.transport :=
  u.transport_isometry.continuous

end HilbertModuleEquiv

variable {Γ A : Type*} [Group Γ] [NonUnitalCStarAlgebra A] [StarOrderedRing B]
  [CompleteSpace E] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace KasparovCycle

/-- All fixed-frame operator conditions persist under genuine unitary transport. -/
theorem transport_operatorConditions (c : KasparovCycle α β E)
    (u : HilbertModuleEquiv B E F) {T : AdjointableMap B E E}
    (hT : c.OperatorConditions T) :
    (c.transport u).OperatorConditions (u.transport T) where
  operator_odd := u.transport_isOdd c.grading hT.operator_odd
  selfadjoint_mod_compact a := by
    have h := (u.transport_isModuleCompact_iff _).2 (hT.selfadjoint_mod_compact a)
    simpa only [transport_representation, HilbertModuleEquiv.transport_mul,
      HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_star] using h
  square_mod_compact a := by
    have h := (u.transport_isModuleCompact_iff _).2 (hT.square_mod_compact a)
    simpa only [transport_representation, HilbertModuleEquiv.transport_mul,
      HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_one] using h
  commutator_compact a := by
    have h := (u.transport_isModuleCompact_iff _).2 (hT.commutator_compact a)
    simpa only [transport_representation, HilbertModuleEquiv.transport_mul,
      HilbertModuleEquiv.transport_sub] using h
  equivariance_mod_compact g a := by
    change IsModuleCompact (((u.transportAction c.groupAction).conjugateOperator g
      (u.transport T) - u.transport T) * u.transport (c.representation a))
    rw [u.transportAction_conjugateOperator]
    have h := (u.transport_isModuleCompact_iff _).2 (hT.equivariance_mod_compact g a)
    simpa only [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_sub] using h

/-- Replacing the admissible operator commutes with transporting the full cycle. -/
theorem transport_withOperator (c : KasparovCycle α β E)
    (u : HilbertModuleEquiv B E F) (T : AdjointableMap B E E)
    (hT : c.OperatorConditions T) :
    (c.withOperator T hT).transport u =
      (c.transport u).withOperator (u.transport T) (c.transport_operatorConditions u hT) := rfl

end KasparovCycle

namespace KasparovOperatorHomotopy

variable {c : KasparovCycle α β E} {T₀ T₁ T₂ : AdjointableMap B E E}

/-- Transport a norm-continuous operator homotopy by an actual module unitary. -/
def transport (h : KasparovOperatorHomotopy c T₀ T₁) (u : HilbertModuleEquiv B E F) :
    KasparovOperatorHomotopy (c.transport u) (u.transport T₀) (u.transport T₁) where
  path := h.path.map u.transport_continuous
  conditions t := c.transport_operatorConditions u (h.conditions t)

@[simp] theorem transport_path_apply (h : KasparovOperatorHomotopy c T₀ T₁)
    (u : HilbertModuleEquiv B E F) (t : I) :
    (h.transport u).path t = u.transport (h.path t) := rfl

/-- Every cycle along the new path is exactly the transported original cycle. -/
@[simp] theorem transport_cycleAt (h : KasparovOperatorHomotopy c T₀ T₁)
    (u : HilbertModuleEquiv B E F) (t : I) :
    (h.transport u).cycleAt t = (h.cycleAt t).transport u := by
  exact (c.transport_withOperator u (h.path t) (h.conditions t)).symm

/-- The parameterwise cycles have genuine varying-module isomorphisms. -/
def cycleAtIso (h : KasparovOperatorHomotopy c T₀ T₁)
    (u : HilbertModuleEquiv B E F) (t : I) :
    KasparovCycleIso (h.cycleAt t) ((h.transport u).cycleAt t) := by
  rw [transport_cycleAt]
  exact (h.cycleAt t).transportIso u

@[simp] theorem transport_source_operator (h : KasparovOperatorHomotopy c T₀ T₁)
    (u : HilbertModuleEquiv B E F) :
    ((h.transport u).cycleAt 0).operator = u.transport T₀ :=
  (h.transport u).source_operator

@[simp] theorem transport_target_operator (h : KasparovOperatorHomotopy c T₀ T₁)
    (u : HilbertModuleEquiv B E F) :
    ((h.transport u).cycleAt 1).operator = u.transport T₁ :=
  (h.transport u).target_operator

/-- Transport commutes with reversing the actual operator path. -/
@[simp] theorem transport_symm (h : KasparovOperatorHomotopy c T₀ T₁)
    (u : HilbertModuleEquiv B E F) :
    h.symm.transport u = (h.transport u).symm := by
  apply ext
  exact (Path.map_symm h.path u.transport_continuous).symm

/-- Transport commutes with concatenation of paths with the same fixed frame. -/
@[simp] theorem transport_trans (h : KasparovOperatorHomotopy c T₀ T₁)
    (k : KasparovOperatorHomotopy c T₁ T₂) (u : HilbertModuleEquiv B E F) :
    (h.trans k).transport u = (h.transport u).trans (k.transport u) := by
  apply ext
  exact Path.map_trans h.path k.path u.transport_continuous

end KasparovOperatorHomotopy
end BC4lean.KKTheory
