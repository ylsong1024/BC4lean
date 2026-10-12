import BC4lean.OddKasparovInverseRotation
import BC4lean.FullCliffordParityHomotopy

/-! # Odd operator paths as actual interval cycles

Uniform compact-field approximation proves actual module compactness of all
four defects on the section module. The genuine completed evaluated fibres
are identified with the raw odd path cycles by whole-cycle unitaries.
-/

noncomputable section
namespace BC4lean.KKTheory
open unitInterval
variable {Γ A B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace OddKasparovOperatorHomotopy

variable {c : OddKasparovCycle α β E} {T₀ T₁ : AdjointableMap B E E}

/-- A fixed-module operator homotopy gives a genuine interval-coefficient
Kasparov cycle, with actual compact module defects on `C(I,E)`. -/
def intervalCycle (h : OddKasparovOperatorHomotopy c T₀ T₁) :
    OddKasparovCycle α (β.continuousSections (X := I)) C(I, E) where
  countablyGenerated := continuousSection_isCountablyGenerated c.countablyGenerated
  groupAction := c.groupAction.continuousSections
  representation := continuousSectionConstantOperatorHom.comp c.representation
  representation_equivariant := by
    intro g a
    ext x t
    exact congrArg (fun T : AdjointableMap B E E => T (x t))
      (c.representation_equivariant g a)
  operator := continuousSectionOperator ⟨h.path, h.path.continuous⟩
  selfadjoint_mod_compact := by
    intro a
    let D : C(I, AdjointableMap B E E) :=
      ⟨fun t => (h.path t - star (h.path t)) * c.representation a,
        (h.path.continuous.sub h.path.continuous.star).mul continuous_const⟩
    have hD := continuousSectionOperator_isModuleCompact D
      (fun t => (h.conditions t).selfadjoint_mod_compact a)
    convert hD using 1
    ext x t
    rfl
  square_mod_compact := by
    intro a
    let D : C(I, AdjointableMap B E E) :=
      ⟨fun t => (h.path t * h.path t - 1) * c.representation a,
        ((h.path.continuous.mul h.path.continuous).sub continuous_const).mul continuous_const⟩
    have hD := continuousSectionOperator_isModuleCompact D
      (fun t => (h.conditions t).square_mod_compact a)
    convert hD using 1
    ext x t
    rfl
  commutator_compact := by
    intro a
    let D : C(I, AdjointableMap B E E) :=
      ⟨fun t => h.path t * c.representation a - c.representation a * h.path t,
        (h.path.continuous.mul continuous_const).sub (continuous_const.mul h.path.continuous)⟩
    have hD := continuousSectionOperator_isModuleCompact D
      (fun t => (h.conditions t).commutator_compact a)
    convert hD using 1
    ext x t
    rfl
  equivariance_mod_compact := by
    intro g a
    let D : C(I, AdjointableMap B E E) :=
      ⟨fun t => (c.groupAction.conjugateOperator g (h.path t) - h.path t) * c.representation a,
        (((c.groupAction.conjugateMapContinuousLinearMap c.groupAction g).continuous.comp
          h.path.continuous).sub h.path.continuous).mul continuous_const⟩
    have hD := continuousSectionOperator_isModuleCompact D
      (fun t => (h.conditions t).equivariance_mod_compact g a)
    convert hD using 1
    ext x t
    rfl

/-- The general fibre construction applied to the actual interval cycle of
an operator path is isomorphic to the path cycle at every parameter. -/
def intervalFibreIso (h : OddKasparovOperatorHomotopy c T₀ T₁) (t : I) :
    OddKasparovCycleIso (h.intervalCycle.fibre t) (h.cycleAt t) where
  moduleEquiv := continuousSectionHilbertModuleFibreEquiv (B := B) t
  action_intertwine g z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := C(I, E)) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [OddKasparovCycle.fibre_action_mk,
        continuousSectionHilbertModuleFibreEquiv_mk,
        continuousSectionHilbertModuleFibreEquiv_mk]
      rfl
  representation_intertwine a z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := C(I, E)) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [OddKasparovCycle.fibre_representation_mk,
        continuousSectionHilbertModuleFibreEquiv_mk,
        continuousSectionHilbertModuleFibreEquiv_mk]
      rfl
  operator_intertwine z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := C(I, E)) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [OddKasparovCycle.fibre_operator_mk,
        continuousSectionHilbertModuleFibreEquiv_mk,
        continuousSectionHilbertModuleFibreEquiv_mk]
      rfl

/-- The source endpoint is identified by a genuine whole-cycle isomorphism. -/
def intervalFibreZeroIso (h : OddKasparovOperatorHomotopy c T₀ T₁) :
    OddKasparovCycleIso (h.intervalCycle.fibre 0) (c.withOperator T₀ h.source_conditions) := by
  simpa only [source_cycleAt] using h.intervalFibreIso 0

/-- The target endpoint is identified by a genuine whole-cycle isomorphism. -/
def intervalFibreOneIso (h : OddKasparovOperatorHomotopy c T₀ T₁) :
    OddKasparovCycleIso (h.intervalCycle.fibre 1) (c.withOperator T₁ h.target_conditions) := by
  simpa only [target_cycleAt] using h.intervalFibreIso 1

end OddKasparovOperatorHomotopy
end BC4lean.KKTheory
