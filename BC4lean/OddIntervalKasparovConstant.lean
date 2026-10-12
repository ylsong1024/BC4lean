import BC4lean.FullCliffordParityHomotopy

/-! # Constant odd interval cycles give actual reflexive full witnesses -/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ A B E X : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace OddKasparovCycle

/-- The actual continuous-section interval cycle with constant odd operators. -/
def intervalConstant (c : OddKasparovCycle α β E) :
    OddKasparovCycle α (β.continuousSections (X := X)) C(X, E) where
  countablyGenerated := continuousSection_isCountablyGenerated c.countablyGenerated
  groupAction := c.groupAction.continuousSections
  representation := continuousSectionConstantOperatorHom.comp c.representation
  representation_equivariant g a := by
    ext x t
    exact congrArg (fun T : AdjointableMap B E E => T (x t)) (c.representation_equivariant g a)
  operator := continuousSectionConstantOperator c.operator
  selfadjoint_mod_compact a := by
    have h := continuousSectionOperator_isModuleCompact
      (ContinuousMap.const X ((c.operator - star c.operator) * c.representation a))
      (fun _ => c.selfadjoint_mod_compact a)
    convert h using 1
    ext x t
    rfl
  square_mod_compact a := by
    have h := continuousSectionOperator_isModuleCompact
      (ContinuousMap.const X ((c.operator * c.operator - 1) * c.representation a))
      (fun _ => by
        simpa only [ContinuousMap.const_apply] using c.square_mod_compact a)
    convert h using 1
    ext x t
    rfl
  commutator_compact a := by
    have h := continuousSectionOperator_isModuleCompact
      (ContinuousMap.const X (c.operator * c.representation a - c.representation a * c.operator))
      (fun _ => c.commutator_compact a)
    convert h using 1
    ext x t
    rfl
  equivariance_mod_compact g a := by
    have h := continuousSectionOperator_isModuleCompact
      (ContinuousMap.const X ((c.groupAction.conjugateOperator g c.operator - c.operator) *
        c.representation a)) (fun _ => c.equivariance_mod_compact g a)
    convert h using 1
    ext x t
    rfl

/-- Every genuine fibre of the constant section cycle is the original entire odd cycle. -/
def intervalConstantFibreIso (c : OddKasparovCycle α β E) (t : X) :
    OddKasparovCycleIso ((c.intervalConstant (X := X)).fibre t) c where
  moduleEquiv := continuousSectionHilbertModuleFibreEquiv t
  action_intertwine g z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := C(X, E)) t z
    rw [OddKasparovCycle.fibre_action_mk, continuousSectionHilbertModuleFibreEquiv_mk,
      continuousSectionHilbertModuleFibreEquiv_mk]
    rfl
  representation_intertwine a z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := C(X, E)) t z
    rw [OddKasparovCycle.fibre_representation_mk, continuousSectionHilbertModuleFibreEquiv_mk,
      continuousSectionHilbertModuleFibreEquiv_mk]
    rfl
  operator_intertwine z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := C(X, E)) t z
    rw [OddKasparovCycle.fibre_operator_mk, continuousSectionHilbertModuleFibreEquiv_mk,
      continuousSectionHilbertModuleFibreEquiv_mk]
    rfl

end OddKasparovCycle

namespace FullOddKasparovHomotopy

/-- Reflexivity is witnessed by the genuine continuous-section interval cycle. -/
def refl (c : BundledOddKasparovCycle α β) : FullOddKasparovHomotopy c c where
  intervalCycle := BundledOddKasparovCycle.of (c.cycle.intervalConstant (X := unitInterval))
  sourceIso := c.cycle.intervalConstantFibreIso (0 : unitInterval)
  targetIso := c.cycle.intervalConstantFibreIso (1 : unitInterval)

/-- Every entire-cycle odd isomorphism is itself an actual full interval witness. -/
def ofIso {c d : BundledOddKasparovCycle α β} (u : c.Iso d) : FullOddKasparovHomotopy c d :=
  (refl c).changeEndpoints (BundledOddKasparovCycle.isoRefl c) u

end FullOddKasparovHomotopy
end BC4lean.KKTheory
