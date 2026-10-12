import BC4lean.GroupShrinkRawCycles
import BC4lean.IntervalModuleFibreNorm
import BC4lean.OddIntervalKasparovFibre
import BC4lean.OddKasparovHomotopyGroup

/-! # Actual shrinking of arbitrary odd full homotopies

Countable generation over separable coefficients supplies a small model
for every cycle and every actual interval module. Evaluation from the
shrunk interval module has the full evaluated inner product and is onto
the original completed fibre. The resulting whole-cycle endpoint
unitaries therefore give genuine full witnesses between the shrunk cycles.
-/

noncomputable section
universe uΓ uA uB uE v uM uX
namespace BC4lean.KKTheory
open scoped InnerProductSpace

section Fibre
variable {B : Type uB} {X : Type uX} {M : Type uM}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]
  [Small.{v} M]

def hilbertModuleShrinkFibreEvaluation (t : X) :
    Shrink.{v} M →L[ℂ] HilbertModuleFibre B M t :=
  (hilbertModuleFibreMk (B := B) t).comp
    (hilbertModuleShrinkDown (B := C(X, B)) (E := M)).toAdjointable.toCLM

theorem hilbertModuleShrinkFibreEvaluation_inner (t : X) (x y : Shrink.{v} M) :
    ⟪hilbertModuleShrinkFibreEvaluation (B := B) (M := M) t x,
      hilbertModuleShrinkFibreEvaluation (B := B) (M := M) t y⟫_(Bᵐᵒᵖ) =
    MulOpposite.op (MulOpposite.unop ⟪x, y⟫_(C(X, B)ᵐᵒᵖ) t) := by
  let _retainedOriginalT2 : T2Space X := inferInstance
  let _retainedOriginalCompleteM : CompleteSpace M := inferInstance
  change ⟪hilbertModuleFibreMk (B := B) t ((equivShrink M).symm x),
    hilbertModuleFibreMk (B := B) t ((equivShrink M).symm y)⟫_(Bᵐᵒᵖ) = _
  rw [hilbertModuleFibre_inner_mk]
  rfl

theorem hilbertModuleShrinkFibreEvaluation_surjective (t : X) :
    Function.Surjective (hilbertModuleShrinkFibreEvaluation (B := B) (M := M) t :
      Shrink.{v} M → HilbertModuleFibre B M t) := by
  intro z
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := M) t z
  refine ⟨equivShrink M x, ?_⟩
  change hilbertModuleFibreMk (B := B) t ((equivShrink M).symm (equivShrink M x)) = _
  rw [Equiv.symm_apply_apply]

def hilbertModuleShrinkFibreDown (t : X) :
    HilbertModuleEquiv B (HilbertModuleFibre B (Shrink.{v} M) t)
      (HilbertModuleFibre B M t) :=
  hilbertModuleFibreEquivOfEvaluation t (hilbertModuleShrinkFibreEvaluation t)
    (hilbertModuleShrinkFibreEvaluation_inner t) (hilbertModuleShrinkFibreEvaluation_surjective t)

@[simp] theorem hilbertModuleShrinkFibreDown_mk (t : X) (x : Shrink.{v} M) :
    hilbertModuleShrinkFibreDown t (hilbertModuleFibreMk (B := B) t x) =
      hilbertModuleFibreMk (B := B) t ((equivShrink M).symm x) :=
  hilbertModuleFibreEquivOfEvaluation_mk t _ _ _ x

variable {Γ : Type uΓ} {A : Type uA} [Group Γ] [NonUnitalCStarAlgebra A]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

def OddKasparovCycle.shrinkFibreIso
    (c : OddKasparovCycle α (β.continuousSections (X := X)) M) (t : X) :
    OddKasparovCycleIso
      ((c.shrink : OddKasparovCycle α (β.continuousSections (X := X)) (Shrink.{v} M)).fibre t)
      (c.fibre t) where
  moduleEquiv := hilbertModuleShrinkFibreDown t
  action_intertwine g z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := Shrink.{v} M) t z
    rw [fibre_action_mk, hilbertModuleShrinkFibreDown_mk, hilbertModuleShrinkFibreDown_mk]
    simp only [OddKasparovCycle.shrink_action, Equiv.symm_apply_apply, fibre_action_mk]
  representation_intertwine a z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := Shrink.{v} M) t z
    rw [fibre_representation_mk, hilbertModuleShrinkFibreDown_mk,
      hilbertModuleShrinkFibreDown_mk]
    simp only [OddKasparovCycle.shrink_representation, Equiv.symm_apply_apply,
      fibre_representation_mk]
  operator_intertwine z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := Shrink.{v} M) t z
    rw [fibre_operator_mk, hilbertModuleShrinkFibreDown_mk, hilbertModuleShrinkFibreDown_mk]
    simp only [OddKasparovCycle.shrink_operator, Equiv.symm_apply_apply, fibre_operator_mk]

end Fibre

section Bundled
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

def BundledOddKasparovCycle.shrink
    (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    BundledOddKasparovCycle.{uΓ, uA, uB, v} α β := by
  letI : Small.{v} c.carrier := c.cycle.countablyGenerated.small
  exact BundledOddKasparovCycle.of
    (c.cycle.shrink : OddKasparovCycle α β (Shrink.{v} c.carrier))

def BundledOddKasparovCycle.shrinkIso
    (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    OddKasparovCycleIso c.cycle
      (c.shrink : BundledOddKasparovCycle.{uΓ, uA, uB, v} α β).cycle := by
  letI : Small.{v} c.carrier := c.cycle.countablyGenerated.small
  exact c.cycle.shrinkIso

def FullOddKasparovHomotopy.shrink
    {c d : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β}
    (h : FullOddKasparovHomotopy c d) : FullOddKasparovHomotopy
      (c.shrink : BundledOddKasparovCycle.{uΓ, uA, uB, v} α β) d.shrink := by
  letI : Small.{v} h.intervalCycle.carrier := h.intervalCycle.cycle.countablyGenerated.small
  exact
    { intervalCycle := h.intervalCycle.shrink
      sourceIso := (h.intervalCycle.cycle.shrinkFibreIso 0).trans
        (h.sourceIso.trans c.shrinkIso)
      targetIso := (h.intervalCycle.cycle.shrinkFibreIso 1).trans
        (h.targetIso.trans d.shrinkIso) }

namespace OddKK

def shrink : OddKK.{uΓ, uA, uB, uE} α β → OddKK.{uΓ, uA, uB, v} α β :=
  Quotient.lift (fun c => OddKK.mk
    (c.shrink : BundledOddKasparovCycle.{uΓ, uA, uB, v} α β)) (by
      intro c d h
      obtain ⟨h⟩ := h
      exact Quotient.sound ⟨h.shrink⟩)

@[simp] theorem shrink_mk (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    shrink (OddKK.mk c) = OddKK.mk
      (c.shrink : BundledOddKasparovCycle.{uΓ, uA, uB, v} α β) := rfl

end OddKK
end Bundled
end BC4lean.KKTheory
