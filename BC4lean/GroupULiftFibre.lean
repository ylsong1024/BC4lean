import BC4lean.GroupULiftRawCycles
import BC4lean.IntervalModuleFibreNorm
import BC4lean.OddIntervalKasparovFibre

/-! # Universe lifting commutes with actual completed fibres

Evaluation is the existing genuine fibre map composed with ULift.down.
Its entire evaluated coefficient form and actual surjectivity identify the
completed radical quotient. Thus lifting an arbitrary interval module gives
the true lifted endpoint modules, with whole-cycle endpoint unitaries.
-/

noncomputable section
universe uB uM uX uΓ uA v
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B : Type uB} {X : Type uX} {M : Type uM}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

def hilbertModuleULiftFibreEvaluation (t : X) :
    ULift.{v} M →L[ℂ] HilbertModuleFibre B M t :=
  (hilbertModuleFibreMk (B := B) t).comp
    (hilbertModuleULiftDown (B := C(X, B)) (E := M)).toAdjointable.toCLM

omit [T2Space X] [CompleteSpace M] in
theorem hilbertModuleULiftFibreEvaluation_inner (t : X) (x y : ULift.{v} M) :
    ⟪hilbertModuleULiftFibreEvaluation (B := B) (M := M) t x,
      hilbertModuleULiftFibreEvaluation (B := B) (M := M) t y⟫_(Bᵐᵒᵖ) =
    MulOpposite.op (MulOpposite.unop ⟪x, y⟫_(C(X, B)ᵐᵒᵖ) t) := by
  change ⟪hilbertModuleFibreMk (B := B) t x.down,
    hilbertModuleFibreMk (B := B) t y.down⟫_(Bᵐᵒᵖ) = _
  rw [hilbertModuleFibre_inner_mk]
  rfl

theorem hilbertModuleULiftFibreEvaluation_surjective (t : X) :
    Function.Surjective (hilbertModuleULiftFibreEvaluation (B := B) (M := M) t :
      ULift.{v} M → HilbertModuleFibre B M t) := by
  intro z
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := M) t z
  exact ⟨ULift.up x, rfl⟩

def hilbertModuleULiftFibreDown (t : X) :
    HilbertModuleEquiv B (HilbertModuleFibre B (ULift.{v} M) t)
      (HilbertModuleFibre B M t) :=
  hilbertModuleFibreEquivOfEvaluation t (hilbertModuleULiftFibreEvaluation t)
    (hilbertModuleULiftFibreEvaluation_inner t) (hilbertModuleULiftFibreEvaluation_surjective t)

@[simp] theorem hilbertModuleULiftFibreDown_mk (t : X) (x : ULift.{v} M) :
    hilbertModuleULiftFibreDown t (hilbertModuleFibreMk (B := B) t x) =
      hilbertModuleFibreMk (B := B) t x.down :=
  hilbertModuleFibreEquivOfEvaluation_mk t _ _ _ x

def hilbertModuleULiftFibreEquiv (t : X) :
    HilbertModuleEquiv B (HilbertModuleFibre B (ULift.{v} M) t)
      (ULift.{v} (HilbertModuleFibre B M t)) :=
  (hilbertModuleULiftFibreDown t).trans (hilbertModuleULiftUp (B := B))

@[simp] theorem hilbertModuleULiftFibreEquiv_mk (t : X) (x : ULift.{v} M) :
    hilbertModuleULiftFibreEquiv t (hilbertModuleFibreMk (B := B) t x) =
      ULift.up (hilbertModuleFibreMk (B := B) t x.down) := by
  rw [hilbertModuleULiftFibreEquiv, HilbertModuleEquiv.trans_apply,
    hilbertModuleULiftFibreDown_mk, hilbertModuleULiftUp_apply]

variable {Γ : Type uΓ} {A : Type uA} [Group Γ] [NonUnitalCStarAlgebra A]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace OddKasparovCycle

def uliftFibreIso (c : OddKasparovCycle α (β.continuousSections (X := X)) M) (t : X) :
    OddKasparovCycleIso
      ((c.ulift : OddKasparovCycle α (β.continuousSections (X := X)) (ULift.{v} M)).fibre t)
      ((c.fibre t).ulift) where
  moduleEquiv := hilbertModuleULiftFibreEquiv t
  action_intertwine g z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := ULift.{v} M) t z
    rw [fibre_action_mk, hilbertModuleULiftFibreEquiv_mk, hilbertModuleULiftFibreEquiv_mk]
    simp only [ulift_action, ULift.down_up, fibre_action_mk]
  representation_intertwine a z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := ULift.{v} M) t z
    rw [fibre_representation_mk, hilbertModuleULiftFibreEquiv_mk,
      hilbertModuleULiftFibreEquiv_mk]
    simp only [ulift_representation, ULift.down_up, fibre_representation_mk]
  operator_intertwine z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := ULift.{v} M) t z
    rw [fibre_operator_mk, hilbertModuleULiftFibreEquiv_mk, hilbertModuleULiftFibreEquiv_mk]
    simp only [ulift_operator, ULift.down_up, fibre_operator_mk]

end OddKasparovCycle
end BC4lean.KKTheory
