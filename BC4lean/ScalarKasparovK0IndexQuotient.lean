import BC4lean.ScalarKasparovOperatorK0IndexFibre
import BC4lean.KasparovHomotopyGroup

/-! # The genuine scalar K₀ index on the full Kasparov quotient

The actual supported homogeneous interval modules and completed endpoint
fibre unitaries give equality of the raw index on every full homotopy witness.
Whole-cycle isomorphism invariance and the genuine equivalence closure then
permit a lift to the project's actual full ordinary scalar KK quotient.
-/

noncomputable section
universe uB uE
namespace BC4lean.KKTheory

variable {B : Type uB} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
local notation "α₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
local notation "β₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B)

/-- Every actual full interval witness preserves the genuine original-cycle index. -/
theorem scalarKasparovOperatorK0Index_full
    {c d : BundledKasparovCycle.{0, 0, uB, uE} α₁ β₁}
    (h : FullKasparovHomotopy c d) : c.cycle.operatorK0Index = d.cycle.operatorK0Index := by
  calc
    _ = (h.intervalCycle.cycle.fibre 0).operatorK0Index :=
      (scalarKasparovOperatorK0Index_iso h.sourceIso).symm
    _ = (h.intervalCycle.cycle.fibre 1).operatorK0Index :=
      scalarKasparovOperatorK0Index_fibre_endpoints h.intervalCycle.cycle
    _ = _ := scalarKasparovOperatorK0Index_iso h.targetIso

/-- Equality holds through the project's actual generated full homotopy relation. -/
theorem scalarKasparovOperatorK0Index_homotopic
    {c d : BundledKasparovCycle.{0, 0, uB, uE} α₁ β₁}
    (h : c.Homotopic d) : c.cycle.operatorK0Index = d.cycle.operatorK0Index := by
  induction h with
  | rel c d h =>
    rcases h with h | h
    · obtain ⟨e⟩ := h
      exact scalarKasparovOperatorK0Index_iso e
    · obtain ⟨h⟩ := h
      exact scalarKasparovOperatorK0Index_full h
  | refl c => rfl
  | symm c d h ih => exact ih.symm
  | trans c d e h h' ih ih' => exact ih.trans ih'

/-- The actual scalar-kernel K₀ index on the full ordinary Kasparov group. -/
def scalarKKOperatorK0Index :
    KasparovHomotopyClass.{0, 0, uB, uE} α₁ β₁ → BC4lean.OperatorKTheory.OperatorK0 B :=
  Quotient.lift (fun c => c.cycle.operatorK0Index) (by
    intro c d h
    exact scalarKasparovOperatorK0Index_homotopic h)

@[simp] theorem scalarKKOperatorK0Index_mk
    (c : BundledKasparovCycle.{0, 0, uB, uE} α₁ β₁) :
    scalarKKOperatorK0Index (KasparovHomotopyClass.mk c) = c.cycle.operatorK0Index := rfl

end BC4lean.KKTheory
