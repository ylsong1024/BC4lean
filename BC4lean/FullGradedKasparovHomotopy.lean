import BC4lean.BundledGradedKasparovCycle
import BC4lean.GradedIntervalKasparovFibre

/-! # Full interval homotopies for genuinely graded cycles

The witness is a genuine graded cycle on an arbitrary complete countably
generated interval-coefficient module. The two completed evaluated fibres
are identified with the endpoint cycles by actual whole-cycle isomorphisms.
Both algebra gradings may be nontrivial. This file does not replace single
interval witnesses by an equivalence closure or claim any gluing theorem.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

/-- An actual arbitrary-module full graded interval homotopy, with genuine
unitary identifications of both evaluated whole-cycle fibres. -/
structure FullGradedKasparovHomotopy
    (c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB) where
  intervalCycle : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α
    (β.continuousSections (X := unitInterval)) δA δB.continuousSections
  sourceIso : GradedKasparovCycleIso
    (intervalCycle.cycle.fibre 0) c.cycle
  targetIso : GradedKasparovCycleIso
    (intervalCycle.cycle.fibre 1) d.cycle

namespace FullGradedKasparovHomotopy

variable {c d e f : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB}

/-- Endpoint changes use the same genuine interval module and compose the
actual whole-cycle isomorphisms. -/
def changeEndpoints (h : FullGradedKasparovHomotopy c d) (u : c.Iso e) (v : d.Iso f) :
    FullGradedKasparovHomotopy e f where
  intervalCycle := h.intervalCycle
  sourceIso := h.sourceIso.trans u
  targetIso := h.targetIso.trans v

end FullGradedKasparovHomotopy
end BC4lean.KKTheory
