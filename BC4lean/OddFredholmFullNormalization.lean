import BC4lean.OddFredholmNormalization
import BC4lean.OddKasparovHomotopyGroup

/-! # Actual full witnesses for odd operator paths and normalization

The operator path is realized on the genuine continuous-section Hilbert
module. Its completed evaluated fibres carry the existing whole-cycle
unitaries; this supplies a full witness and equality in the actual quotient.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {E : Type uE} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace FullOddKasparovHomotopy

/-- An actual odd operator homotopy gives a full arbitrary-interval-module
witness through its section module and genuine fibre identifications. -/
def ofOperatorHomotopy {c : OddKasparovCycle α β E} {T₀ T₁ : AdjointableMap B E E}
    (h : OddKasparovOperatorHomotopy c T₀ T₁) :
    FullOddKasparovHomotopy
      (BundledOddKasparovCycle.of (c.withOperator T₀ h.source_conditions))
      (BundledOddKasparovCycle.of (c.withOperator T₁ h.target_conditions)) where
  intervalCycle := BundledOddKasparovCycle.of h.intervalCycle
  sourceIso := by
    change OddKasparovCycleIso (h.intervalCycle.fibre 0)
      (c.withOperator T₀ h.source_conditions)
    exact h.intervalFibreZeroIso
  targetIso := by
    change OddKasparovCycleIso (h.intervalCycle.fibre 1)
      (c.withOperator T₁ h.target_conditions)
    exact h.intervalFibreOneIso

end FullOddKasparovHomotopy

variable [TopologicalSpace.SeparableSpace B]

namespace OddKK

theorem mk_eq_of_full {c d : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β}
    (h : FullOddKasparovHomotopy c d) : mk c = mk d := Quotient.sound ⟨h⟩

end OddKK

namespace OddKasparovCycle

/-- The explicit selfadjoint contractive normalization preserves the actual
full-homotopy quotient class of every odd cycle. -/
theorem normalized_class (c : OddKasparovCycle α β E) :
    OddKK.mk (BundledOddKasparovCycle.of c) =
      OddKK.mk (BundledOddKasparovCycle.of c.normalized) := by
  simpa only [withOperator_self, normalized, withOperator_operator] using
    OddKK.mk_eq_of_full (FullOddKasparovHomotopy.ofOperatorHomotopy c.normalizationHomotopy)

end OddKasparovCycle
end BC4lean.KKTheory
