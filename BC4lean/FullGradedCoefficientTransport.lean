import BC4lean.GradedCoefficientFibreTransport
import BC4lean.FullGradedKasparovHomotopy

/-! # Invertible transport of genuine full graded homotopy witnesses

Every arbitrary interval module is transported through the actual pointwise
coefficient equivalence. The proved fibre unitaries and transported endpoint
unitaries supply the endpoint identifications of the whole interval cycle.
-/

noncomputable section
universe uΓ uA uB uC uE
namespace BC4lean.KKTheory

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} [Group Γ]
  [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {η : CStarAlgebraAction Γ C} {δA : CStarGrading A}
  {δB : CStarGrading B} {δC : CStarGrading C}

def FullGradedKasparovHomotopy.changeCoefficients
    {c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB}
    (h : FullGradedKasparovHomotopy c d) (e : GradedCoefficientEquiv β δB η δC) :
    FullGradedKasparovHomotopy (c.changeCoefficients e) (d.changeCoefficients e) where
  intervalCycle := h.intervalCycle.changeCoefficients e.continuousSections
  sourceIso := (h.intervalCycle.cycle.changeCoefficientsFibreIso e 0).trans
    (h.sourceIso.changeCoefficients e)
  targetIso := (h.intervalCycle.cycle.changeCoefficientsFibreIso e 1).trans
    (h.targetIso.changeCoefficients e)

/-- Both directions construct one actual full homotopy witness; the inverse
uses the proved whole-cycle inverse coefficient-change unitaries. -/
theorem fullGradedHomotopy_iff_changeCoefficients
    (c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB)
    (e : GradedCoefficientEquiv β δB η δC) :
    Nonempty (FullGradedKasparovHomotopy c d) ↔
      Nonempty (FullGradedKasparovHomotopy (c.changeCoefficients e) (d.changeCoefficients e)) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.changeCoefficients e⟩
  · rintro ⟨h⟩
    exact ⟨(h.changeCoefficients e.symm).changeEndpoints
      (c.cycle.changeCoefficientsInverseIso e) (d.cycle.changeCoefficientsInverseIso e)⟩

end BC4lean.KKTheory
