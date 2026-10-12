import BC4lean.IntervalKasparovFibre
import BC4lean.KasparovInverseRotation

/-! # Opposite cycles and genuine interval fibres

The evaluated inner product and its null quotient are unchanged when a cycle
is replaced by its opposite. The identity unitary on the completed fibre
intertwines the reversed gradings and Fredholm operators. Their equalities
are proved on the actual dense image of the interval module and extended by
continuity.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ A B X M : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace KasparovCycleIso

/-- Taking the fibre of the opposite full interval cycle yields the opposite
fibre cycle, through the genuine identity Hilbert-module unitary. -/
def fibreOpposite (c : KasparovCycle α (β.continuousSections (X := X)) M) (t : X) :
    KasparovCycleIso (c.opposite.fibre t) (c.fibre t).opposite where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine z := by
    change (c.opposite.fibre t).grading.grading z = (c.fibre t).opposite.grading.grading z
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := M) t).induction_on z ?_ ?_
    · exact isClosed_eq (c.opposite.fibre t).grading.grading.continuous
        (c.fibre t).opposite.grading.grading.continuous
    · intro x
      change (c.opposite.grading.fibre t).grading (hilbertModuleFibreMk (B := B) t x) =
        -(c.grading.fibre t).grading (hilbertModuleFibreMk (B := B) t x)
      rw [GradedHilbertModule.fibre_grading_mk,
        KasparovCycle.opposite_grading, GradedHilbertModule.opposite_grading_apply,
        GradedHilbertModule.fibre_grading_mk,
        map_neg]
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine z := by
    change (c.opposite.fibre t).operator z = (c.fibre t).opposite.operator z
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := M) t).induction_on z ?_ ?_
    · exact isClosed_eq (c.opposite.fibre t).operator.toCLM.continuous
        (c.fibre t).opposite.operator.toCLM.continuous
    · intro x
      rw [KasparovCycle.fibre_operator_mk]
      simp only [KasparovCycle.opposite_operator, AdjointableMap.coe_neg_apply]
      rw [KasparovCycle.fibre_operator_mk, map_neg]

end KasparovCycleIso
end BC4lean.KKTheory
