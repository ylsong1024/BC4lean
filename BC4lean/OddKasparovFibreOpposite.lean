import BC4lean.OddIntervalKasparovFibre
import BC4lean.OddKasparovCycleIso
import BC4lean.OddKasparovInverseRotation

/-! # Opposite cycles and genuine interval fibres

The evaluated inner product and its null quotient are unchanged when a cycle
is replaced by its opposite. The identity unitary on the completed fibre
intertwines the negated Fredholm operators. Their equalities
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

namespace OddKasparovCycleIso

/-- Taking the fibre of the opposite full interval cycle yields the opposite
fibre cycle, through the genuine identity Hilbert-module unitary. -/
def fibreOpposite (c : OddKasparovCycle α (β.continuousSections (X := X)) M) (t : X) :
    OddKasparovCycleIso (c.opposite.fibre t) (c.fibre t).opposite where
  moduleEquiv := HilbertModuleEquiv.refl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine z := by
    change (c.opposite.fibre t).operator z = (c.fibre t).opposite.operator z
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := M) t).induction_on z ?_ ?_
    · exact isClosed_eq (c.opposite.fibre t).operator.toCLM.continuous
        (c.fibre t).opposite.operator.toCLM.continuous
    · intro x
      rw [OddKasparovCycle.fibre_operator_mk]
      change hilbertModuleFibreMk (B := B) t ((-c.operator) x) =
        (-(c.fibre t).operator) (hilbertModuleFibreMk (B := B) t x)
      simp only [AdjointableMap.coe_neg_apply]
      rw [OddKasparovCycle.fibre_operator_mk, map_neg]

end OddKasparovCycleIso
end BC4lean.KKTheory
