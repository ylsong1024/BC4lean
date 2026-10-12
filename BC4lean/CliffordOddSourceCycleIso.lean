import BC4lean.CliffordOddSourceCycle
import BC4lean.OddKasparovCycleIso
import BC4lean.KasparovDirectSumIso
import BC4lean.GradedKasparovCycleIso

/-! # Whole-cycle unitaries for the actual odd source Clifford cycle

The diagonal sum of the original whole module unitary intertwines the
swap grading, both source coordinates and the Pauli σ_y operator.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordOddSourceCycle

variable {Γ B C E F : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Cᵐᵒᵖ E] [CStarModule Cᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]
  {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  {c : OddKasparovCycle β γ E} {d : OddKasparovCycle β γ F}

local instance cliffordOddSourceCycleIsoLocalInstance1 : CompleteSpace (HilbertModuleSum C E E) := hilbertModuleSum_complete
local instance cliffordOddSourceCycleIsoLocalInstance2 : CompleteSpace (HilbertModuleSum C F F) := hilbertModuleSum_complete

/-- The original actual whole-cycle unitary acts on both genuine sum coordinates. -/
def iso (e : OddKasparovCycleIso c d) :
    GradedKasparovCycleIso (cycle c) (cycle d) where
  moduleEquiv := e.moduleEquiv.sum e.moduleEquiv
  grading_intertwine x := by
    change sumMk (e.moduleEquiv x.snd) (e.moduleEquiv x.fst) = _
    rfl
  action_intertwine g x := by
    apply Prod.ext <;> exact e.action_intertwine g _
  representation_intertwine b x := by
    change (e.moduleEquiv.sum e.moduleEquiv)
        (sumMap (c.representation b.1) (c.representation b.2) x) =
      sumMap (d.representation b.1) (d.representation b.2)
        ((e.moduleEquiv.sum e.moduleEquiv) x)
    simp only [HilbertModuleEquiv.sum_apply, sumMap_apply, sumMk_fst, sumMk_snd]
    apply Prod.ext
    · change e.moduleEquiv (c.representation b.1 x.fst) =
        d.representation b.1 (e.moduleEquiv x.fst)
      exact e.representation_intertwine b.1 x.fst
    · change e.moduleEquiv (c.representation b.2 x.snd) =
        d.representation b.2 (e.moduleEquiv x.snd)
      exact e.representation_intertwine b.2 x.snd
  operator_intertwine x := by
    change (e.moduleEquiv.sum e.moduleEquiv) (operator c.operator x) =
      operator d.operator ((e.moduleEquiv.sum e.moduleEquiv) x)
    simp only [operator_apply, HilbertModuleEquiv.sum_apply, sumMk_fst, sumMk_snd,
      map_smul, e.operator_intertwine]

end BC4lean.KKTheory.CliffordOddSourceCycle
