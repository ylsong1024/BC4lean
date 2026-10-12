import BC4lean.IntervalKasparovFibre
import BC4lean.HilbertModuleFibreSum
import BC4lean.KasparovDirectSum

/-! # Whole-cycle fibre isomorphisms for direct sums

The genuine sum-fibre unitary intertwines grading, coefficient-twisted group
action, representation and Fredholm operator. This applies to arbitrary
interval modules and supplies the direct-sum compatibility of actual full
Kasparov homotopies.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ A B X M N : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, B)ᵐᵒᵖ M]
  [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]
  [NormedAddCommGroup N] [NormedSpace ℂ N] [SMul C(X, B)ᵐᵒᵖ N]
  [CStarModule C(X, B)ᵐᵒᵖ N] [CompleteSpace N]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace KasparovCycleIso

/-- The actual fibre of a genuine direct-sum cycle is isomorphic to the
genuine direct sum of the actual fibre cycles. -/
def fibreDirectSum (c : KasparovCycle α (β.continuousSections (X := X)) M)
    (d : KasparovCycle α (β.continuousSections (X := X)) N) (t : X) :
    KasparovCycleIso ((c.directSum d).fibre t) ((c.fibre t).directSum (d.fibre t)) where
  moduleEquiv := hilbertModuleFibreSumEquiv t
  grading_intertwine z := by
    refine (hilbertModuleFibreMk_denseRange (B := B)
      (M := HilbertModuleSum C(X, B) M N) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [KasparovCycle.fibre_grading_mk, hilbertModuleFibreSumEquiv_mk,
        hilbertModuleFibreSumEquiv_mk]
      change sumMk (hilbertModuleFibreMk (B := B) t (c.grading.grading x.fst))
        (hilbertModuleFibreMk (B := B) t (d.grading.grading x.snd)) =
          ((c.fibre t).grading.sum (d.fibre t).grading).grading
            (sumMk (hilbertModuleFibreMk (B := B) t x.fst)
              (hilbertModuleFibreMk (B := B) t x.snd))
      simp only [GradedHilbertModule.sum_grading_apply, sumMk_fst, sumMk_snd,
        KasparovCycle.fibre_grading_mk]
  action_intertwine g z := by
    refine (hilbertModuleFibreMk_denseRange (B := B)
      (M := HilbertModuleSum C(X, B) M N) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [KasparovCycle.fibre_action_mk, hilbertModuleFibreSumEquiv_mk,
        hilbertModuleFibreSumEquiv_mk]
      change sumMk (hilbertModuleFibreMk (B := B) t (c.groupAction.action g x.fst))
        (hilbertModuleFibreMk (B := B) t (d.groupAction.action g x.snd)) =
          ((c.fibre t).groupAction.sum (d.fibre t).groupAction).action g
            (sumMk (hilbertModuleFibreMk (B := B) t x.fst)
              (hilbertModuleFibreMk (B := B) t x.snd))
      simp only [EquivariantHilbertModule.sum_action_apply, sumMk_fst, sumMk_snd,
        KasparovCycle.fibre_action_mk]
  representation_intertwine a z := by
    exact hilbertModuleFibreSumEquiv_operator_intertwine t (c.representation a)
      (d.representation a) z
  operator_intertwine z :=
    hilbertModuleFibreSumEquiv_operator_intertwine t c.operator d.operator z

end KasparovCycleIso
end BC4lean.KKTheory
