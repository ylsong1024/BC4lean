import BC4lean.FullGradedKasparovHomotopyEquivalence
import BC4lean.HilbertModuleFibreSum
import BC4lean.GradedKasparovDirectSum

/-! # Direct sums of single full homotopies with both algebra gradings

The actual completed sum-fibre Hilbert-module unitary intertwines the
semilinear grading, action, source representation and operator. Thus summing
two arbitrary full witnesses gives one actual full witness, including for
nontrivial source and coefficient gradings.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory

section Fibre
variable {Γ A B X M N : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, B)ᵐᵒᵖ M]
  [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]
  [NormedAddCommGroup N] [NormedSpace ℂ N] [SMul C(X, B)ᵐᵒᵖ N]
  [CStarModule C(X, B)ᵐᵒᵖ N] [CompleteSpace N]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

def GradedKasparovCycleIso.fibreDirectSum
    (c : GradedKasparovCycle α (β.continuousSections (X := X)) δA δB.continuousSections M)
    (d : GradedKasparovCycle α (β.continuousSections (X := X)) δA δB.continuousSections N)
    (t : X) : GradedKasparovCycleIso ((c.directSum d).fibre t) ((c.fibre t).directSum (d.fibre t)) where
  moduleEquiv := hilbertModuleFibreSumEquiv t
  grading_intertwine z := by
    refine (hilbertModuleFibreMk_denseRange (B := B)
      (M := HilbertModuleSum C(X, B) M N) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [(c.directSum d).fibre_grading_mk t x,
        hilbertModuleFibreSumEquiv_mk (B := B) (X := X) (M := M) (N := N),
        hilbertModuleFibreSumEquiv_mk (B := B) (X := X) (M := M) (N := N)]
      change sumMk (hilbertModuleFibreMk (B := B) t (c.grading.grading x.fst))
        (hilbertModuleFibreMk (B := B) t (d.grading.grading x.snd)) =
          ((c.fibre t).grading.sum (d.fibre t).grading).grading
            (sumMk (hilbertModuleFibreMk (B := B) t x.fst) (hilbertModuleFibreMk (B := B) t x.snd))
      simp only [GradedHilbertModule.sum_grading_apply, sumMk_fst, sumMk_snd,
        GradedKasparovCycle.fibre_grading_mk]
  action_intertwine g z := by
    refine (hilbertModuleFibreMk_denseRange (B := B)
      (M := HilbertModuleSum C(X, B) M N) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [(c.directSum d).fibre_action_mk t g x,
        hilbertModuleFibreSumEquiv_mk (B := B) (X := X) (M := M) (N := N),
        hilbertModuleFibreSumEquiv_mk (B := B) (X := X) (M := M) (N := N)]
      change sumMk (hilbertModuleFibreMk (B := B) t (c.groupAction.action g x.fst))
        (hilbertModuleFibreMk (B := B) t (d.groupAction.action g x.snd)) =
          ((c.fibre t).groupAction.sum (d.fibre t).groupAction).action g
            (sumMk (hilbertModuleFibreMk (B := B) t x.fst) (hilbertModuleFibreMk (B := B) t x.snd))
      simp only [EquivariantHilbertModule.sum_action_apply, sumMk_fst, sumMk_snd,
        GradedKasparovCycle.fibre_action_mk]
  representation_intertwine a z :=
    hilbertModuleFibreSumEquiv_operator_intertwine t (c.representation a) (d.representation a) z
  operator_intertwine z := hilbertModuleFibreSumEquiv_operator_intertwine t c.operator d.operator z

end Fibre

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

def FullGradedKasparovHomotopy.directSum
    {c d k l : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA δB}
    (h : FullGradedKasparovHomotopy c d) (h' : FullGradedKasparovHomotopy k l) :
    FullGradedKasparovHomotopy (c.directSum k) (d.directSum l) where
  intervalCycle := h.intervalCycle.directSum h'.intervalCycle
  sourceIso := (GradedKasparovCycleIso.fibreDirectSum h.intervalCycle.cycle h'.intervalCycle.cycle 0).trans
    (h.sourceIso.directSum h'.sourceIso)
  targetIso := (GradedKasparovCycleIso.fibreDirectSum h.intervalCycle.cycle h'.intervalCycle.cycle 1).trans
    (h.targetIso.directSum h'.targetIso)

theorem BundledGradedKasparovCycle.fullHomotopic_directSum
    {c d k l : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA δB}
    (h : c.FullHomotopic d) (h' : k.FullHomotopic l) :
    (c.directSum k).FullHomotopic (d.directSum l) := by
  obtain ⟨h⟩ := h
  obtain ⟨h'⟩ := h'
  exact ⟨h.directSum h'⟩

end BC4lean.KKTheory
