import BC4lean.GradedIntervalKasparovCycleGluing
import BC4lean.GradedIntervalKasparovReversal
import BC4lean.GradedIntervalKasparovNormalization

/-! # Equivalence of single full graded interval witnesses

Reflexivity uses a genuine constant section cycle. Symmetry uses the actual
reversed arbitrary module. Transitivity uses the closed endpoint-matched
Hilbert module and the actual compact pullback theorem. Consequently the
quotient below uses the existence of one full witness directly, with both
coefficient and source gradings retained.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

namespace FullGradedKasparovHomotopy

/-- A constant operator path gives one full constant-section witness. -/
def refl (c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB) :
    FullGradedKasparovHomotopy c c := by
  let h : GradedKasparovOperatorHomotopy c.cycle c.cycle.operator c.cycle.operator := {
    path := Path.refl c.cycle.operator
    conditions := fun _ => c.cycle.operatorConditions }
  simpa only [GradedKasparovCycle.withOperator_self,
    BundledGradedKasparovCycle.of_storedCycle] using h.fullHomotopy

/-- Actual cycle isomorphisms give a single full witness on constant sections. -/
def ofIso {c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB}
    (e : c.Iso d) : FullGradedKasparovHomotopy c d :=
  (refl c).changeEndpoints (BundledGradedKasparovCycle.isoRefl c) e

variable [TopologicalSpace.SeparableSpace B]

set_option maxHeartbeats 800000 in
/-- Joining the actual interval cycles at the composed boundary unitary
produces one full witness, including a genuine semilinear grading. -/
def trans {c d k : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB}
    (h : FullGradedKasparovHomotopy c d) (h' : FullGradedKasparovHomotopy d k) :
    FullGradedKasparovHomotopy c k where
  intervalCycle := BundledGradedKasparovCycle.of
    (h.intervalCycle.cycle.intervalJoined h'.intervalCycle.cycle
      (h.targetIso.trans h'.sourceIso.symm))
  sourceIso := by
    let j := h.intervalCycle.cycle.intervalJoined h'.intervalCycle.cycle
      (h.targetIso.trans h'.sourceIso.symm)
    have u := GradedKasparovCycleIso.intervalJoinedLeftFibre h.intervalCycle.cycle
      h'.intervalCycle.cycle (h.targetIso.trans h'.sourceIso.symm) (0 : unitInterval)
    have v : GradedKasparovCycleIso (j.fibre (0 : unitInterval))
        (h.intervalCycle.cycle.fibre (0 : unitInterval)) :=
      Eq.mp (congrArg (fun t : unitInterval =>
        GradedKasparovCycleIso (j.fibre t)
          (h.intervalCycle.cycle.fibre (0 : unitInterval))) intervalLeftHalf_zero) u
    exact v.trans h.sourceIso
  targetIso := by
    let j := h.intervalCycle.cycle.intervalJoined h'.intervalCycle.cycle
      (h.targetIso.trans h'.sourceIso.symm)
    have u := GradedKasparovCycleIso.intervalJoinedRightFibre h.intervalCycle.cycle
      h'.intervalCycle.cycle (h.targetIso.trans h'.sourceIso.symm) (1 : unitInterval)
    have v : GradedKasparovCycleIso (j.fibre (1 : unitInterval))
        (h'.intervalCycle.cycle.fibre (1 : unitInterval)) :=
      Eq.mp (congrArg (fun t : unitInterval =>
        GradedKasparovCycleIso (j.fibre t)
          (h'.intervalCycle.cycle.fibre (1 : unitInterval))) intervalRightHalf_one) u
    exact v.trans h'.targetIso

end FullGradedKasparovHomotopy

namespace BundledGradedKasparovCycle

/-- Genuine full graded homotopy means one actual interval-module witness. -/
def FullHomotopic (c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB) : Prop :=
  Nonempty (FullGradedKasparovHomotopy c d)

@[refl] theorem fullHomotopic_refl (c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB) :
    c.FullHomotopic c := ⟨FullGradedKasparovHomotopy.refl c⟩

@[symm] theorem fullHomotopic_symm
    {c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB}
    (h : c.FullHomotopic d) : d.FullHomotopic c := by
  obtain ⟨h⟩ := h
  exact ⟨h.symm⟩

variable [TopologicalSpace.SeparableSpace B]

@[trans] theorem fullHomotopic_trans
    {c d k : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB}
    (h : c.FullHomotopic d) (h' : d.FullHomotopic k) : c.FullHomotopic k := by
  obtain ⟨h⟩ := h
  obtain ⟨h'⟩ := h'
  exact ⟨h.trans h'⟩

/-- The full homotopy relation itself is an equivalence relation. -/
def fullHomotopySetoid : Setoid (BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB) where
  r := FullHomotopic
  iseqv := ⟨fullHomotopic_refl, fullHomotopic_symm, fullHomotopic_trans⟩

end BundledGradedKasparovCycle

/-- Classes of genuinely graded cycles by a single full interval witness. -/
abbrev GradedKasparovHomotopyClass [TopologicalSpace.SeparableSpace B]
    (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B)
    (δA : CStarGrading A) (δB : CStarGrading B) :=
  Quotient (BundledGradedKasparovCycle.fullHomotopySetoid.{uΓ, uA, uB, uE}
    (α := α) (β := β) (δA := δA) (δB := δB))

end BC4lean.KKTheory
