import BC4lean.FullGradedKasparovHomotopyEquivalence
import BC4lean.PositiveGradedULiftFullWitness

/-! # Single full graded witnesses with independent carrier universes

The endpoint modules and the actual interval module have independent
universes. A witness still consists of one complete countably generated
interval-coefficient cycle and genuine whole-cycle unitary identifications
of its true completed fibres. Composition uses the actual endpoint-matched
module, retaining its semilinear grading and every localized compact defect.
The original fixed-universe interface is recovered on the diagonal, and
canonical ULift transport supplies a fixed-universe witness in a common
universe without changing any cycle law.
-/

noncomputable section
universe uΓ uA uB uE uF uG uH uM uN
namespace BC4lean.KKTheory

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

/-- One genuine full interval witness; neither endpoint carrier universe
is required to equal the other endpoint or the interval carrier universe. -/
structure HeterogeneousFullGradedKasparovHomotopy
    (c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB)
    (d : BundledGradedKasparovCycle.{uΓ, uA, uB, uF} α β δA δB) where
  intervalCycle : BundledGradedKasparovCycle.{uΓ, uA, uB, uM} α
    (β.continuousSections (X := unitInterval)) δA δB.continuousSections
  sourceIso : GradedKasparovCycleIso (intervalCycle.cycle.fibre 0) c.cycle
  targetIso : GradedKasparovCycleIso (intervalCycle.cycle.fibre 1) d.cycle

namespace HeterogeneousFullGradedKasparovHomotopy

/-- A fixed-universe full witness retains exactly its interval cycle and
both actual fibre unitaries in the independent-universe interface. -/
def ofFull
    {c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB}
    (h : FullGradedKasparovHomotopy c d) :
    HeterogeneousFullGradedKasparovHomotopy.{uΓ, uA, uB, uE, uE, uE} c d where
  intervalCycle := h.intervalCycle
  sourceIso := h.sourceIso
  targetIso := h.targetIso

/-- On the diagonal the independent-universe witness is exactly an
original full witness, with no replacement of its interval module. -/
def toFull
    {c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB}
    (h : HeterogeneousFullGradedKasparovHomotopy.{uΓ, uA, uB, uE, uE, uE} c d) :
    FullGradedKasparovHomotopy c d where
  intervalCycle := h.intervalCycle
  sourceIso := h.sourceIso
  targetIso := h.targetIso

/-- Endpoint changes compose raw whole-cycle unitaries across independent
universes and keep the same actual interval cycle. -/
def changeEndpoints
    {c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB}
    {d : BundledGradedKasparovCycle.{uΓ, uA, uB, uF} α β δA δB}
    {e : BundledGradedKasparovCycle.{uΓ, uA, uB, uG} α β δA δB}
    {f : BundledGradedKasparovCycle.{uΓ, uA, uB, uH} α β δA δB}
    (h : HeterogeneousFullGradedKasparovHomotopy.{uΓ, uA, uB, uE, uF, uM} c d)
    (u : GradedKasparovCycleIso c.cycle e.cycle)
    (v : GradedKasparovCycleIso d.cycle f.cycle) :
    HeterogeneousFullGradedKasparovHomotopy.{uΓ, uA, uB, uG, uH, uM} e f where
  intervalCycle := h.intervalCycle
  sourceIso := h.sourceIso.trans u
  targetIso := h.targetIso.trans v

/-- Actual reversal retains one full witness and its complete cycle data. -/
def symm
    {c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB}
    {d : BundledGradedKasparovCycle.{uΓ, uA, uB, uF} α β δA δB}
    (h : HeterogeneousFullGradedKasparovHomotopy.{uΓ, uA, uB, uE, uF, uM} c d) :
    HeterogeneousFullGradedKasparovHomotopy.{uΓ, uA, uB, uF, uE, uM} d c where
  intervalCycle := BundledGradedKasparovCycle.of h.intervalCycle.cycle.intervalReversed
  sourceIso := (GradedKasparovCycleIso.intervalReversedFibreAt
    h.intervalCycle.cycle 0 1 unitInterval.symm_zero).trans h.targetIso
  targetIso := (GradedKasparovCycleIso.intervalReversedFibreAt
    h.intervalCycle.cycle 1 0 unitInterval.symm_one).trans h.sourceIso

variable [TopologicalSpace.SeparableSpace B]

set_option maxHeartbeats 800000 in
/-- Actual matched-module composition. The joined carrier is the closed
submodule of the two interval carriers' product, in their maximum universe. -/
def trans
    {c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB}
    {d : BundledGradedKasparovCycle.{uΓ, uA, uB, uF} α β δA δB}
    {k : BundledGradedKasparovCycle.{uΓ, uA, uB, uG} α β δA δB}
    (h : HeterogeneousFullGradedKasparovHomotopy.{uΓ, uA, uB, uE, uF, uM} c d)
    (h' : HeterogeneousFullGradedKasparovHomotopy.{uΓ, uA, uB, uF, uG, uN} d k) :
    HeterogeneousFullGradedKasparovHomotopy.{uΓ, uA, uB, uE, uG, max uM uN} c k where
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

omit [TopologicalSpace.SeparableSpace B] in
/-- Canonical actual ULift transport gives an original full witness in
the common maximum of the endpoint and interval carrier universes. -/
def commonUniverse
    {c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB}
    {d : BundledGradedKasparovCycle.{uΓ, uA, uB, uF} α β δA δB}
    (h : HeterogeneousFullGradedKasparovHomotopy.{uΓ, uA, uB, uE, uF, uM} c d) :
    FullGradedKasparovHomotopy
      (BundledGradedKasparovCycle.of
        (c.cycle.ulift : GradedKasparovCycle α β δA δB
          (ULift.{max (max uE uF) uM} c.carrier)))
      (BundledGradedKasparovCycle.of
        (d.cycle.ulift : GradedKasparovCycle α β δA δB
          (ULift.{max (max uE uF) uM} d.carrier))) where
  intervalCycle := BundledGradedKasparovCycle.of
    (h.intervalCycle.cycle.ulift : GradedKasparovCycle α
      (β.continuousSections (X := unitInterval)) δA δB.continuousSections
      (ULift.{max (max uE uF) uM} h.intervalCycle.carrier))
  sourceIso := (h.intervalCycle.cycle.uliftFibreIso 0).trans h.sourceIso.ulift
  targetIso := (h.intervalCycle.cycle.uliftFibreIso 1).trans h.targetIso.ulift

end HeterogeneousFullGradedKasparovHomotopy
end BC4lean.KKTheory
