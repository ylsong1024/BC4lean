import BC4lean.CliffordTensorOrder
import BC4lean.FullGradedCoefficientTransport
import BC4lean.CliffordParityQuotient

/-! # Genuine Clifford tensor parity on arbitrary-module homotopy quotients

The coefficient is the constructed complete tensor B ⊗ Cl₁, with its proved
maximal C⋆ norm and actual tensor grading. The coordinate star equivalence
transports whole cycles and arbitrary full interval witnesses. Its inverse
on quotient classes uses the actual inverse coefficient-change cycle
unitaries. No equivalence of full homotopy relations is assumed.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

/-- The proved tensor coordinates, including their genuine grading and
equivariance laws, packaged for actual whole-cycle coefficient transport. -/
def cliffordTensorGradedCoefficientEquiv (β : CStarAlgebraAction Γ B) :
    GradedCoefficientEquiv (cliffordTensorAction β) cliffordTensorGrading
      (cliffordCoefficientAction β) cliffordCoefficientGrading where
  starAlgEquiv := cliffordTensorCoordinateStarAlgEquiv
  action_intertwine := cliffordTensorCoordinate_action β
  grading_intertwine := cliffordTensorCoordinate_grading

namespace FullGradedKasparovHomotopy

def cliffordTensorOfIso
    {c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α (cliffordTensorAction β)
      CStarGrading.trivial cliffordTensorGrading} (u : c.Iso d) :
    FullGradedKasparovHomotopy c d := by
  let e := cliffordTensorGradedCoefficientEquiv β
  have h : FullGradedKasparovHomotopy (c.changeCoefficients e) (d.changeCoefficients e) :=
    cliffordOfIso (c := c.changeCoefficients e) (d := d.changeCoefficients e)
      (u.changeCoefficients e)
  exact (h.changeCoefficients e.symm).changeEndpoints (e := c) (f := d)
    (c.cycle.changeCoefficientsInverseIso e) (d.cycle.changeCoefficientsInverseIso e)

end FullGradedKasparovHomotopy

namespace BundledGradedKasparovCycle

def CliffordTensorFullHomotopic
    (c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α (cliffordTensorAction β)
      CStarGrading.trivial cliffordTensorGrading) : Prop :=
  Nonempty (FullGradedKasparovHomotopy c d)

/-- Actual single full tensor interval witnesses form an equivalence relation,
by invertible transport to the proved actual coordinate witnesses. -/
def cliffordTensorFullHomotopySetoid :
    Setoid (BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α (cliffordTensorAction β)
      CStarGrading.trivial cliffordTensorGrading) where
  r := CliffordTensorFullHomotopic
  iseqv :=
    { refl c := ⟨FullGradedKasparovHomotopy.cliffordTensorOfIso (isoRefl c)⟩
      symm := by
        intro c d h
        let e := cliffordTensorGradedCoefficientEquiv β
        apply (fullGradedHomotopy_iff_changeCoefficients d c e).mpr
        exact (cliffordFullHomotopySetoid.iseqv.symm
          ((fullGradedHomotopy_iff_changeCoefficients c d e).mp h))
      trans := by
        intro c d k h h'
        let e := cliffordTensorGradedCoefficientEquiv β
        apply (fullGradedHomotopy_iff_changeCoefficients c k e).mpr
        exact (cliffordFullHomotopySetoid.iseqv.trans
          ((fullGradedHomotopy_iff_changeCoefficients c d e).mp h)
          ((fullGradedHomotopy_iff_changeCoefficients d k e).mp h')) }

end BundledGradedKasparovCycle

/-- Degree one represented with the actual complete Clifford tensor
coefficient algebra and actual full arbitrary interval witnesses. -/
abbrev CliffordTensorKK (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B) :=
  Quotient (BundledGradedKasparovCycle.cliffordTensorFullHomotopySetoid
    (α := α) (β := β) :
      Setoid (BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α (cliffordTensorAction β)
        CStarGrading.trivial cliffordTensorGrading))

/-- Whole-cycle and whole-witness transport induces the actual tensor-coordinate
quotient equivalence. Both inverse identities use the proved cycle unitaries. -/
def cliffordTensorCoordinateQuotientEquiv :
    CliffordTensorKK.{uΓ, uA, uB, uE} α β ≃ CliffordKK.{uΓ, uA, uB, uE} α β where
  toFun := Quotient.map (fun c => c.changeCoefficients (cliffordTensorGradedCoefficientEquiv β)) (by
    intro c d h
    change Nonempty (FullGradedKasparovHomotopy c d) at h
    change Nonempty (FullGradedKasparovHomotopy
      (c.changeCoefficients (cliffordTensorGradedCoefficientEquiv β))
      (d.changeCoefficients (cliffordTensorGradedCoefficientEquiv β)))
    obtain ⟨h⟩ := h
    exact ⟨h.changeCoefficients (cliffordTensorGradedCoefficientEquiv β)⟩)
  invFun := Quotient.map (fun c => c.changeCoefficients (cliffordTensorGradedCoefficientEquiv β).symm) (by
    intro c d h
    change Nonempty (FullGradedKasparovHomotopy c d) at h
    change Nonempty (FullGradedKasparovHomotopy
      (c.changeCoefficients (cliffordTensorGradedCoefficientEquiv β).symm)
      (d.changeCoefficients (cliffordTensorGradedCoefficientEquiv β).symm))
    obtain ⟨h⟩ := h
    exact ⟨h.changeCoefficients (cliffordTensorGradedCoefficientEquiv β).symm⟩)
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro c
    exact Quotient.sound ⟨FullGradedKasparovHomotopy.cliffordTensorOfIso
      (c := (c.changeCoefficients (cliffordTensorGradedCoefficientEquiv β)).changeCoefficients
        (cliffordTensorGradedCoefficientEquiv β).symm) (d := c)
      (c.cycle.changeCoefficientsInverseIso (cliffordTensorGradedCoefficientEquiv β))⟩
  right_inv q := by
    refine Quotient.inductionOn q ?_
    intro c
    have u : ((c.changeCoefficients (cliffordTensorGradedCoefficientEquiv β).symm).changeCoefficients
        (cliffordTensorGradedCoefficientEquiv β)).Iso c := by
      change GradedKasparovCycleIso
        ((c.cycle.changeCoefficients (cliffordTensorGradedCoefficientEquiv β).symm).changeCoefficients
          (cliffordTensorGradedCoefficientEquiv β)) c.cycle
      let e := cliffordTensorGradedCoefficientEquiv β
      let P (f : GradedCoefficientEquiv (cliffordTensorAction β) cliffordTensorGrading
          (cliffordCoefficientAction β) cliffordCoefficientGrading) :=
        GradedKasparovCycleIso ((c.cycle.changeCoefficients e.symm).changeCoefficients f) c.cycle
      exact Eq.mp (congrArg P (GradedCoefficientEquiv.symm_symm e))
        (c.cycle.changeCoefficientsInverseIso e.symm)
    exact Quotient.sound ⟨FullGradedKasparovHomotopy.cliffordOfIso
      (c := (c.changeCoefficients (cliffordTensorGradedCoefficientEquiv β).symm).changeCoefficients
        (cliffordTensorGradedCoefficientEquiv β)) (d := c) u⟩

/-- Odd KK is identified with the genuine one-Clifford tensor model on
the quotients by full arbitrary interval homotopies. -/
def cliffordTensorParityEquiv :
    OddKK.{uΓ, uA, uB, uE} α β ≃ CliffordTensorKK.{uΓ, uA, uB, uE} α β :=
  cliffordParityEquiv.trans cliffordTensorCoordinateQuotientEquiv.symm

end BC4lean.KKTheory
