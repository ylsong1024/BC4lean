import BC4lean.CliffordTensorParityQuotient
import BC4lean.CliffordParityDirectSum
import BC4lean.GradedCoefficientDirectSum

/-! # Genuine Clifford tensor parity is an additive equivalence

The actual tensor quotient inherits the proved coordinate quotient group.
The inverse whole-cycle coefficient transport and the sum-change unitary
show that its addition is the class of the actual graded Hilbert direct sum.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

instance cliffordTensorKKAddCommGroup : AddCommGroup (CliffordTensorKK.{uΓ, uA, uB, uE} α β) :=
  (cliffordTensorCoordinateQuotientEquiv (α := α) (β := β)).addCommGroup

def cliffordTensorCoordinateQuotientAddEquiv :
    CliffordTensorKK.{uΓ, uA, uB, uE} α β ≃+ CliffordKK.{uΓ, uA, uB, uE} α β :=
  (cliffordTensorCoordinateQuotientEquiv (α := α) (β := β)).addEquiv

def cliffordTensorParityAddEquiv :
    OddKK.{uΓ, uA, uB, uE} α β ≃+ CliffordTensorKK.{uΓ, uA, uB, uE} α β :=
  cliffordParityAddEquiv.trans cliffordTensorCoordinateQuotientAddEquiv.symm

@[simp] theorem cliffordTensorParityAddEquiv_apply (x : OddKK.{uΓ, uA, uB, uE} α β) :
    cliffordTensorParityAddEquiv x = cliffordTensorParityEquiv x := rfl

namespace CliffordTensorKK
def mk (c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α (cliffordTensorAction β)
    CStarGrading.trivial cliffordTensorGrading) : CliffordTensorKK.{uΓ, uA, uB, uE} α β :=
  Quotient.mk _ c

theorem mk_eq_of_iso
    {c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α (cliffordTensorAction β)
      CStarGrading.trivial cliffordTensorGrading} (u : c.Iso d) : mk c = mk d :=
  Quotient.sound ⟨FullGradedKasparovHomotopy.cliffordTensorOfIso u⟩

/-- The actual Clifford tensor group sum is represented by the actual raw
graded Hilbert-module direct sum over the constructed tensor coefficients. -/
@[simp] theorem mk_directSum
    (c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α (cliffordTensorAction β)
      CStarGrading.trivial cliffordTensorGrading) :
    mk (c.directSum d) = mk c + mk d := by
  apply cliffordTensorCoordinateQuotientAddEquiv.injective
  rw [map_add]
  change CliffordKK.mk ((c.directSum d).changeCoefficients (cliffordTensorGradedCoefficientEquiv β)) =
    CliffordKK.mk (c.changeCoefficients (cliffordTensorGradedCoefficientEquiv β)) +
      CliffordKK.mk (d.changeCoefficients (cliffordTensorGradedCoefficientEquiv β))
  rw [← CliffordKK.mk_directSum]
  exact CliffordKK.mk_eq_of_iso
    (c.cycle.changeCoefficientsDirectSumIso d.cycle (cliffordTensorGradedCoefficientEquiv β))

end CliffordTensorKK
end BC4lean.KKTheory
