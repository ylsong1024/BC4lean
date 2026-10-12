import BC4lean.GroupUniverseExternalEvenInterval
import BC4lean.CliffordExternalEvenQuotient
import BC4lean.GroupUniverseEvenBridge

/-! # Genuine external even full classes with independent universes

The actual pair of the original module retains uE. Its arbitrary full
interval transport preserves all evaluated data, and the actual Koszul
pair/sum unitary proves the raw direct-sum identity used for additivity.
-/

noncomputable section
universe uΓ uB uC uE
namespace BC4lean.KKTheory.GroupUniverseExternalEvenClass
variable {Γ : Type uΓ} {B : Type uB} {C : Type uC} [Group Γ]
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder C] [StarOrderedRing C] [TopologicalSpace.SeparableSpace C]
  {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

def externalClass (x : KasparovHomotopyClass.{uΓ,uB,uC,uE} β γ) :
    GradedKasparovHomotopyClass.{uΓ,uB,uC,uE} (cliffordCoefficientAction β)
      (cliffordCoefficientAction γ) cliffordCoefficientGrading cliffordCoefficientGrading :=
  Quotient.lift (fun c => GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
    (CliffordExternalEvenCycle.cycle (GradedKasparovCycle.ofKasparovCycle c.cycle)))) (by
      intro c d h
      obtain ⟨h⟩ := BundledKasparovCycle.homotopic_iff_full.mp h
      exact GradedKasparovHomotopyClass.mk_eq_of_full (GroupUniverseExternalEvenCycle.full h)) x

@[simp] theorem externalClass_mk (c : BundledKasparovCycle.{uΓ,uB,uC,uE} β γ) :
    externalClass (KasparovHomotopyClass.mk c) =
      GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
        (CliffordExternalEvenCycle.cycle (GradedKasparovCycle.ofKasparovCycle c.cycle))) := rfl

theorem externalClass_add (x y : KasparovHomotopyClass.{uΓ,uB,uC,uE} β γ) :
    externalClass (x + y) = externalClass x + externalClass y := by
  refine Quotient.inductionOn₂' x y ?_
  intro c d
  change externalClass (KasparovHomotopyClass.mk c + KasparovHomotopyClass.mk d) =
    externalClass (KasparovHomotopyClass.mk c) + externalClass (KasparovHomotopyClass.mk d)
  rw [← KasparovHomotopyClass.mk_directSum]
  simp only [externalClass_mk, ← GradedKasparovHomotopyClass.mk_directSum]
  exact GradedKasparovHomotopyClass.mk_eq_of_iso
    (CliffordExternalEvenCycle.directSumIso
      (GradedKasparovCycle.ofKasparovCycle c.cycle)
      (GradedKasparovCycle.ofKasparovCycle d.cycle)).symm

end BC4lean.KKTheory.GroupUniverseExternalEvenClass
