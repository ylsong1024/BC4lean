import BC4lean.GroupUniverseOddSourceInterval
import BC4lean.CliffordOddSourceDirectSumIso
import BC4lean.OddKasparovHomotopyGroup
import BC4lean.GradedKasparovSourcePullbackClass

/-! # Genuine signed Clifford source classes with independent universes

The Pauli operator acts on the actual sum of the original whole module.
The same arbitrary full interval witness transports both sum coordinates;
the real four-coordinate sum unitary proves addition.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory.GroupUniverseOddSourceClass
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

def sourceClass (x : OddKK.{uΓ,uA,uB,uE} α β) :
    GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} (cliffordCoefficientAction α) β
      cliffordCoefficientGrading CStarGrading.trivial :=
  Quotient.lift (fun c : BundledOddKasparovCycle.{uΓ,uA,uB,uE} α β =>
    GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
      (CliffordOddSourceCycle.cycle c.cycle))) (by
      intro c d h
      obtain ⟨h⟩ := h
      exact GradedKasparovHomotopyClass.mk_eq_of_full (GroupUniverseOddSourceCycle.full h)) x

@[simp] theorem sourceClass_mk (c : BundledOddKasparovCycle.{uΓ,uA,uB,uE} α β) :
    sourceClass (OddKK.mk c) =
      GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
        (CliffordOddSourceCycle.cycle c.cycle)) := rfl

theorem sourceClass_add (x y : OddKK.{uΓ,uA,uB,uE} α β) :
    sourceClass (x + y) = sourceClass x + sourceClass y := by
  refine Quotient.inductionOn₂ x y ?_
  intro c d
  change sourceClass (OddKK.mk c + OddKK.mk d) =
    sourceClass (OddKK.mk c) + sourceClass (OddKK.mk d)
  rw [← OddKK.mk_directSum]
  simp only [sourceClass_mk, ← GradedKasparovHomotopyClass.mk_directSum]
  exact GradedKasparovHomotopyClass.mk_eq_of_iso
    (CliffordOddSourceCycle.directSumIso c.cycle d.cycle)

end BC4lean.KKTheory.GroupUniverseOddSourceClass
