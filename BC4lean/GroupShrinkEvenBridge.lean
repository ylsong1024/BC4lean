import BC4lean.GroupShrinkGradedEquivalence
import BC4lean.GroupUniverseEvenBridge

/-! # Genuine even universe comparison via actual full witnesses

The actual trivial-grading full-interval conversions and the proved graded
shrink equivalence identify the existing even homotopy-class groups in
any two chosen module universes. Its value on a raw class is the genuine
whole Kasparov cycle transported to the small Hilbert-module model.
-/

noncomputable section
universe uΓ uA uB uE v
namespace BC4lean.KKTheory
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

def BundledKasparovCycle.shrink (c : BundledKasparovCycle.{uΓ, uA, uB, uE} α β) :
    BundledKasparovCycle.{uΓ, uA, uB, v} α β := by
  letI : Small.{v} c.carrier := c.cycle.countablyGenerated.small
  exact BundledKasparovCycle.of (c.cycle.shrink : KasparovCycle α β (Shrink.{v} c.carrier))

def BundledKasparovCycle.shrinkIso (c : BundledKasparovCycle.{uΓ, uA, uB, uE} α β) :
    KasparovCycleIso c.cycle (c.shrink : BundledKasparovCycle.{uΓ, uA, uB, v} α β).cycle := by
  letI : Small.{v} c.carrier := c.cycle.countablyGenerated.small
  exact c.cycle.shrinkIso

namespace GroupShrinkEvenBridge

def addEquivalence : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β ≃+
    KasparovHomotopyClass.{uΓ, uA, uB, v} α β :=
  (GroupUniverseEvenBridge.addEquivalence.{uΓ, uA, uB, uE}).symm.trans
    ((GradedKasparovHomotopyClass.shrinkAddEquiv.{uΓ, uA, uB, uE, v}).trans
      GroupUniverseEvenBridge.addEquivalence)

@[simp] theorem addEquivalence_mk (c : BundledKasparovCycle.{uΓ, uA, uB, uE} α β) :
    addEquivalence (KasparovHomotopyClass.mk c) =
      KasparovHomotopyClass.mk (c.shrink : BundledKasparovCycle.{uΓ, uA, uB, v} α β) := by
  apply KasparovHomotopyClass.mk_eq_of_iso
  exact
    { moduleEquiv := HilbertModuleEquiv.refl
      grading_intertwine _ := rfl
      action_intertwine _ _ := rfl
      representation_intertwine _ _ := rfl
      operator_intertwine _ := rfl }

end GroupShrinkEvenBridge
end BC4lean.KKTheory
