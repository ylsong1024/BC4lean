import BC4lean.BundledOddKasparovCycle
import BC4lean.OddKasparovDirectSumIso
import BC4lean.OddKasparovInverseRotation
import BC4lean.BundledKasparovDirectSum

/-! # Actual direct sums, inverses and zero for bundled odd cycles -/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

def zeroOddKasparovCycle (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B) :
    OddKasparovCycle α β ZeroHilbertModule.{uE} :=
  OddKasparovCycle.zeroRepresentation isCountablyGeneratedModule_of_subsingleton (zeroHilbertModuleAction β)

namespace OddKasparovCycleIso
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

def sumZeroRight (c : OddKasparovCycle α β E) :
    OddKasparovCycleIso (c.directSum (zeroOddKasparovCycle α β)) c where
  moduleEquiv := HilbertModuleEquiv.sumZeroRight
  action_intertwine _ _ := rfl
  representation_intertwine a x := by
    change HilbertModuleEquiv.sumZeroRight
      (sumMap (c.representation a) ((zeroOddKasparovCycle α β).representation a) x) =
        c.representation a x.fst
    simp only [sumMap_apply, HilbertModuleEquiv.sumZeroRight_apply, sumMk_fst]
  operator_intertwine x := by
    change HilbertModuleEquiv.sumZeroRight
      (sumMap c.operator (zeroOddKasparovCycle α β).operator x) = c.operator x.fst
    simp only [sumMap_apply, HilbertModuleEquiv.sumZeroRight_apply, sumMk_fst]

def sumZeroLeft (c : OddKasparovCycle α β E) :
    OddKasparovCycleIso ((zeroOddKasparovCycle α β).directSum c) c :=
  (sumComm (zeroOddKasparovCycle α β) c).trans (sumZeroRight c)

def opposite {F : Type uE} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]
    {c : OddKasparovCycle α β E} {d : OddKasparovCycle α β F}
    (u : OddKasparovCycleIso c d) : OddKasparovCycleIso c.opposite d.opposite where
  moduleEquiv := u.moduleEquiv
  action_intertwine := u.action_intertwine
  representation_intertwine := u.representation_intertwine
  operator_intertwine x := by
    simp only [OddKasparovCycle.opposite_operator, AdjointableMap.coe_neg_apply,
      HilbertModuleEquiv.map_neg, u.operator_intertwine]
end OddKasparovCycleIso

namespace BundledOddKasparovCycle

def directSum (c d : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β := of (c.cycle.directSum d.cycle)
def opposite (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β := of c.cycle.opposite
def zero (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B) :
    BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β := of (zeroOddKasparovCycle α β)

def directSumCommIso (c d : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    (c.directSum d).Iso (d.directSum c) := OddKasparovCycleIso.sumComm c.cycle d.cycle
def directSumAssocIso (c d k : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    ((c.directSum d).directSum k).Iso (c.directSum (d.directSum k)) :=
  OddKasparovCycleIso.sumAssoc c.cycle d.cycle k.cycle
def directSumZeroRightIso (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    (c.directSum (zero α β)).Iso c := OddKasparovCycleIso.sumZeroRight c.cycle
def directSumZeroLeftIso (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    ((zero α β).directSum c).Iso c := OddKasparovCycleIso.sumZeroLeft c.cycle

end BundledOddKasparovCycle
end BC4lean.KKTheory
