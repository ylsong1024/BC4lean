import BC4lean.KasparovDescentFullHomotopy
import BC4lean.KasparovDescentDirectSum
import BC4lean.GroupUniverseParityGroup

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Actual even and odd full-homotopy quotient maps for reduced descent

The construction imports the concrete reduced source representation, raw
cycles, whole-cycle isomorphisms, direct-sum unitaries, interval cycles
and full-homotopy transport.
 No map, unitary, relation-preservation statement, or
tensor norm conclusion is supplied as an extra field or hypothesis here.

The even quotient uses the actual generated relation of whole-cycle
isomorphisms and arbitrary full interval witnesses. The odd quotient uses
the actual existence of an arbitrary full odd witness. Their concrete
transport gives the quotient maps. Genuine direct-sum unitaries prove
additivity; zero preservation follows from cancellation in the actual target
group. Opposites are also related by their concrete whole-cycle unitaries.

The target has its actual enlarged module universe
`max uE (max uΓ uB)`, crossed algebra universes `max uΓ uA` and `max uΓ uB`,
and the same trivial Unit action as the constructed raw cycles. No universe
shrinking, group replacement, Clifford comparison, or product compatibility
is asserted by this file.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory.KasparovDescent

open scoped KasparovDescent

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB}
  [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]

variable (β : CStarAlgebraAction Γ B) (α : CStarAlgebraAction Γ A)

/-- Whole-cycle isomorphisms are transported by the actual completed tensor unitary. -/
def bundledEvenIso
    {c d : BundledKasparovCycle.{uΓ, uA, uB, uE} α β} (u : c.Iso d) :
    (bundledEvenCycle β α c).Iso (bundledEvenCycle β α d) :=
  evenCycleIso β α u

def bundledOddIso
    {c d : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β} (u : c.Iso d) :
    (bundledOddCycle β α c).Iso (bundledOddCycle β α d) :=
  oddCycleIso β α u

/-- Additivity uses the proved distributivity unitary on actual completed tensors. -/
def bundledEvenDirectSumIso (c d : BundledKasparovCycle.{uΓ, uA, uB, uE} α β) :
    (bundledEvenCycle β α (c.directSum d)).Iso
      ((bundledEvenCycle β α c).directSum (bundledEvenCycle β α d)) :=
  evenDirectSumIso β α c.cycle d.cycle

def bundledOddDirectSumIso (c d : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    (bundledOddCycle β α (c.directSum d)).Iso
      ((bundledOddCycle β α c).directSum (bundledOddCycle β α d)) :=
  oddDirectSumIso β α c.cycle d.cycle

/-- Opposites use the genuine identity-module unitary with its proved parity laws. -/
def bundledEvenOppositeIso (c : BundledKasparovCycle.{uΓ, uA, uB, uE} α β) :
    (bundledEvenCycle β α c.opposite).Iso (bundledEvenCycle β α c).opposite :=
  evenOppositeIso β α c.cycle

def bundledOddOppositeIso (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    (bundledOddCycle β α c.opposite).Iso (bundledOddCycle β α c).opposite :=
  oddOppositeIso β α c.cycle

/-- The actual even generating relation is preserved step by step and hence
through its proved equivalence closure. -/
theorem bundledEvenCycle_homotopic
    {c d : BundledKasparovCycle.{uΓ, uA, uB, uE} α β} (h : c.Homotopic d) :
    (bundledEvenCycle β α c).Homotopic (bundledEvenCycle β α d) := by
  induction h with
  | rel a b h =>
      change a.Isomorphic b ∨ Nonempty (FullKasparovHomotopy a b) at h
      rcases h with h | h
      · obtain ⟨u⟩ := h
        exact BundledKasparovCycle.homotopic_of_iso (bundledEvenIso β α u)
      · obtain ⟨H⟩ := h
        exact BundledKasparovCycle.homotopic_of_full (evenFullHomotopy β α H)
  | refl => exact BundledKasparovCycle.homotopic_refl _
  | symm a b _ ih => exact BundledKasparovCycle.homotopic_symm ih
  | trans a b k _ _ hab hbk => exact BundledKasparovCycle.homotopic_trans hab hbk

/-- The actual odd quotient relation consists of full witnesses, and the
constructed interval-module transport preserves that precise relation. -/
theorem bundledOddCycle_fullHomotopic
    {c d : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β}
    (h : c.FullHomotopic d) :
    (bundledOddCycle β α c).FullHomotopic (bundledOddCycle β α d) := by
  obtain ⟨H⟩ := h
  exact ⟨oddFullHomotopy β α H⟩

/-- The genuine even quotient map, retaining the actual carrier universe. -/
def evenClass : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β →
    KasparovHomotopyClass.{0, max uΓ uA, max uΓ uB, max uE (max uΓ uB)} (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α)) (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β)) :=
  Quotient.lift
    (fun c : BundledKasparovCycle.{uΓ, uA, uB, uE} α β =>
      KasparovHomotopyClass.mk (bundledEvenCycle β α c))
    (fun _ _ h => Quotient.sound (bundledEvenCycle_homotopic β α h))

/-- The genuine odd quotient map for the actual full odd witness relation. -/
def oddClass : OddKK.{uΓ, uA, uB, uE} α β →
    OddKK.{0, max uΓ uA, max uΓ uB, max uE (max uΓ uB)} (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α)) (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β)) :=
  Quotient.lift
    (fun c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β =>
      OddKK.mk (bundledOddCycle β α c))
    (fun _ _ h => Quotient.sound (bundledOddCycle_fullHomotopic β α h))

@[simp] theorem evenClass_mk (c : BundledKasparovCycle.{uΓ, uA, uB, uE} α β) :
    evenClass β α (KasparovHomotopyClass.mk c) =
      KasparovHomotopyClass.mk (bundledEvenCycle β α c) := rfl

@[simp] theorem oddClass_mk (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    oddClass β α (OddKK.mk c) = OddKK.mk (bundledOddCycle β α c) := rfl

/-- Direct-sum compatibility of the actual cycles proves even additivity. -/
theorem evenClass_add (x y : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β) :
    evenClass β α (x + y) = evenClass β α x + evenClass β α y := by
  refine Quotient.inductionOn₂' x y ?_
  intro c d
  change KasparovHomotopyClass.mk (bundledEvenCycle β α (c.directSum d)) =
    KasparovHomotopyClass.mk (bundledEvenCycle β α c) +
      KasparovHomotopyClass.mk (bundledEvenCycle β α d)
  rw [← KasparovHomotopyClass.mk_directSum]
  exact KasparovHomotopyClass.mk_eq_of_iso (bundledEvenDirectSumIso β α c d)

/-- Odd additivity uses the same genuine direct-sum unitary in the odd picture. -/
theorem oddClass_add (x y : OddKK.{uΓ, uA, uB, uE} α β) :
    oddClass β α (x + y) = oddClass β α x + oddClass β α y := by
  refine Quotient.inductionOn₂' x y ?_
  intro c d
  change OddKK.mk (bundledOddCycle β α (c.directSum d)) =
    OddKK.mk (bundledOddCycle β α c) + OddKK.mk (bundledOddCycle β α d)
  rw [← OddKK.mk_directSum]
  exact OddKK.mk_eq_of_iso (bundledOddDirectSumIso β α c d)

/-- The actual class homomorphism in even degree. The zero law is a consequence
of the proved additive law and target-group cancellation. -/
def evenClassHom : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β →+
    KasparovHomotopyClass.{0, max uΓ uA, max uΓ uB, max uE (max uΓ uB)} (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α)) (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β)) :=
  AddMonoidHom.mk' (evenClass β α) (evenClass_add β α)

def oddClassHom : OddKK.{uΓ, uA, uB, uE} α β →+
    OddKK.{0, max uΓ uA, max uΓ uB, max uE (max uΓ uB)} (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α)) (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β)) :=
  AddMonoidHom.mk' (oddClass β α) (oddClass_add β α)

@[simp] theorem evenClassHom_apply (x : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β) :
    evenClassHom β α x = evenClass β α x := rfl

@[simp] theorem oddClassHom_apply (x : OddKK.{uΓ, uA, uB, uE} α β) :
    oddClassHom β α x = oddClass β α x := rfl

@[simp] theorem evenClass_zero :
    evenClass β α (0 : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β) = 0 :=
  (evenClassHom β α).map_zero

@[simp] theorem oddClass_zero :
    oddClass β α (0 : OddKK.{uΓ, uA, uB, uE} α β) = 0 :=
  (oddClassHom β α).map_zero

/-- The concrete opposite-cycle unitary identifies the image of an actual
opposite representative with the negative target class. -/
theorem evenClass_mk_opposite (c : BundledKasparovCycle.{uΓ, uA, uB, uE} α β) :
    evenClass β α (KasparovHomotopyClass.mk c.opposite) =
      -evenClass β α (KasparovHomotopyClass.mk c) := by
  rw [evenClass_mk, evenClass_mk, ← KasparovHomotopyClass.mk_opposite]
  exact KasparovHomotopyClass.mk_eq_of_iso (bundledEvenOppositeIso β α c)

theorem oddClass_mk_opposite (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    oddClass β α (OddKK.mk c.opposite) = -oddClass β α (OddKK.mk c) := by
  rw [oddClass_mk, oddClass_mk, ← OddKK.mk_opposite]
  exact OddKK.mk_eq_of_iso (bundledOddOppositeIso β α c)

@[simp] theorem evenClass_neg (x : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β) :
    evenClass β α (-x) = -evenClass β α x :=
  map_neg (evenClassHom β α) x

@[simp] theorem oddClass_neg (x : OddKK.{uΓ, uA, uB, uE} α β) :
    oddClass β α (-x) = -oddClass β α x :=
  map_neg (oddClassHom β α) x

/-- The genuine parity-wise class map into the actual enlarged ordinary
quotients used by the concrete Unit-action cycles. -/
def classHom (p : Bool) :
    GroupUniverseParityGroup.KKParityGroup.{uΓ, uA, uB, uE} p α β →+
    GroupUniverseParityGroup.KKParityGroup.{0, max uΓ uA, max uΓ uB,
      max uE (max uΓ uB)} p (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α)) (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β)) := by
  cases p
  · exact evenClassHom β α
  · exact oddClassHom β α

@[simp] theorem classHom_even (x : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β) :
    classHom β α false x = evenClass β α x := rfl

@[simp] theorem classHom_odd (x : OddKK.{uΓ, uA, uB, uE} α β) :
    classHom β α true x = oddClass β α x := rfl

end BC4lean.KKTheory.KasparovDescent
