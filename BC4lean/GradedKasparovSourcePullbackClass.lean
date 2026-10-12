import BC4lean.GradedKasparovSourcePullback
import BC4lean.GradedKasparovFullDirectSum

/-! # Source pullback descends to actual full graded classes and preserves sums

The quotient relation is the existence of one full arbitrary-module witness.
Its sum is represented by the actual raw graded direct sum and descends using
the genuine full-witness sum. Source pullback is well-defined by transporting
that single witness, and its sum law uses the actual whole-cycle sum unitary.
No group inverse law for arbitrary source grading is asserted here.
-/

noncomputable section
universe uΓ uA uA' uB uE
namespace BC4lean.KKTheory

variable {Γ : Type uΓ} {A : Type uA} {A' : Type uA'} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A'] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

namespace GradedKasparovHomotopyClass

def mk (c : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA δB) :
    GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α β δA δB := Quotient.mk _ c

theorem mk_eq_mk_iff_full {c d : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA δB} :
    mk c = mk d ↔ Nonempty (FullGradedKasparovHomotopy c d) := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

theorem mk_eq_of_iso {c d : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA δB}
    (e : c.Iso d) : mk c = mk d := Quotient.sound ⟨FullGradedKasparovHomotopy.ofIso e⟩

theorem mk_eq_of_full {c d : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA δB}
    (h : FullGradedKasparovHomotopy c d) : mk c = mk d := Quotient.sound ⟨h⟩

instance instAdd : Add (GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α β δA δB) where
  add := Quotient.lift₂
    (fun (c d : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA δB) => mk (c.directSum d))
    (fun _ _ _ _ h h' => Quotient.sound (BundledGradedKasparovCycle.fullHomotopic_directSum h h'))

@[simp] theorem mk_directSum (c d : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA δB) :
    mk (c.directSum d) = mk c + mk d := rfl

variable (α' : CStarAlgebraAction Γ A') (δA' : CStarGrading A')
  (hα' : α'.PreservesGrading δA') (f : A' →⋆ₙₐ[ℂ] A)
  (hact : ∀ g a, f (α'.automorphism g a) = α.automorphism g (f a))
  (hgrade : ∀ a, f (δA'.automorphism a) = δA.automorphism (f a))

def sourcePullback : GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α β δA δB →
    GradedKasparovHomotopyClass.{uΓ,uA',uB,uE} α' β δA' δB :=
  Quotient.lift
    (fun c : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA δB =>
      mk (c.sourcePullback α' δA' hα' f hact hgrade))
    (by
      intro c d h
      obtain ⟨h⟩ := h
      exact Quotient.sound ⟨h.sourcePullback α' δA' hα' f hact hgrade⟩)

@[simp] theorem sourcePullback_mk (c : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA δB) :
    sourcePullback α' δA' hα' f hact hgrade (mk c) =
      mk (c.sourcePullback α' δA' hα' f hact hgrade) := rfl

theorem sourcePullback_add (x y : GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α β δA δB) :
    sourcePullback α' δA' hα' f hact hgrade (x + y) =
      sourcePullback α' δA' hα' f hact hgrade x + sourcePullback α' δA' hα' f hact hgrade y := by
  refine Quotient.inductionOn₂ x y ?_
  intro c d
  change mk ((c.directSum d).sourcePullback α' δA' hα' f hact hgrade) =
    mk ((c.sourcePullback α' δA' hα' f hact hgrade).directSum
      (d.sourcePullback α' δA' hα' f hact hgrade))
  exact mk_eq_of_iso (c.cycle.sourcePullbackDirectSumIso α' δA' hα' f hact hgrade d.cycle)

end GradedKasparovHomotopyClass
end BC4lean.KKTheory
