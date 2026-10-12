import BC4lean.GroupShrinkGradedHomotopy

/-! # Actual graded quotient equivalences across arbitrary module universes

The whole-cycle units identify a twice-shrunk cycle with its original and
identify shrinking a direct sum with the sum of the shrunk cycles. This
gives an additive equivalence of the genuine full graded quotients, with
both algebra gradings retained. Only the established addition is used;
no group inverse for a general nontrivial source grading is assumed.
-/

noncomputable section
universe uΓ uA uB uE v
namespace BC4lean.KKTheory.GradedKasparovHomotopyClass
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

theorem shrink_add (x y : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE} α β δA δB) :
    shrink.{uΓ, uA, uB, uE, v} (x + y) =
      shrink.{uΓ, uA, uB, uE, v} x + shrink.{uΓ, uA, uB, uE, v} y := by
  refine Quotient.inductionOn₂ x y ?_
  intro c d
  exact mk_eq_of_iso ((c.directSum d).shrinkIso.symm.trans
    (c.shrinkIso.directSum d.shrinkIso))

theorem shrink_shrink (x : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE} α β δA δB) :
    shrink.{uΓ, uA, uB, v, uE} (shrink.{uΓ, uA, uB, uE, v} x) = x := by
  refine Quotient.inductionOn x ?_
  intro c
  let d := (c.shrink : BundledGradedKasparovCycle.{uΓ, uA, uB, v} α β δA δB)
  exact mk_eq_of_iso ((d.shrinkIso : GradedKasparovCycleIso d.cycle
      (d.shrink : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB).cycle).symm.trans
    (c.shrinkIso : GradedKasparovCycleIso c.cycle d.cycle).symm)

def shrinkAddEquiv : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE} α β δA δB ≃+
    GradedKasparovHomotopyClass.{uΓ, uA, uB, v} α β δA δB where
  toFun := shrink.{uΓ, uA, uB, uE, v}
  invFun := shrink.{uΓ, uA, uB, v, uE}
  left_inv := shrink_shrink
  right_inv := shrink_shrink
  map_add' := shrink_add

@[simp] theorem shrinkAddEquiv_apply
    (x : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE} α β δA δB) :
    shrinkAddEquiv.{uΓ, uA, uB, uE, v} x = shrink.{uΓ, uA, uB, uE, v} x := rfl

end BC4lean.KKTheory.GradedKasparovHomotopyClass
