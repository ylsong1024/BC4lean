import BC4lean.GroupShrinkOddHomotopy
import BC4lean.OddKasparovDirectSumIso

/-! # Genuine odd KK equivalences between arbitrary module universes

Every complete countably generated module over separable coefficients can
be represented in either chosen universe. Actual whole-cycle unitaries
identify a twice-shrunk cycle with its original cycle and identify the
shrink of a direct sum with the direct sum of the shrunk cycles. Together
with the arbitrary interval shrink witness these prove an additive
equivalence of the actual full-homotopy quotients.
-/

noncomputable section
universe uΓ uA uB uE v
namespace BC4lean.KKTheory
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace OddKK

theorem shrink_add (x y : OddKK.{uΓ, uA, uB, uE} α β) :
    shrink.{uΓ, uA, uB, uE, v} (x + y) =
      shrink.{uΓ, uA, uB, uE, v} x + shrink.{uΓ, uA, uB, uE, v} y := by
  refine Quotient.inductionOn₂ x y ?_
  intro c d
  exact mk_eq_of_iso ((c.directSum d).shrinkIso.symm.trans
    (c.shrinkIso.directSum d.shrinkIso))

def shrinkHom : OddKK.{uΓ, uA, uB, uE} α β →+ OddKK.{uΓ, uA, uB, v} α β :=
  AddMonoidHom.mk' (shrink.{uΓ, uA, uB, uE, v}) shrink_add

theorem shrink_shrink (x : OddKK.{uΓ, uA, uB, uE} α β) :
    shrink.{uΓ, uA, uB, v, uE} (shrink.{uΓ, uA, uB, uE, v} x) = x := by
  refine Quotient.inductionOn x ?_
  intro c
  let d := (c.shrink : BundledOddKasparovCycle.{uΓ, uA, uB, v} α β)
  exact mk_eq_of_iso ((d.shrinkIso : OddKasparovCycleIso d.cycle
      (d.shrink : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β).cycle).symm.trans
    (c.shrinkIso : OddKasparovCycleIso c.cycle d.cycle).symm)

def shrinkAddEquiv : OddKK.{uΓ, uA, uB, uE} α β ≃+ OddKK.{uΓ, uA, uB, v} α β where
  toFun := shrink.{uΓ, uA, uB, uE, v}
  invFun := shrink.{uΓ, uA, uB, v, uE}
  left_inv := shrink_shrink
  right_inv := shrink_shrink
  map_add' := shrink_add

@[simp] theorem shrinkAddEquiv_apply (x : OddKK.{uΓ, uA, uB, uE} α β) :
    shrinkAddEquiv.{uΓ, uA, uB, uE, v} x = shrink.{uΓ, uA, uB, uE, v} x := rfl

end OddKK
end BC4lean.KKTheory
