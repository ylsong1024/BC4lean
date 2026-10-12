import BC4lean.FullOddKasparovOperations

/-! # The genuine odd full-homotopy quotient is an abelian group

Addition is the actual Hilbert-module direct sum and negation is the actual
opposite Fredholm operator. Their descent uses full arbitrary interval
witnesses and the genuine sum-fibre unitary. All group laws use actual cycle
unitaries, inverse rotation, the degenerate cone, and matched concatenation.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace OddKK

def mk (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) : OddKK.{uΓ, uA, uB, uE} α β :=
  Quotient.mk _ c

theorem mk_eq_mk_iff_full {c d : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β} :
    mk c = mk d ↔ Nonempty (FullOddKasparovHomotopy c d) := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

theorem mk_eq_of_iso {c d : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β} (u : c.Iso d) :
    mk c = mk d := Quotient.sound ⟨FullOddKasparovHomotopy.ofIso u⟩

instance instZero : Zero (OddKK.{uΓ, uA, uB, uE} α β) := ⟨mk (BundledOddKasparovCycle.zero α β)⟩
instance instAdd : Add (OddKK.{uΓ, uA, uB, uE} α β) where
  add := Quotient.lift₂ (fun c d => mk (c.directSum d)) (by
    intro c d k l h h'
    obtain ⟨h⟩ := h
    obtain ⟨h'⟩ := h'
    exact Quotient.sound ⟨h.directSum h'⟩)
instance instNeg : Neg (OddKK.{uΓ, uA, uB, uE} α β) where
  neg := Quotient.lift (fun c => mk c.opposite) (by
    intro c d h
    obtain ⟨h⟩ := h
    exact Quotient.sound ⟨h.opposite⟩)

@[simp] theorem mk_directSum (c d : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    mk (c.directSum d) = mk c + mk d := rfl
@[simp] theorem mk_opposite (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    mk c.opposite = -mk c := rfl

instance instAddCommGroup : AddCommGroup (OddKK.{uΓ, uA, uB, uE} α β) where
  add_assoc x y z := by
    refine Quotient.inductionOn₃' x y z ?_
    intro c d k
    exact mk_eq_of_iso (BundledOddKasparovCycle.directSumAssocIso c d k)
  zero_add x := by
    refine Quotient.inductionOn' x ?_
    intro c
    exact mk_eq_of_iso (BundledOddKasparovCycle.directSumZeroLeftIso c)
  add_zero x := by
    refine Quotient.inductionOn' x ?_
    intro c
    exact mk_eq_of_iso (BundledOddKasparovCycle.directSumZeroRightIso c)
  add_comm x y := by
    refine Quotient.inductionOn₂' x y ?_
    intro c d
    exact mk_eq_of_iso (BundledOddKasparovCycle.directSumCommIso c d)
  neg_add_cancel x := by
    refine Quotient.inductionOn' x ?_
    intro c
    exact Quotient.sound ⟨FullOddKasparovHomotopy.inverseLaw c⟩
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Exact degeneracy vanishes through the actual cone full homotopy. -/
theorem mk_eq_zero_of_degenerate (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β)
    (hc : c.cycle.IsDegenerate) : mk c = (0 : OddKK.{uΓ, uA, uB, uE} α β) :=
  Quotient.sound ⟨(FullOddKasparovHomotopy.degenerateCone c hc).symm⟩

end OddKK
end BC4lean.KKTheory
