import BC4lean.CliffordParityQuotient
import BC4lean.OddKasparovHomotopyGroup
import Mathlib.Algebra.Group.TransferInstance

/-! # The genuine Clifford quotient group and odd parity group equivalence

The Clifford classes are quotiented by actual full graded interval witnesses.
The proved full-homotopy parity equivalence transports the actual odd group,
whose sum and inverse laws use direct-sum witnesses, inverse rotation and the
degenerate cone. Thus the group structure does not assume any inverse law or
equivalence of homotopy relations.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

/-- The actual Clifford full-homotopy quotient inherits the proved odd
additive operations through the actual full parity equivalence. -/
instance cliffordKKAddCommGroup : AddCommGroup (CliffordKK.{uΓ, uA, uB, uE} α β) :=
  (cliffordParityEquiv (α := α) (β := β)).symm.addCommGroup

/-- Odd KK and its genuine one-Clifford graded quotient are isomorphic
abelian groups, with the plus-generator convention fixed throughout. -/
def cliffordParityAddEquiv : OddKK.{uΓ, uA, uB, uE} α β ≃+ CliffordKK.{uΓ, uA, uB, uE} α β :=
  ((cliffordParityEquiv (α := α) (β := β)).symm.addEquiv).symm

@[simp] theorem cliffordParityAddEquiv_apply (x : OddKK.{uΓ, uA, uB, uE} α β) :
    cliffordParityAddEquiv x = cliffordParityEquiv x := rfl

end BC4lean.KKTheory
