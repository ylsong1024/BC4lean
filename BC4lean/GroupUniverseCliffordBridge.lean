import BC4lean.CliffordTensorParityGroup
import BC4lean.CliffordTensorSeparable
import BC4lean.GradedKasparovSourcePullbackClass

/-! # The genuine Clifford quotient bridge with independent universes

The generic graded quotient and the existing actual Clifford tensor quotient
have identical raw carriers and identical single-full-interval-witness
relations. Their identity map therefore supplies the bridge for independent
group, source, coefficient and module universes. In particular PUnit and ℂ
remain in universe zero while the coefficient B may live in a larger one;
no source or coefficient algebra is silently replaced by a universe lift.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory.GroupUniverseCliffordBridge

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

def equivalence :
    GradedKasparovHomotopyClass.{uΓ, uA, uB, uE} α (cliffordTensorAction β)
      CStarGrading.trivial cliffordTensorGrading ≃ CliffordTensorKK.{uΓ, uA, uB, uE} α β where
  toFun := Quotient.map id (fun _ _ h => h)
  invFun := Quotient.map id (fun _ _ h => h)
  left_inv x := by refine Quotient.inductionOn x ?_; intro c; rfl
  right_inv x := by refine Quotient.inductionOn x ?_; intro c; rfl

def addEquivalence :
    GradedKasparovHomotopyClass.{uΓ, uA, uB, uE} α (cliffordTensorAction β)
      CStarGrading.trivial cliffordTensorGrading ≃+ CliffordTensorKK.{uΓ, uA, uB, uE} α β where
  toEquiv := equivalence
  map_add' x y := by
    refine Quotient.inductionOn₂ x y ?_
    intro c d
    change CliffordTensorKK.mk (c.directSum d) = CliffordTensorKK.mk c + CliffordTensorKK.mk d
    exact CliffordTensorKK.mk_directSum c d

def oddAddEquivalence :
    GradedKasparovHomotopyClass.{uΓ, uA, uB, uE} α (cliffordTensorAction β)
      CStarGrading.trivial cliffordTensorGrading ≃+ OddKK.{uΓ, uA, uB, uE} α β :=
  addEquivalence.trans cliffordTensorParityAddEquiv.symm

def gradedOddClass (x : OddKK.{uΓ, uA, uB, uE} α β) :
    GradedKasparovHomotopyClass.{uΓ, uA, uB, uE} α (cliffordTensorAction β)
      CStarGrading.trivial cliffordTensorGrading := oddAddEquivalence.symm x

def oddClass (x : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE} α (cliffordTensorAction β)
    CStarGrading.trivial cliffordTensorGrading) : OddKK.{uΓ, uA, uB, uE} α β :=
  oddAddEquivalence x

@[simp] theorem gradedOddClass_oddClass
    (x : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE} α (cliffordTensorAction β)
      CStarGrading.trivial cliffordTensorGrading) : gradedOddClass (oddClass x) = x :=
  oddAddEquivalence.symm_apply_apply x

@[simp] theorem oddClass_gradedOddClass (x : OddKK.{uΓ, uA, uB, uE} α β) :
    oddClass (gradedOddClass x) = x := oddAddEquivalence.apply_symm_apply x

theorem gradedOddClass_injective : Function.Injective
    (gradedOddClass (α := α) (β := β)) := oddAddEquivalence.symm.injective

@[simp] theorem gradedOddClass_add (x y : OddKK.{uΓ, uA, uB, uE} α β) :
    gradedOddClass (x + y) = gradedOddClass x + gradedOddClass y :=
  map_add oddAddEquivalence.symm x y

end BC4lean.KKTheory.GroupUniverseCliffordBridge
