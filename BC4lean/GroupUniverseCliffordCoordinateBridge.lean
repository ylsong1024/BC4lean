import BC4lean.GroupUniverseCliffordBridge

/-! # The actual coordinate Clifford quotient with independent universes

This identity-on-whole-cycle quotient bridge uses exactly the same
single full graded interval witness relation. The proved coordinate
parity equivalence then identifies it with the genuine odd full quotient.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory.GroupUniverseCliffordCoordinateBridge
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

def equivalence : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE}
    α (cliffordCoefficientAction β) CStarGrading.trivial cliffordCoefficientGrading ≃
    CliffordKK.{uΓ, uA, uB, uE} α β where
  toFun := Quotient.map id (fun _ _ h => h)
  invFun := Quotient.map id (fun _ _ h => h)
  left_inv x := by refine Quotient.inductionOn x ?_; intro c; rfl
  right_inv x := by refine Quotient.inductionOn x ?_; intro c; rfl

def addEquivalence : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE}
    α (cliffordCoefficientAction β) CStarGrading.trivial cliffordCoefficientGrading ≃+
    CliffordKK.{uΓ, uA, uB, uE} α β where
  toEquiv := equivalence
  map_add' x y := by
    refine Quotient.inductionOn₂ x y ?_
    intro c d
    exact CliffordKK.mk_directSum c d

def oddAddEquivalence : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE}
    α (cliffordCoefficientAction β) CStarGrading.trivial cliffordCoefficientGrading ≃+
    OddKK.{uΓ, uA, uB, uE} α β :=
  addEquivalence.trans cliffordParityAddEquiv.symm

def gradedOddClass (x : OddKK.{uΓ, uA, uB, uE} α β) := oddAddEquivalence.symm x
def oddClass (x : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE}
    α (cliffordCoefficientAction β) CStarGrading.trivial cliffordCoefficientGrading) :=
  oddAddEquivalence x

@[simp] theorem gradedOddClass_oddClass
    (x : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE}
      α (cliffordCoefficientAction β) CStarGrading.trivial cliffordCoefficientGrading) :
    gradedOddClass (oddClass x) = x := oddAddEquivalence.symm_apply_apply x

@[simp] theorem oddClass_gradedOddClass (x : OddKK.{uΓ, uA, uB, uE} α β) :
    oddClass (gradedOddClass x) = x := oddAddEquivalence.apply_symm_apply x

theorem gradedOddClass_injective : Function.Injective
    (gradedOddClass (α := α) (β := β)) := oddAddEquivalence.symm.injective

@[simp] theorem gradedOddClass_add (x y : OddKK.{uΓ, uA, uB, uE} α β) :
    gradedOddClass (x + y) = gradedOddClass x + gradedOddClass y :=
  map_add oddAddEquivalence.symm x y

@[simp] theorem oddClass_add
    (x y : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE}
      α (cliffordCoefficientAction β) CStarGrading.trivial cliffordCoefficientGrading) :
    oddClass (x + y) = oddClass x + oddClass y := map_add oddAddEquivalence x y

@[simp] theorem gradedOddClass_mk (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    gradedOddClass (OddKK.mk c) = GradedKasparovHomotopyClass.mk c.cliffordExpansion := rfl

end BC4lean.KKTheory.GroupUniverseCliffordCoordinateBridge
