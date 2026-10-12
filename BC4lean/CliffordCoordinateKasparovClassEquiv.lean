import BC4lean.CliffordParityDirectSum
import BC4lean.GradedKasparovSourcePullbackClass

/-! # The actual coordinate Clifford quotient and ordinary odd KK

The generic graded quotient and the proved coordinate Clifford quotient
use the same raw cycles and the same single-full-witness relation.
Identity on raw cycles and the true raw direct-sum formula give the
additive equivalence, followed by the genuine odd parity equivalence.
-/

noncomputable section
universe u
namespace BC4lean.KKTheory.CliffordCoordinateKasparovClassEquiv

variable {Γ A B : Type u} [Group Γ] [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

def equivalence :
    GradedKasparovHomotopyClass.{u,u,u,u} α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading ≃ CliffordKK.{u,u,u,u} α β where
  toFun := Quotient.map id (fun _ _ h => h)
  invFun := Quotient.map id (fun _ _ h => h)
  left_inv x := by refine Quotient.inductionOn x ?_; intro c; rfl
  right_inv x := by refine Quotient.inductionOn x ?_; intro c; rfl

def addEquivalence :
    GradedKasparovHomotopyClass.{u,u,u,u} α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading ≃+ CliffordKK.{u,u,u,u} α β where
  toEquiv := equivalence
  map_add' x y := by
    refine Quotient.inductionOn₂ x y ?_
    intro c d
    exact CliffordKK.mk_directSum c d

def oddAddEquivalence :
    GradedKasparovHomotopyClass.{u,u,u,u} α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading ≃+ OddKK.{u,u,u,u} α β :=
  addEquivalence.trans cliffordParityAddEquiv.symm

def coordinateClass (x : OddKK.{u,u,u,u} α β) := oddAddEquivalence.symm x
def oddClass (x : GradedKasparovHomotopyClass.{u,u,u,u} α (cliffordCoefficientAction β)
    CStarGrading.trivial cliffordCoefficientGrading) := oddAddEquivalence x

@[simp] theorem coordinateClass_oddClass
    (x : GradedKasparovHomotopyClass.{u,u,u,u} α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading) :
    coordinateClass (oddClass x) = x := oddAddEquivalence.symm_apply_apply x

@[simp] theorem oddClass_coordinateClass (x : OddKK.{u,u,u,u} α β) :
    oddClass (coordinateClass x) = x := oddAddEquivalence.apply_symm_apply x

theorem coordinateClass_injective : Function.Injective (coordinateClass (α := α) (β := β)) :=
  oddAddEquivalence.symm.injective

@[simp] theorem coordinateClass_add (x y : OddKK.{u,u,u,u} α β) :
    coordinateClass (x + y) = coordinateClass x + coordinateClass y :=
  map_add oddAddEquivalence.symm x y

@[simp] theorem oddClass_add
    (x y : GradedKasparovHomotopyClass.{u,u,u,u} α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading) :
    oddClass (x + y) = oddClass x + oddClass y := map_add oddAddEquivalence x y

@[simp] theorem coordinateClass_mk (c : BundledOddKasparovCycle.{u,u,u,u} α β) :
    coordinateClass (OddKK.mk c) = GradedKasparovHomotopyClass.mk c.cliffordExpansion := rfl

@[simp] theorem oddClass_mk
    (c : BundledGradedKasparovCycle.{u,u,u,u} α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading) :
    oddClass (GradedKasparovHomotopyClass.mk c) = OddKK.mk c.cliffordExtraction := rfl

end BC4lean.KKTheory.CliffordCoordinateKasparovClassEquiv
