import BC4lean.GradedMatrixMoritaEvenBase
import BC4lean.GradedKasparovSourcePullbackClass

/-! # The actual even group and the full graded quotient

For the two trivial algebra gradings the raw conversions preserve all
module and cycle data. Their actual interval-module conversions preserve
single full witnesses in both directions. They therefore identify the
graded quotient with the chapter's existing even homotopy-class group.
The sum law uses the actual identity-on-vectors direct-sum unitary.
-/

noncomputable section
universe u
namespace BC4lean.KKTheory.EvenGradedKasparovClassEquiv

variable {Γ A B : Type u} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

open GradedMatrixMoritaEvenBase

/-- The genuine full trivial-grading quotient is exactly the existing
even group quotient, using both actual whole-interval conversions. -/
def equivalence :
    GradedKasparovHomotopyClass.{u,u,u,u} α β CStarGrading.trivial CStarGrading.trivial ≃
      KasparovHomotopyClass.{u,u,u,u} α β where
  toFun := Quotient.map toEven (fun c d h => (full_iff_homotopic c d).mp h)
  invFun := Quotient.map ofEven (by
    intro c d h
    obtain ⟨h⟩ := BundledKasparovCycle.homotopic_iff_full.mp h
    exact ⟨fullOfEven h⟩)
  left_inv x := by
    refine Quotient.inductionOn x ?_
    intro c
    change Quotient.mk _ (ofEven (toEven c)) = Quotient.mk _ c
    rw [ofEven_toEven]
  right_inv x := by
    refine Quotient.inductionOn x ?_
    intro c
    change Quotient.mk _ (toEven (ofEven c)) = Quotient.mk _ c
    rw [toEven_ofEven]

def evenDirectSumIso
    (c d : BundledGradedKasparovCycle.{u,u,u,u} α β
      CStarGrading.trivial CStarGrading.trivial) :
    (toEven (c.directSum d)).Iso ((toEven c).directSum (toEven d)) where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

/-- The actual full-quotient equivalence preserves genuine Hilbert-module
direct sums and hence the established group addition. -/
def addEquivalence :
    GradedKasparovHomotopyClass.{u,u,u,u} α β CStarGrading.trivial CStarGrading.trivial ≃+
      KasparovHomotopyClass.{u,u,u,u} α β where
  toEquiv := equivalence
  map_add' x y := by
    refine Quotient.inductionOn₂ x y ?_
    intro c d
    change KasparovHomotopyClass.mk (toEven (c.directSum d)) =
      KasparovHomotopyClass.mk (toEven c) + KasparovHomotopyClass.mk (toEven d)
    rw [← KasparovHomotopyClass.mk_directSum]
    exact KasparovHomotopyClass.mk_eq_of_iso (evenDirectSumIso c d)

def gradedClass
    (x : KasparovHomotopyClass.{u,u,u,u} α β) :
    GradedKasparovHomotopyClass.{u,u,u,u} α β CStarGrading.trivial CStarGrading.trivial :=
  addEquivalence.symm x

def evenClass
    (x : GradedKasparovHomotopyClass.{u,u,u,u} α β CStarGrading.trivial CStarGrading.trivial) :
    KasparovHomotopyClass.{u,u,u,u} α β := addEquivalence x

@[simp] theorem gradedClass_mk (c : BundledKasparovCycle.{u,u,u,u} α β) :
    gradedClass (KasparovHomotopyClass.mk c) = GradedKasparovHomotopyClass.mk (ofEven c) := rfl

@[simp] theorem evenClass_mk (c : BundledGradedKasparovCycle.{u,u,u,u} α β
    CStarGrading.trivial CStarGrading.trivial) :
    evenClass (GradedKasparovHomotopyClass.mk c) = KasparovHomotopyClass.mk (toEven c) := rfl

@[simp] theorem evenClass_gradedClass (x : KasparovHomotopyClass.{u,u,u,u} α β) :
    evenClass (gradedClass x) = x := addEquivalence.apply_symm_apply x

@[simp] theorem gradedClass_evenClass
    (x : GradedKasparovHomotopyClass.{u,u,u,u} α β CStarGrading.trivial CStarGrading.trivial) :
    gradedClass (evenClass x) = x := addEquivalence.symm_apply_apply x

theorem gradedClass_injective : Function.Injective
    (gradedClass (α := α) (β := β)) := addEquivalence.symm.injective

@[simp] theorem gradedClass_add (x y : KasparovHomotopyClass.{u,u,u,u} α β) :
    gradedClass (x + y) = gradedClass x + gradedClass y := map_add addEquivalence.symm x y

@[simp] theorem evenClass_add
    (x y : GradedKasparovHomotopyClass.{u,u,u,u} α β CStarGrading.trivial CStarGrading.trivial) :
    evenClass (x + y) = evenClass x + evenClass y := map_add addEquivalence x y

end BC4lean.KKTheory.EvenGradedKasparovClassEquiv
