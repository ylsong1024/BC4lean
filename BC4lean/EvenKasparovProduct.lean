import BC4lean.EvenGradedKasparovClassEquiv
import BC4lean.GradedKasparovProductAssociativityClass
import BC4lean.GradedKasparovProductSecondAdditivity

/-! # The genuine product on the chapter's existing even groups

The actual full graded quotient for trivial algebra gradings is identified
with the established even group by the genuine whole-interval conversion.
The constructed product descends along that explicit additive equivalence.
Both additivity laws, both identity laws and associativity therefore retain
the actual even group and its original full-homotopy meaning.
-/

noncomputable section
universe u
namespace BC4lean.KKTheory.KasparovHomotopyClass

variable {Γ A B C D : Type u} [Group Γ]
  [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C] [TopologicalSpace.SeparableSpace D] [Countable Γ]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C} {η : CStarAlgebraAction Γ D}

open EvenGradedKasparovClassEquiv

/-- The actual Kasparov product on the existing even full-homotopy groups. -/
def product (x : KasparovHomotopyClass.{u,u,u,u} α β)
    (y : KasparovHomotopyClass.{u,u,u,u} β γ) :
    KasparovHomotopyClass.{u,u,u,u} α γ :=
  evenClass (GradedKasparovHomotopyClass.product (gradedClass x) (gradedClass y))

@[simp] theorem gradedClass_product
    (x : KasparovHomotopyClass.{u,u,u,u} α β)
    (y : KasparovHomotopyClass.{u,u,u,u} β γ) :
    gradedClass (product x y) =
      GradedKasparovHomotopyClass.product (gradedClass x) (gradedClass y) :=
  gradedClass_evenClass _

/-- Products of raw even representatives use their actual interior tensor
and the previously constructed genuine product operator. -/
theorem product_mk (c : BundledKasparovCycle.{u,u,u,u} α β)
    (d : BundledKasparovCycle.{u,u,u,u} β γ) :
    product (mk c) (mk d) =
      mk (GradedMatrixMoritaEvenBase.toEven
        ((GradedMatrixMoritaEvenBase.ofEven c).product (GradedMatrixMoritaEvenBase.ofEven d))) := rfl

theorem add_product (x x' : KasparovHomotopyClass.{u,u,u,u} α β)
    (y : KasparovHomotopyClass.{u,u,u,u} β γ) :
    product (x + x') y = product x y + product x' y := by
  apply gradedClass_injective
  simp only [gradedClass_product, gradedClass_add]
  exact GradedKasparovHomotopyClass.add_product (gradedClass x) (gradedClass x') (gradedClass y)

theorem product_add (x : KasparovHomotopyClass.{u,u,u,u} α β)
    (y y' : KasparovHomotopyClass.{u,u,u,u} β γ) :
    product x (y + y') = product x y + product x y' := by
  apply gradedClass_injective
  simp only [gradedClass_product, gradedClass_add]
  exact GradedKasparovHomotopyClass.product_add (gradedClass x) (gradedClass y) (gradedClass y')

theorem product_assoc (x : KasparovHomotopyClass.{u,u,u,u} α β)
    (y : KasparovHomotopyClass.{u,u,u,u} β γ)
    (z : KasparovHomotopyClass.{u,u,u,u} γ η) :
    product (product x y) z = product x (product y z) := by
  apply gradedClass_injective
  simp only [gradedClass_product]
  exact GradedKasparovHomotopyClass.product_assoc (gradedClass x) (gradedClass y) (gradedClass z)

/-- The unit is represented by the actual compact standard B-module cycle. -/
def identity (β : CStarAlgebraAction Γ B) : KasparovHomotopyClass.{u,u,u,u} β β :=
  evenClass (GradedKasparovHomotopyClass.identity β CStarGrading.trivial β.preservesGrading_trivial)

omit [Countable Γ] in
@[simp] theorem gradedClass_identity (β : CStarAlgebraAction Γ B) :
    gradedClass (identity β) =
      GradedKasparovHomotopyClass.identity β CStarGrading.trivial β.preservesGrading_trivial :=
  gradedClass_evenClass _

theorem product_right_identity (x : KasparovHomotopyClass.{u,u,u,u} α β) :
    product x (identity β) = x := by
  apply gradedClass_injective
  rw [gradedClass_product, gradedClass_identity]
  exact GradedKasparovHomotopyClass.product_right_identity β.preservesGrading_trivial (gradedClass x)

theorem product_left_identity [PartialOrder A] [StarOrderedRing A]
    (x : KasparovHomotopyClass.{u,u,u,u} α β) : product (identity α) x = x := by
  apply gradedClass_injective
  rw [gradedClass_product, gradedClass_identity]
  exact GradedKasparovHomotopyClass.product_left_identity α.preservesGrading_trivial (gradedClass x)

theorem zero_product (y : KasparovHomotopyClass.{u,u,u,u} β γ) :
    product (0 : KasparovHomotopyClass.{u,u,u,u} α β) y = 0 := by
  have h := add_product (0 : KasparovHomotopyClass.{u,u,u,u} α β) 0 y
  rw [zero_add] at h
  have h' : product (0 : KasparovHomotopyClass.{u,u,u,u} α β) y + 0 =
      product (0 : KasparovHomotopyClass.{u,u,u,u} α β) y + product 0 y := by
    simpa only [add_zero] using h
  exact (add_left_cancel h').symm

theorem product_zero (x : KasparovHomotopyClass.{u,u,u,u} α β) :
    product x (0 : KasparovHomotopyClass.{u,u,u,u} β γ) = 0 := by
  have h := product_add x (0 : KasparovHomotopyClass.{u,u,u,u} β γ) 0
  rw [zero_add] at h
  have h' : product x (0 : KasparovHomotopyClass.{u,u,u,u} β γ) + 0 =
      product x (0 : KasparovHomotopyClass.{u,u,u,u} β γ) + product x 0 := by
    simpa only [add_zero] using h
  exact (add_left_cancel h').symm

/-- Bilinearity is packaged using the actual established abelian groups. -/
def productAddHom : KasparovHomotopyClass.{u,u,u,u} α β →+
    (KasparovHomotopyClass.{u,u,u,u} β γ →+ KasparovHomotopyClass.{u,u,u,u} α γ) where
  toFun x := {
    toFun := product x
    map_zero' := product_zero x
    map_add' := product_add x }
  map_zero' := by ext y; exact zero_product y
  map_add' x x' := by ext y; exact add_product x x' y

end BC4lean.KKTheory.KasparovHomotopyClass
