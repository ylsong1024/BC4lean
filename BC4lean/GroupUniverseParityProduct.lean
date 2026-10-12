import BC4lean.GroupUniverseProduct
import BC4lean.GroupUniverseEvenBridge
import BC4lean.GroupUniverseCliffordBridge

/-! # Actual even and even-by-odd products with independent universes

The separately proved even and Clifford full-witness bridges route the
genuine graded product to the chapter's existing parity groups. Group,
source and coefficient universes remain independent, and the resulting
module universe is the actual maximum of the two input module universes.
The parity laws therefore apply with PUnit and ℂ at universe zero and
coefficients in an arbitrary universe, without changing those algebras.
-/

noncomputable section
universe uΓ uA uB uC uD uE uF uG
namespace BC4lean.KKTheory.GroupUniverseParityProduct

section Pairs
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} [Group Γ]
  [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C] [Countable Γ]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

def evenProduct (x : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β)
    (y : KasparovHomotopyClass.{uΓ, uB, uC, uF} β γ) :
    KasparovHomotopyClass.{uΓ, uA, uC, max uE uF} α γ :=
  GroupUniverseEvenBridge.evenClass (GroupUniverseProduct.product
    (GroupUniverseEvenBridge.gradedClass x) (GroupUniverseEvenBridge.gradedClass y))

@[simp] theorem gradedClass_evenProduct
    (x : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β)
    (y : KasparovHomotopyClass.{uΓ, uB, uC, uF} β γ) :
    GroupUniverseEvenBridge.gradedClass (evenProduct x y) = GroupUniverseProduct.product
      (GroupUniverseEvenBridge.gradedClass x) (GroupUniverseEvenBridge.gradedClass y) :=
  GroupUniverseEvenBridge.gradedClass_evenClass _

theorem evenProduct_add_first (x x' : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β)
    (y : KasparovHomotopyClass.{uΓ, uB, uC, uF} β γ) :
    evenProduct (x + x') y = evenProduct x y + evenProduct x' y := by
  apply GroupUniverseEvenBridge.gradedClass_injective
  simp only [gradedClass_evenProduct, GroupUniverseEvenBridge.gradedClass_add]
  exact GroupUniverseProduct.add_product _ _ _

theorem evenProduct_add_second (x : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β)
    (y y' : KasparovHomotopyClass.{uΓ, uB, uC, uF} β γ) :
    evenProduct x (y + y') = evenProduct x y + evenProduct x y' := by
  apply GroupUniverseEvenBridge.gradedClass_injective
  simp only [gradedClass_evenProduct, GroupUniverseEvenBridge.gradedClass_add]
  exact GroupUniverseProduct.product_add _ _ _

def evenOddProduct (x : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β)
    (y : OddKK.{uΓ, uB, uC, uF} β γ) : OddKK.{uΓ, uA, uC, max uE uF} α γ :=
  GroupUniverseCliffordBridge.oddClass (GroupUniverseProduct.product
    (GroupUniverseEvenBridge.gradedClass x) (GroupUniverseCliffordBridge.gradedOddClass y))

@[simp] theorem gradedOddClass_evenOddProduct
    (x : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β) (y : OddKK.{uΓ, uB, uC, uF} β γ) :
    GroupUniverseCliffordBridge.gradedOddClass (evenOddProduct x y) =
      GroupUniverseProduct.product (GroupUniverseEvenBridge.gradedClass x)
        (GroupUniverseCliffordBridge.gradedOddClass y) :=
  GroupUniverseCliffordBridge.gradedOddClass_oddClass _

theorem evenOddProduct_add_first
    (x x' : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β) (y : OddKK.{uΓ, uB, uC, uF} β γ) :
    evenOddProduct (x + x') y = evenOddProduct x y + evenOddProduct x' y := by
  apply GroupUniverseCliffordBridge.gradedOddClass_injective
  simp only [gradedOddClass_evenOddProduct, GroupUniverseCliffordBridge.gradedOddClass_add,
    GroupUniverseEvenBridge.gradedClass_add]
  exact GroupUniverseProduct.add_product _ _ _

theorem evenOddProduct_add_second
    (x : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β) (y y' : OddKK.{uΓ, uB, uC, uF} β γ) :
    evenOddProduct x (y + y') = evenOddProduct x y + evenOddProduct x y' := by
  apply GroupUniverseCliffordBridge.gradedOddClass_injective
  simp only [gradedOddClass_evenOddProduct, GroupUniverseCliffordBridge.gradedOddClass_add]
  exact GroupUniverseProduct.product_add _ _ _

end Pairs

section Triples
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} [Group Γ]
  [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C] [TopologicalSpace.SeparableSpace D] [Countable Γ]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C} {η : CStarAlgebraAction Γ D}

theorem evenProduct_assoc (x : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β)
    (y : KasparovHomotopyClass.{uΓ, uB, uC, uF} β γ)
    (z : KasparovHomotopyClass.{uΓ, uC, uD, uG} γ η) :
    evenProduct (evenProduct x y) z = evenProduct x (evenProduct y z) := by
  apply GroupUniverseEvenBridge.gradedClass_injective
  simp only [gradedClass_evenProduct]
  exact GroupUniverseProduct.product_assoc _ _ _

theorem evenEvenOddProduct_assoc (x : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β)
    (y : KasparovHomotopyClass.{uΓ, uB, uC, uF} β γ) (z : OddKK.{uΓ, uC, uD, uG} γ η) :
    evenOddProduct (evenProduct x y) z = evenOddProduct x (evenOddProduct y z) := by
  apply GroupUniverseCliffordBridge.gradedOddClass_injective
  simp only [gradedOddClass_evenOddProduct, gradedClass_evenProduct]
  exact GroupUniverseProduct.product_assoc _ _ _

end Triples

section Identity
variable {Γ : Type uΓ} {B : Type uB} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]

def evenIdentity (β : CStarAlgebraAction Γ B) :
    KasparovHomotopyClass.{uΓ, uB, uB, uB} β β :=
  GroupUniverseEvenBridge.evenClass
    (GroupUniverseProduct.identity β CStarGrading.trivial β.preservesGrading_trivial)

@[simp] theorem gradedClass_evenIdentity (β : CStarAlgebraAction Γ B) :
    GroupUniverseEvenBridge.gradedClass (evenIdentity β) =
      GroupUniverseProduct.identity β CStarGrading.trivial β.preservesGrading_trivial :=
  GroupUniverseEvenBridge.gradedClass_evenClass _

end Identity

section Units
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B] [Countable Γ]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

theorem evenProduct_right_identity (x : KasparovHomotopyClass.{uΓ, uA, uB, max uB uE} α β) :
    evenProduct x (evenIdentity β) = x := by
  apply GroupUniverseEvenBridge.gradedClass_injective
  rw [gradedClass_evenProduct, gradedClass_evenIdentity]
  exact GroupUniverseProduct.product_right_identity β.preservesGrading_trivial _

theorem evenProduct_left_identity [PartialOrder A] [StarOrderedRing A]
    (x : KasparovHomotopyClass.{uΓ, uA, uB, max uA uE} α β) :
    evenProduct (evenIdentity α) x = x := by
  apply GroupUniverseEvenBridge.gradedClass_injective
  rw [gradedClass_evenProduct, gradedClass_evenIdentity]
  exact GroupUniverseProduct.product_left_identity α.preservesGrading_trivial _

theorem evenOddProduct_left_identity [PartialOrder A] [StarOrderedRing A]
    (y : OddKK.{uΓ, uA, uB, max uA uE} α β) :
    evenOddProduct (evenIdentity α) y = y := by
  apply GroupUniverseCliffordBridge.gradedOddClass_injective
  rw [gradedOddClass_evenOddProduct, gradedClass_evenIdentity]
  exact GroupUniverseProduct.product_left_identity α.preservesGrading_trivial _

end Units
end BC4lean.KKTheory.GroupUniverseParityProduct
