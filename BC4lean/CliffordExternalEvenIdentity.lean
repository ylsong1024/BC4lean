import BC4lean.CliffordExternalEvenQuotient
import BC4lean.EvenKasparovProduct
import BC4lean.OddEvenKasparovProduct

/-! # The actual external Clifford extension of the even identity

The standard product-coefficient module is unitarily its two opposite
coordinate modules. The original identity grading has actual projections
1 and 0, so the Koszul half representation is exactly first-coordinate
left multiplication. This whole-cycle unitary proves the odd-by-even
right identity law on the established full homotopy groups.
-/

noncomputable section
universe u
namespace BC4lean.KKTheory
open scoped InnerProductSpace

section Standard
variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def cliffordPairStandardEquiv :
    HilbertModuleEquiv (B × B) (B × B)ᵐᵒᵖ (CliffordPairModule B Bᵐᵒᵖ) where
  linearIsometryEquiv :=
    { toFun x := cliffordPairMk (MulOpposite.op (MulOpposite.unop x).1)
        (MulOpposite.op (MulOpposite.unop x).2)
      invFun x := MulOpposite.op (MulOpposite.unop x.1, MulOpposite.unop x.2)
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      norm_map' _ := rfl }
  inner_map _ _ := rfl

namespace CliffordExternalEvenCycle
open CliffordExternalEvenRepresentation
variable {Γ : Type*} [Group Γ] [TopologicalSpace.SeparableSpace B]

theorem half_standard_identity (β : CStarAlgebraAction Γ B) (b : B × B) :
    half (gradedStandardIdentityCycle β CStarGrading.trivial β.preservesGrading_trivial) b =
      standardLeftMul b.1 := by
  have hJ : (gradedStandardIdentityCycle β CStarGrading.trivial β.preservesGrading_trivial).grading.toAdjointable =
      (1 : AdjointableMap B Bᵐᵒᵖ Bᵐᵒᵖ) := by ext x; rfl
  have hp : CliffordOne.plusProjection (1 : AdjointableMap B Bᵐᵒᵖ Bᵐᵒᵖ) = 1 := by
    rw [CliffordOne.plusProjection, smul_add, ← add_smul]
    norm_num
  have hm : CliffordOne.minusProjection (1 : AdjointableMap B Bᵐᵒᵖ Bᵐᵒᵖ) = 0 := by
    simp only [CliffordOne.minusProjection, sub_self, smul_zero]
  rw [half, halfRepresentation_eq, hJ, hp, hm, mul_one, mul_zero, add_zero]
  rfl

def standardIdentityIso (β : CStarAlgebraAction Γ B) :
    GradedKasparovCycleIso
      (gradedStandardIdentityCycle (cliffordCoefficientAction β) cliffordCoefficientGrading
        (cliffordCoefficientAction_preservesGrading β))
      (cycle (gradedStandardIdentityCycle β CStarGrading.trivial β.preservesGrading_trivial)) where
  moduleEquiv := cliffordPairStandardEquiv
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine b x := by
    change cliffordPairStandardEquiv (standardLeftMul b x) =
      cliffordPairMap
        (half (gradedStandardIdentityCycle β CStarGrading.trivial β.preservesGrading_trivial) b)
        (half (gradedStandardIdentityCycle β CStarGrading.trivial β.preservesGrading_trivial)
          (cliffordCoefficientGrading.automorphism b)) (cliffordPairStandardEquiv x)
    rw [half_standard_identity, half_standard_identity]
    rfl
  operator_intertwine _ := rfl

end CliffordExternalEvenCycle
end Standard

variable {Γ A B : Type u} [Group Γ] [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

theorem cliffordExternalEvenClass_identity (β : CStarAlgebraAction Γ B) :
    cliffordExternalEvenClass (KasparovHomotopyClass.identity β) =
      GradedKasparovHomotopyClass.identity (cliffordCoefficientAction β) cliffordCoefficientGrading
        (cliffordCoefficientAction_preservesGrading β) := by
  change GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
    (CliffordExternalEvenCycle.cycle (GradedKasparovCycle.ofKasparovCycle
      ((gradedStandardIdentityCycle β CStarGrading.trivial
        β.preservesGrading_trivial).toKasparovCycle)))) = _
  rw [GradedKasparovCycle.ofKasparovCycle_toKasparovCycle]
  exact GradedKasparovHomotopyClass.mk_eq_of_iso (CliffordExternalEvenCycle.standardIdentityIso β).symm

variable [TopologicalSpace.SeparableSpace A] [Countable Γ]

theorem OddKK.productEven_right_identity (x : OddKK.{u,u,u,u} α β) :
    OddKK.productEven x (KasparovHomotopyClass.identity β) = x := by
  apply CliffordCoordinateKasparovClassEquiv.coordinateClass_injective
  rw [OddKK.coordinateClass_productEven, cliffordExternalEvenClass_identity]
  exact GradedKasparovHomotopyClass.product_right_identity
    (cliffordCoefficientAction_preservesGrading β) _

end BC4lean.KKTheory
