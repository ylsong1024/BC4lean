import BC4lean.OddKasparovOperatorHomotopy
import BC4lean.KasparovInverseRotation

/-! # The genuine odd inverse rotation

The opposite odd cycle reverses its Fredholm operator. On its direct sum
with the original, the signed diagonal operator anticommutes with the
actual selfadjoint summand flip. The trigonometric path retains all four
actual compact defects and ends at an exactly degenerate flip cycle.
-/

noncomputable section
namespace BC4lean.KKTheory
open unitInterval
variable {Γ A B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace OddKasparovCycle

/-- The opposite odd cycle reverses its Fredholm operator. -/
def opposite (c : OddKasparovCycle α β E) : OddKasparovCycle α β E where
  countablyGenerated := c.countablyGenerated
  groupAction := c.groupAction
  representation := c.representation
  representation_equivariant := c.representation_equivariant
  operator := -c.operator
  selfadjoint_mod_compact a := by
    simpa only [star_neg, sub_mul, neg_mul, neg_sub_neg, neg_sub] using
      (c.selfadjoint_mod_compact a).neg
  square_mod_compact a := by
    simpa only [neg_mul_neg] using c.square_mod_compact a
  commutator_compact a := by
    simpa only [neg_mul, mul_neg, neg_sub_neg, neg_sub] using (c.commutator_compact a).neg
  equivariance_mod_compact g a := by
    simpa only [EquivariantHilbertModule.conjugateOperator_neg, sub_mul, neg_mul,
      neg_sub_neg, neg_sub] using (c.equivariance_mod_compact g a).neg

@[simp] theorem opposite_operator (c : OddKasparovCycle α β E) : c.opposite.operator = -c.operator := rfl
@[simp] theorem opposite_representation (c : OddKasparovCycle α β E) :
    c.opposite.representation = c.representation := rfl
@[simp] theorem opposite_groupAction (c : OddKasparovCycle α β E) :
    c.opposite.groupAction = c.groupAction := rfl

/-- The selfadjoint unitary flip satisfies all operator conditions on c plus its opposite. -/
theorem oppositeSum_flip_conditions (c : OddKasparovCycle α β E) :
    (c.directSum c.opposite).OperatorConditions sumFlip where
  selfadjoint_mod_compact a := by
    rw [sumFlip_star, sub_self, zero_mul]
    exact IsModuleCompact.zero
  square_mod_compact a := by
    rw [sumFlip_square, sub_self, zero_mul]
    exact IsModuleCompact.zero
  commutator_compact a := by
    change IsModuleCompact (sumFlip * sumMap (c.representation a) (c.representation a) -
      sumMap (c.representation a) (c.representation a) * sumFlip)
    rw [sumFlip_commutes_diagonal, sub_self]
    exact IsModuleCompact.zero
  equivariance_mod_compact g a := by
    change IsModuleCompact (((c.groupAction.sum c.groupAction).conjugateOperator g sumFlip - sumFlip) *
      sumMap (c.representation a) (c.representation a))
    rw [sumFlip_conjugate_diagonal, sub_self, zero_mul]
    exact IsModuleCompact.zero

/-- The terminal flip cycle on c plus its opposite is exactly degenerate. -/
def oppositeSum_flipCycle (c : OddKasparovCycle α β E) :
    OddKasparovCycle α β (HilbertModuleSum B E E) :=
  (c.directSum c.opposite).withOperator sumFlip c.oppositeSum_flip_conditions

theorem oppositeSum_flipCycle_isDegenerate (c : OddKasparovCycle α β E) :
    c.oppositeSum_flipCycle.IsDegenerate := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    change (sumFlip - star sumFlip) * sumMap (c.representation a) (c.representation a) = 0
    rw [sumFlip_star, sub_self, zero_mul]
  · intro a
    change (sumFlip * sumFlip - 1) * sumMap (c.representation a) (c.representation a) = 0
    rw [sumFlip_square, sub_self, zero_mul]
  · intro a
    change sumFlip * sumMap (c.representation a) (c.representation a) -
      sumMap (c.representation a) (c.representation a) * sumFlip = 0
    rw [sumFlip_commutes_diagonal, sub_self]
  · intro g a
    change ((c.groupAction.sum c.groupAction).conjugateOperator g sumFlip - sumFlip) *
      sumMap (c.representation a) (c.representation a) = 0
    rw [sumFlip_conjugate_diagonal, sub_self, zero_mul]

/-- Every point of the trigonometric rotation satisfies the exact raw cycle requirements. -/
theorem oppositeSum_rotation_conditions (c : OddKasparovCycle α β E) (t : ℝ) :
    (c.directSum c.opposite).OperatorConditions
      (rotationOperator (c.directSum c.opposite).operator sumFlip t) where
  selfadjoint_mod_compact a := by
    rw [rotationOperator_selfadjoint_defect _ _ _ sumFlip_star]
    exact ((c.directSum c.opposite).selfadjoint_mod_compact a).smul (rotationCos t)
  square_mod_compact a := by
    have hanti : (c.directSum c.opposite).operator * sumFlip +
        sumFlip * (c.directSum c.opposite).operator = 0 :=
      sumFlip_anticommutes_signed_diagonal c.operator
    rw [rotationOperator_square_defect _ _ sumFlip_square hanti, smul_mul_assoc]
    exact ((c.directSum c.opposite).square_mod_compact a).smul (rotationCos t * rotationCos t)
  commutator_compact a := by
    have hcomm : sumFlip * (c.directSum c.opposite).representation a =
        (c.directSum c.opposite).representation a * sumFlip :=
      sumFlip_commutes_diagonal (c.representation a)
    rw [rotationOperator_commutator _ _ _ hcomm]
    exact ((c.directSum c.opposite).commutator_compact a).smul (rotationCos t)
  equivariance_mod_compact g a := by
    have hZ : (c.directSum c.opposite).groupAction.conjugateOperator g sumFlip = sumFlip :=
      sumFlip_conjugate_diagonal c.groupAction g
    rw [rotationOperator_equivariance_defect _ _ _ _ _ hZ]
    exact ((c.directSum c.opposite).equivariance_mod_compact g a).smul (rotationCos t)

end OddKasparovCycle

namespace OddKasparovOperatorHomotopy

/-- The actual norm-continuous inverse rotation, from c plus its opposite to the flip. -/
def inverseRotation (c : OddKasparovCycle α β E) :
    OddKasparovOperatorHomotopy (c.directSum c.opposite) (c.directSum c.opposite).operator sumFlip where
  path :=
    { toFun := fun t => rotationOperator (c.directSum c.opposite).operator sumFlip (t : ℝ)
      continuous_toFun := (continuous_rotationOperator _ _).comp continuous_subtype_val
      source' := by simp
      target' := by simp }
  conditions t := c.oppositeSum_rotation_conditions (t : ℝ)

@[simp] theorem inverseRotation_path_apply (c : OddKasparovCycle α β E) (t : I) :
    (inverseRotation c).path t =
      rotationCos (t : ℝ) • (c.directSum c.opposite).operator +
        rotationSin (t : ℝ) • sumFlip := rfl

theorem inverseRotation_target_isDegenerate (c : OddKasparovCycle α β E) :
    ((inverseRotation c).cycleAt 1).IsDegenerate := by
  simpa only [target_cycleAt, OddKasparovCycle.oppositeSum_flipCycle] using c.oppositeSum_flipCycle_isDegenerate

end OddKasparovOperatorHomotopy
end BC4lean.KKTheory
