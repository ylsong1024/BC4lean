import BC4lean.KasparovInverseRotation
import BC4lean.KasparovHomotopyGroup

/-! # Rotation of two genuine cycle operators

Both endpoint operators satisfy the full cycle conditions on the same
represented graded equivariant module. Their localized anticommutator
is compact. The trigonometric rotation therefore satisfies the same
conditions at every parameter. Its whole interval witness is constructed
by the existing operator-path to interval-module construction.
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

omit [StarOrderedRing B] [CompleteSpace E] in
/-- The exact square expansion retains both endpoint defects and the
actual anticommutator term. -/
theorem rotationOperator_square_defect_general (S T : AdjointableMap B E E) (t : ℝ) :
    rotationOperator S T t * rotationOperator S T t - 1 =
      (rotationCos t * rotationCos t) • (S * S - 1) +
        (rotationSin t * rotationSin t) • (T * T - 1) +
          (rotationCos t * rotationSin t) • (S * T + T * S) := by
  have hexpand : rotationOperator S T t * rotationOperator S T t - 1 =
      (rotationCos t * rotationCos t) • (S * S) +
        (rotationSin t * rotationSin t) • (T * T) +
          (rotationCos t * rotationSin t) • (S * T + T * S) - 1 := by
    simp only [rotationOperator, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
    module
  rw [hexpand]
  have hscalar := rotationCos_sq_add_rotationSin_sq t
  calc
    _ = (rotationCos t * rotationCos t) • (S * S - 1) +
        (rotationSin t * rotationSin t) • (T * T - 1) +
          (rotationCos t * rotationSin t) • (S * T + T * S) +
            (rotationCos t * rotationCos t + rotationSin t * rotationSin t - 1) •
              (1 : AdjointableMap B E E) := by module
    _ = _ := by rw [hscalar]; simp

theorem KasparovCycle.compactAnticommutator_rotation_conditions
    (c : KasparovCycle α β E) (S T : AdjointableMap B E E)
    (hS : c.OperatorConditions S) (hT : c.OperatorConditions T)
    (hanti : ∀ a, IsModuleCompact ((S * T + T * S) * c.representation a)) (t : ℝ) :
    c.OperatorConditions (rotationOperator S T t) where
  operator_odd := (hS.operator_odd.smul (rotationCos t)).add
    (hT.operator_odd.smul (rotationSin t))
  selfadjoint_mod_compact a := by
    have hc : star (rotationCos t) = rotationCos t := by
      simp only [rotationCos, Complex.star_def, Complex.conj_ofReal]
    have hs : star (rotationSin t) = rotationSin t := by
      simp only [rotationSin, Complex.star_def, Complex.conj_ofReal]
    have heq : (rotationOperator S T t - star (rotationOperator S T t)) * c.representation a =
        rotationCos t • ((S - star S) * c.representation a) +
          rotationSin t • ((T - star T) * c.representation a) := by
      simp only [rotationOperator, star_add, star_smul, hc, hs, add_mul, sub_mul, smul_mul_assoc]
      module
    rw [heq]
    exact ((hS.selfadjoint_mod_compact a).smul (rotationCos t)).add
      ((hT.selfadjoint_mod_compact a).smul (rotationSin t))
  square_mod_compact a := by
    rw [rotationOperator_square_defect_general, add_mul, add_mul, smul_mul_assoc,
      smul_mul_assoc, smul_mul_assoc]
    exact (((hS.square_mod_compact a).smul (rotationCos t * rotationCos t)).add
      ((hT.square_mod_compact a).smul (rotationSin t * rotationSin t))).add
      ((hanti a).smul (rotationCos t * rotationSin t))
  commutator_compact a := by
    have heq : rotationOperator S T t * c.representation a -
        c.representation a * rotationOperator S T t =
      rotationCos t • (S * c.representation a - c.representation a * S) +
        rotationSin t • (T * c.representation a - c.representation a * T) := by
      simp only [rotationOperator, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
      module
    rw [heq]
    exact ((hS.commutator_compact a).smul (rotationCos t)).add
      ((hT.commutator_compact a).smul (rotationSin t))
  equivariance_mod_compact g a := by
    let L := c.groupAction.conjugateMapContinuousLinearMap c.groupAction g
    have heq : (c.groupAction.conjugateOperator g (rotationOperator S T t) -
        rotationOperator S T t) * c.representation a =
      rotationCos t • ((c.groupAction.conjugateOperator g S - S) * c.representation a) +
        rotationSin t • ((c.groupAction.conjugateOperator g T - T) * c.representation a) := by
      change (L (rotationCos t • S + rotationSin t • T) -
        (rotationCos t • S + rotationSin t • T)) * c.representation a = _
      rw [map_add, map_smul, map_smul]
      change (rotationCos t • c.groupAction.conjugateOperator g S +
        rotationSin t • c.groupAction.conjugateOperator g T -
          (rotationCos t • S + rotationSin t • T)) * c.representation a = _
      simp only [add_mul, sub_mul, smul_mul_assoc]
      module
    rw [heq]
    exact ((hS.equivariance_mod_compact g a).smul (rotationCos t)).add
      ((hT.equivariance_mod_compact g a).smul (rotationSin t))

/-- An actual operator path, whose full cycle conditions are proved above. -/
def KasparovOperatorHomotopy.compactAnticommutatorRotation
    (c : KasparovCycle α β E) (S T : AdjointableMap B E E)
    (hS : c.OperatorConditions S) (hT : c.OperatorConditions T)
    (hanti : ∀ a, IsModuleCompact ((S * T + T * S) * c.representation a)) :
    KasparovOperatorHomotopy c S T where
  path := {
    toFun := fun t => rotationOperator S T (t : ℝ)
    continuous_toFun := (continuous_rotationOperator S T).comp continuous_subtype_val
    source' := rotationOperator_zero S T
    target' := rotationOperator_one S T }
  conditions t := c.compactAnticommutator_rotation_conditions S T hS hT hanti (t : ℝ)

end BC4lean.KKTheory
