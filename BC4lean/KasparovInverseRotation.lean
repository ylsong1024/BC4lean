import BC4lean.KasparovDirectSum
import BC4lean.KasparovOperatorHomotopy
import BC4lean.EquivariantCompactOperator
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Module

/-! # Opposite cycles and the inverse rotation

Reversing both the module grading and Fredholm operator produces the opposite
raw cycle. On its direct sum with the original cycle, the diagonal operator
anticommutes with the summand flip. Their real trigonometric rotation is a
norm-continuous path of admissible Kasparov operators ending at an exactly
degenerate flip cycle. This is an actual operator homotopy, without a KK
quotient or group-law assertion.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace
open unitInterval

variable {Γ A B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

namespace GradedHilbertModule

omit [StarOrderedRing B] in
/-- Reversing the two grading subspaces preserves the coefficient grading. -/
def opposite {δ : CStarGrading B} (γ : GradedHilbertModule δ E) : GradedHilbertModule δ E where
  grading := γ.grading.trans (LinearIsometryEquiv.neg ℂ)
  involutive x := by
    change -γ.grading (-γ.grading x) = x
    rw [map_neg, grading_sq, neg_neg]
  inner_grading x y := by
    change ⟪-γ.grading x, -γ.grading y⟫_(Bᵐᵒᵖ) =
      opStarAlgEquiv δ.automorphism ⟪x, y⟫_(Bᵐᵒᵖ)
    simpa using γ.inner_grading x y

omit [StarOrderedRing B] in
@[simp] theorem opposite_grading_apply {δ : CStarGrading B} (γ : GradedHilbertModule δ E) (x : E) :
    γ.opposite.grading x = -γ.grading x := rfl

end GradedHilbertModule

/-- The summand flip as an actual adjointable module operator. -/
def sumFlip : AdjointableMap B (HilbertModuleSum B E E) (HilbertModuleSum B E E) :=
  sumInl.comp sumSnd + sumInr.comp sumFst

@[simp] theorem sumFlip_apply (x : HilbertModuleSum B E E) : sumFlip x = sumMk x.snd x.fst := by
  change (x.snd, (0 : E)) + ((0 : E), x.fst) = (x.snd, x.fst)
  simp

@[simp] theorem sumFlip_star : star (sumFlip (B := B) (E := E)) = sumFlip := by
  ext x
  change ((0 : E), x.fst) + (x.snd, (0 : E)) = (x.snd, (0 : E)) + ((0 : E), x.fst)
  simp

@[simp] theorem sumFlip_square : sumFlip (B := B) (E := E) * sumFlip = 1 := by
  ext x
  simp only [AdjointableMap.mul_apply, sumFlip_apply, sumMk_fst, sumMk_snd,
    sumMk_eta, AdjointableMap.one_apply]

theorem sumFlip_commutes_diagonal (T : AdjointableMap B E E) :
    sumFlip * sumMap T T = sumMap T T * sumFlip := by
  ext x
  simp only [AdjointableMap.mul_apply, sumFlip_apply, sumMap_apply, sumMk_fst, sumMk_snd]

theorem sumFlip_anticommutes_signed_diagonal (T : AdjointableMap B E E) :
    sumMap T (-T) * sumFlip + sumFlip * sumMap T (-T) = 0 := by
  ext x
  apply Prod.ext <;> simp [sumFlip_apply, sumMap_apply]

theorem sumFlip_odd_opposite {δ : CStarGrading B} (γ : GradedHilbertModule δ E) :
    (γ.sum γ.opposite).IsOdd (γ.sum γ.opposite) sumFlip := by
  intro x
  simp only [GradedHilbertModule.sum_grading_apply, sumFlip_apply,
    GradedHilbertModule.opposite_grading_apply, sumMk_fst, sumMk_snd]
  apply Prod.ext <;> simp

/-- The two real rotation coefficients, regarded as complex scalars. -/
def rotationCos (t : ℝ) : ℂ := (Real.cos (Real.pi * t / 2) : ℝ)
def rotationSin (t : ℝ) : ℂ := (Real.sin (Real.pi * t / 2) : ℝ)

/-- The norm-continuous real rotation of two adjointable operators. -/
def rotationOperator (M Z : AdjointableMap B E E) (t : ℝ) : AdjointableMap B E E :=
  rotationCos t • M + rotationSin t • Z

omit [StarOrderedRing B] in
theorem continuous_rotationOperator (M Z : AdjointableMap B E E) :
    Continuous (rotationOperator M Z) := by
  have hθ : Continuous (fun t : ℝ => Real.pi * t / 2) :=
    (continuous_const.mul continuous_id).div_const 2
  exact ((Complex.continuous_ofReal.comp (Real.continuous_cos.comp hθ)).smul continuous_const).add
    ((Complex.continuous_ofReal.comp (Real.continuous_sin.comp hθ)).smul continuous_const)

omit [StarOrderedRing B] in
@[simp] theorem rotationOperator_zero (M Z : AdjointableMap B E E) : rotationOperator M Z 0 = M := by
  simp [rotationOperator, rotationCos, rotationSin]

omit [StarOrderedRing B] in
@[simp] theorem rotationOperator_one (M Z : AdjointableMap B E E) : rotationOperator M Z 1 = Z := by
  simp [rotationOperator, rotationCos, rotationSin, Real.cos_pi_div_two, Real.sin_pi_div_two]

theorem rotationCos_sq_add_rotationSin_sq (t : ℝ) :
    rotationCos t * rotationCos t + rotationSin t * rotationSin t = 1 := by
  dsimp [rotationCos, rotationSin]
  norm_cast
  simpa only [pow_two] using Real.cos_sq_add_sin_sq (Real.pi * t / 2)

omit [StarOrderedRing B] in
/-- Selfadjointness defects scale by the cosine because the flip is selfadjoint. -/
theorem rotationOperator_selfadjoint_defect (M Z R : AdjointableMap B E E)
    (hZ : star Z = Z) (t : ℝ) :
    (rotationOperator M Z t - star (rotationOperator M Z t)) * R =
      rotationCos t • ((M - star M) * R) := by
  have ha : star (rotationCos t) = rotationCos t := by
    simp only [rotationCos, Complex.star_def, Complex.conj_ofReal]
  have hb : star (rotationSin t) = rotationSin t := by
    simp only [rotationSin, Complex.star_def, Complex.conj_ofReal]
  simp only [rotationOperator, star_add, star_smul, ha, hb, hZ,
    sub_mul, add_mul, smul_mul_assoc]
  module

omit [StarOrderedRing B] in
/-- The square defect scales by the cosine squared, using genuine anticommutation. -/
theorem rotationOperator_square_defect (M Z : AdjointableMap B E E)
    (hZ : Z * Z = 1) (hanti : M * Z + Z * M = 0) (t : ℝ) :
    rotationOperator M Z t * rotationOperator M Z t - 1 =
      (rotationCos t * rotationCos t) • (M * M - 1) := by
  calc
    rotationOperator M Z t * rotationOperator M Z t - 1 =
        (rotationCos t * rotationCos t) • (M * M) +
          (rotationCos t * rotationSin t) • (M * Z + Z * M) +
          (rotationSin t * rotationSin t) • (Z * Z) - 1 := by
      simp only [rotationOperator, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
      module
    _ = (rotationCos t * rotationCos t) • (M * M - 1) +
        (rotationCos t * rotationCos t + rotationSin t * rotationSin t - 1) •
          (1 : AdjointableMap B E E) := by
      rw [hZ, hanti]
      module
    _ = (rotationCos t * rotationCos t) • (M * M - 1) := by
      rw [rotationCos_sq_add_rotationSin_sq]
      simp

omit [StarOrderedRing B] in
theorem rotationOperator_commutator (M Z R : AdjointableMap B E E)
    (hcomm : Z * R = R * Z) (t : ℝ) :
    rotationOperator M Z t * R - R * rotationOperator M Z t =
      rotationCos t • (M * R - R * M) := by
  simp only [rotationOperator, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  rw [hcomm]
  module

variable [Group Γ] {β : CStarAlgebraAction Γ B}

omit [StarOrderedRing B] in
@[simp] theorem EquivariantHilbertModule.conjugateOperator_neg
    (U : EquivariantHilbertModule β E) (g : Γ) (T : AdjointableMap B E E) :
    U.conjugateOperator g (-T) = -U.conjugateOperator g T := by
  let L := U.conjugateMapContinuousLinearMap U g
  change L (-T) = -L T
  exact L.map_neg T

theorem sumFlip_conjugate_diagonal (U : EquivariantHilbertModule β E) (g : Γ) :
    (U.sum U).conjugateOperator g sumFlip = sumFlip := by
  ext x
  simp only [EquivariantHilbertModule.conjugateMap_apply,
    EquivariantHilbertModule.sum_action_apply, sumFlip_apply, sumMk_fst, sumMk_snd,
    EquivariantHilbertModule.apply_inv_apply]

omit [StarOrderedRing B] in
theorem rotationOperator_equivariance_defect (U : EquivariantHilbertModule β E)
    (g : Γ) (M Z R : AdjointableMap B E E) (hZ : U.conjugateOperator g Z = Z) (t : ℝ) :
    (U.conjugateOperator g (rotationOperator M Z t) - rotationOperator M Z t) * R =
      rotationCos t • ((U.conjugateOperator g M - M) * R) := by
  have hconj : U.conjugateOperator g (rotationOperator M Z t) =
      rotationCos t • U.conjugateOperator g M + rotationSin t • Z := by
    let L := U.conjugateMapContinuousLinearMap U g
    change L (rotationCos t • M + rotationSin t • Z) =
      rotationCos t • L M + rotationSin t • Z
    rw [map_add, map_smul, map_smul]
    change rotationCos t • U.conjugateOperator g M + rotationSin t • U.conjugateOperator g Z = _
    rw [hZ]
    rfl
  rw [hconj]
  simp only [rotationOperator, sub_mul, add_mul, smul_mul_assoc]
  module

variable [NonUnitalCStarAlgebra A] [CompleteSpace E] {α : CStarAlgebraAction Γ A}

namespace KasparovCycle

/-- The opposite raw cycle reverses both the grading and Fredholm operator. -/
def opposite (c : KasparovCycle α β E) : KasparovCycle α β E where
  countablyGenerated := c.countablyGenerated
  grading := c.grading.opposite
  groupAction := c.groupAction
  grading_preserved g x := by
    change c.groupAction.action g (-c.grading.grading x) =
      -c.grading.grading (c.groupAction.action g x)
    rw [map_neg, c.grading_preserved]
  representation := c.representation
  representation_even a x := by
    change -c.grading.grading (c.representation a x) = c.representation a (-c.grading.grading x)
    rw [(c.representation a).toCLM.map_neg, c.representation_even]
  representation_equivariant := c.representation_equivariant
  operator := -c.operator
  operator_odd x := by
    change -c.grading.grading ((-c.operator) x) = -(-c.operator) (-c.grading.grading x)
    simp only [AdjointableMap.coe_neg_apply, map_neg, neg_neg]
    exact c.operator_odd x
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

@[simp] theorem opposite_operator (c : KasparovCycle α β E) : c.opposite.operator = -c.operator := rfl
@[simp] theorem opposite_grading (c : KasparovCycle α β E) : c.opposite.grading = c.grading.opposite := rfl
@[simp] theorem opposite_representation (c : KasparovCycle α β E) :
    c.opposite.representation = c.representation := rfl
@[simp] theorem opposite_groupAction (c : KasparovCycle α β E) :
    c.opposite.groupAction = c.groupAction := rfl

/-- The selfadjoint unitary flip satisfies all operator conditions on c plus its opposite. -/
theorem oppositeSum_flip_conditions (c : KasparovCycle α β E) :
    (c.directSum c.opposite).OperatorConditions sumFlip where
  operator_odd := sumFlip_odd_opposite c.grading
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
def oppositeSum_flipCycle (c : KasparovCycle α β E) :
    KasparovCycle α β (HilbertModuleSum B E E) :=
  (c.directSum c.opposite).withOperator sumFlip c.oppositeSum_flip_conditions

theorem oppositeSum_flipCycle_isDegenerate (c : KasparovCycle α β E) :
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
theorem oppositeSum_rotation_conditions (c : KasparovCycle α β E) (t : ℝ) :
    (c.directSum c.opposite).OperatorConditions
      (rotationOperator (c.directSum c.opposite).operator sumFlip t) where
  operator_odd := by
    exact ((c.directSum c.opposite).operator_odd.smul (rotationCos t)).add
      ((sumFlip_odd_opposite c.grading).smul (rotationSin t))
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

end KasparovCycle

namespace KasparovOperatorHomotopy

/-- The actual norm-continuous inverse rotation, from c plus its opposite to the flip. -/
def inverseRotation (c : KasparovCycle α β E) :
    KasparovOperatorHomotopy (c.directSum c.opposite) (c.directSum c.opposite).operator sumFlip where
  path :=
    { toFun := fun t => rotationOperator (c.directSum c.opposite).operator sumFlip (t : ℝ)
      continuous_toFun := (continuous_rotationOperator _ _).comp continuous_subtype_val
      source' := by simp
      target' := by simp }
  conditions t := c.oppositeSum_rotation_conditions (t : ℝ)

@[simp] theorem inverseRotation_path_apply (c : KasparovCycle α β E) (t : I) :
    (inverseRotation c).path t =
      rotationCos (t : ℝ) • (c.directSum c.opposite).operator +
        rotationSin (t : ℝ) • sumFlip := rfl

theorem inverseRotation_target_isDegenerate (c : KasparovCycle α β E) :
    ((inverseRotation c).cycleAt 1).IsDegenerate := by
  simpa only [target_cycleAt, KasparovCycle.oppositeSum_flipCycle] using c.oppositeSum_flipCycle_isDegenerate

end KasparovOperatorHomotopy
end BC4lean.KKTheory
