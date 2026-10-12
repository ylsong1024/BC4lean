import BC4lean.KasparovInverseRotation
import BC4lean.HilbertModuleEquiv

/-! # The actual doubled unitary rotation

The standard two-copy rotation joins U ⊕ U* to the identity. If U commutes
with a reference operator Q, the entire path commutes with Q ⊕ Q. The proof
uses actual adjointable maps on the Hilbert-module sum, including its true
coefficient norm; no contraction theorem for the full unitary group is used.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

/-- The skew rotation of the two actual Hilbert-module summands. -/
def moduleRotationSkew :
    AdjointableMap B (HilbertModuleSum B E E) (HilbertModuleSum B E E) :=
  -(sumInl.comp sumSnd) + sumInr.comp sumFst

@[simp] theorem moduleRotationSkew_apply (x : HilbertModuleSum B E E) :
    moduleRotationSkew x = sumMk (-x.snd) x.fst := by
  simp only [moduleRotationSkew, AdjointableMap.coe_add_apply,
    AdjointableMap.coe_neg_apply, AdjointableMap.comp_apply, sumSnd_apply,
    sumFst_apply, sumInl_apply, sumInr_apply]
  apply Prod.ext
  · change -(x.snd) + 0 = -x.snd
    exact add_zero _
  · change -(0 : E) + x.fst = x.fst
    simp only [neg_zero, zero_add]

@[simp] theorem moduleRotationSkew_star :
    star (moduleRotationSkew (B := B) (E := E)) = -moduleRotationSkew := by
  simp only [moduleRotationSkew, star_add, star_neg, AdjointableMap.star_eq_adjoint,
    AdjointableMap.adjoint_comp, sumSnd_adjoint, sumInl_adjoint,
    sumFst_adjoint, sumInr_adjoint]
  abel

@[simp] theorem moduleRotationSkew_square :
    moduleRotationSkew (B := B) (E := E) * moduleRotationSkew = -1 := by
  ext x
  simp only [AdjointableMap.mul_apply, moduleRotationSkew_apply, sumMk_fst, sumMk_snd,
    AdjointableMap.coe_neg_apply, AdjointableMap.one_apply]
  apply Prod.ext <;> rfl

/-- The usual scalar rotation, acting on the actual module direct sum. -/
def moduleRotation (t : ℝ) :
    AdjointableMap B (HilbertModuleSum B E E) (HilbertModuleSum B E E) :=
  rotationOperator 1 moduleRotationSkew t

@[simp] theorem moduleRotation_zero : moduleRotation (B := B) (E := E) 0 = 1 :=
  rotationOperator_zero _ _

@[simp] theorem moduleRotation_one :
    moduleRotation (B := B) (E := E) 1 = moduleRotationSkew :=
  rotationOperator_one _ _

@[simp] theorem moduleRotation_star (t : ℝ) :
    star (moduleRotation (B := B) (E := E) t) =
      rotationCos t • 1 - rotationSin t • moduleRotationSkew := by
  have ha : star (rotationCos t) = rotationCos t := by
    simp only [rotationCos, Complex.star_def, Complex.conj_ofReal]
  have hb : star (rotationSin t) = rotationSin t := by
    simp only [rotationSin, Complex.star_def, Complex.conj_ofReal]
  simp only [moduleRotation, rotationOperator, star_add, star_smul, star_one,
    ha, hb, moduleRotationSkew_star, smul_neg, sub_eq_add_neg]

/-- Both unitary equations hold in the actual adjointable operator algebra. -/
theorem moduleRotation_mem_unitary (t : ℝ) :
    moduleRotation (B := B) (E := E) t ∈ unitary
      (AdjointableMap B (HilbertModuleSum B E E) (HilbertModuleSum B E E)) := by
  apply Unitary.mem_iff.mpr
  constructor
  · calc
      star (moduleRotation (B := B) (E := E) t) * moduleRotation t =
          (rotationCos t * rotationCos t + rotationSin t * rotationSin t) •
            (1 : AdjointableMap B (HilbertModuleSum B E E) (HilbertModuleSum B E E)) := by
        rw [moduleRotation_star]
        simp only [moduleRotation, rotationOperator, sub_mul, mul_add,
          smul_mul_assoc, mul_smul_comm, one_mul, mul_one, moduleRotationSkew_square]
        module
      _ = 1 := by rw [rotationCos_sq_add_rotationSin_sq]; exact one_smul ℂ _
  · calc
      moduleRotation (B := B) (E := E) t * star (moduleRotation t) =
          (rotationCos t * rotationCos t + rotationSin t * rotationSin t) •
            (1 : AdjointableMap B (HilbertModuleSum B E E) (HilbertModuleSum B E E)) := by
        rw [moduleRotation_star]
        simp only [moduleRotation, rotationOperator, mul_sub, add_mul,
          smul_mul_assoc, mul_smul_comm, one_mul, mul_one, moduleRotationSkew_square]
        module
      _ = 1 := by rw [rotationCos_sq_add_rotationSin_sq]; exact one_smul ℂ _

/-- The explicit rotation factors for the doubled unitary. -/
def doubledAdjointableUnitaryPath (U : unitary (AdjointableMap B E E)) (t : ℝ) :
    AdjointableMap B (HilbertModuleSum B E E) (HilbertModuleSum B E E) :=
  sumMap (U : AdjointableMap B E E) 1 * moduleRotation t *
    sumMap 1 (star (U : AdjointableMap B E E)) * star (moduleRotation t)

/-- The path is continuous in the actual operator norm. -/
theorem continuous_doubledAdjointableUnitaryPath
    (U : unitary (AdjointableMap B E E)) : Continuous (doubledAdjointableUnitaryPath U) := by
  have hR : Continuous (moduleRotation (B := B) (E := E)) := continuous_rotationOperator _ _
  exact (((continuous_const.mul hR).mul continuous_const).mul hR.star)

@[simp] theorem doubledAdjointableUnitaryPath_zero (U : unitary (AdjointableMap B E E)) :
    doubledAdjointableUnitaryPath U 0 = sumMap (U : AdjointableMap B E E) (star U) := by
  ext x
  simp only [doubledAdjointableUnitaryPath, moduleRotation_zero, star_one,
    mul_one, AdjointableMap.mul_apply, sumMap_apply, AdjointableMap.one_apply,
    sumMk_fst, sumMk_snd]

@[simp] theorem doubledAdjointableUnitaryPath_one (U : unitary (AdjointableMap B E E)) :
    doubledAdjointableUnitaryPath U 1 = 1 := by
  have hU : (U : AdjointableMap B E E) * star (U : AdjointableMap B E E) = 1 := U.property.2
  ext x
  simp only [doubledAdjointableUnitaryPath, moduleRotation_one, moduleRotationSkew_star,
    AdjointableMap.mul_apply, AdjointableMap.coe_neg_apply, moduleRotationSkew_apply,
    sumMap_apply, sumMk_fst, sumMk_snd, AdjointableMap.one_apply, map_neg]
  apply Prod.ext
  · change -(-((U : AdjointableMap B E E) (star (U : AdjointableMap B E E) x.fst))) = x.fst
    rw [neg_neg]
    simpa only [AdjointableMap.mul_apply, AdjointableMap.one_apply] using
      congrArg (fun T : AdjointableMap B E E => T x.fst) hU
  · change -(-x.snd) = x.snd
    exact neg_neg x.snd

/-- Block-diagonal unitary operators are unitary on the actual Hilbert sum. -/
theorem sumMap_mem_unitary (U V : unitary (AdjointableMap B E E)) :
    sumMap (U : AdjointableMap B E E) (V : AdjointableMap B E E) ∈
      unitary (AdjointableMap B (HilbertModuleSum B E E) (HilbertModuleSum B E E)) := by
  apply Unitary.mem_iff.mpr
  constructor
  · rw [← sumMap_star, ← sumMap_mul, U.property.1, V.property.1, sumMap_one]
  · rw [← sumMap_star, ← sumMap_mul, U.property.2, V.property.2, sumMap_one]

/-- Every point of the doubled rotation is an actual unitary. -/
theorem doubledAdjointableUnitaryPath_mem_unitary
    (U : unitary (AdjointableMap B E E)) (t : ℝ) :
    doubledAdjointableUnitaryPath U t ∈
      unitary (AdjointableMap B (HilbertModuleSum B E E) (HilbertModuleSum B E E)) := by
  exact (unitary _).mul_mem
    ((unitary _).mul_mem
      ((unitary _).mul_mem (sumMap_mem_unitary U 1) (moduleRotation_mem_unitary t))
      (sumMap_mem_unitary 1 (star U)))
    (Unitary.star_mem (moduleRotation_mem_unitary t))

/-- The scalar rotations commute with any repeated reference operator. -/
theorem moduleRotation_commutes_sumMap (Q : AdjointableMap B E E) (t : ℝ) :
    Commute (moduleRotation (B := B) (E := E) t) (sumMap Q Q) := by
  show moduleRotation t * sumMap Q Q = sumMap Q Q * moduleRotation t
  ext x
  apply Prod.ext <;>
    simp [moduleRotation, rotationOperator, moduleRotationSkew_apply, sumMap_apply,
      map_add, map_smul, map_neg]

/-- Actual reference commutation persists at every point of the unitary path. -/
theorem doubledAdjointableUnitaryPath_commutes
    (U : unitary (AdjointableMap B E E)) (Q : AdjointableMap B E E)
    (hU : Commute (U : AdjointableMap B E E) Q) (t : ℝ) :
    Commute (doubledAdjointableUnitaryPath U t) (sumMap Q Q) := by
  have hUs : Commute (star (U : AdjointableMap B E E)) Q := by
    show star (U : AdjointableMap B E E) * Q = Q * star (U : AdjointableMap B E E)
    calc
      star (U : AdjointableMap B E E) * Q =
          star (U : AdjointableMap B E E) * Q *
            ((U : AdjointableMap B E E) * star (U : AdjointableMap B E E)) := by
        rw [U.property.2, mul_one]
      _ = star (U : AdjointableMap B E E) *
          ((U : AdjointableMap B E E) * Q) * star (U : AdjointableMap B E E) := by
        rw [hU.eq]
        simp only [mul_assoc]
      _ = Q * star (U : AdjointableMap B E E) := by
        rw [← mul_assoc, U.property.1, one_mul]
  have hL : Commute (sumMap (U : AdjointableMap B E E) 1) (sumMap Q Q) := by
    show _ * _ = _ * _
    rw [← sumMap_mul, ← sumMap_mul, one_mul, mul_one, hU.eq]
  have hM : Commute (sumMap 1 (star (U : AdjointableMap B E E))) (sumMap Q Q) := by
    show _ * _ = _ * _
    rw [← sumMap_mul, ← sumMap_mul, one_mul, mul_one, hUs.eq]
  have hRs : Commute (star (moduleRotation (B := B) (E := E) t)) (sumMap Q Q) := by
    rw [moduleRotation_star]
    show _ * _ = _ * _
    ext x
    apply Prod.ext <;>
      simp [moduleRotationSkew_apply, sumMap_apply, map_sub, map_smul, map_neg]
  exact ((hL.mul_left (moduleRotation_commutes_sumMap Q t)).mul_left hM).mul_left hRs

/-- Conjugate the first member of a stabilized pair along the actual doubled rotation. -/
def doubledUnitaryRelativeProjectionPath
    (U : unitary (AdjointableMap B E E)) (P Q : AdjointableMap B E E) (t : ℝ) :
    AdjointableMap B (HilbertModuleSum B E E) (HilbertModuleSum B E E) :=
  doubledAdjointableUnitaryPath U t * sumMap P Q *
    star (doubledAdjointableUnitaryPath U t)

/-- The conjugated projection varies continuously in operator norm. -/
theorem continuous_doubledUnitaryRelativeProjectionPath
    (U : unitary (AdjointableMap B E E)) (P Q : AdjointableMap B E E) :
    Continuous (doubledUnitaryRelativeProjectionPath U P Q) :=
  ((continuous_doubledAdjointableUnitaryPath U).mul continuous_const).mul
    (continuous_doubledAdjointableUnitaryPath U).star

/-- The actual two-copy block of projections is a projection. -/
theorem doubledReferenceSum_isStarProjection {P Q : AdjointableMap B E E}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    IsStarProjection (sumMap P Q) := by
  apply isStarProjection_iff'.mpr
  constructor
  · rw [← sumMap_mul, hP.isIdempotentElem.eq, hQ.isIdempotentElem.eq]
  · rw [← sumMap_star, hP.isSelfAdjoint.star_eq, hQ.isSelfAdjoint.star_eq]

/-- Every point is a genuine projection, by the proved unitary equations. -/
theorem doubledUnitaryRelativeProjectionPath_isStarProjection
    (U : unitary (AdjointableMap B E E)) {P Q : AdjointableMap B E E}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (t : ℝ) :
    IsStarProjection (doubledUnitaryRelativeProjectionPath U P Q t) := by
  let W := doubledAdjointableUnitaryPath U t
  have hW : star W * W = 1 := (doubledAdjointableUnitaryPath_mem_unitary U t).1
  have hPQ := doubledReferenceSum_isStarProjection hP hQ
  apply isStarProjection_iff'.mpr
  constructor
  · change (W * sumMap P Q * star W) * (W * sumMap P Q * star W) = _
    calc
      (W * sumMap P Q * star W) * (W * sumMap P Q * star W) =
          W * (sumMap P Q * sumMap P Q) * star W := by
        simp only [mul_assoc]
        rw [← mul_assoc (star W) W, hW, one_mul]
      _ = W * sumMap P Q * star W := by rw [hPQ.isIdempotentElem.eq]
  · change star (W * sumMap P Q * star W) = W * sumMap P Q * star W
    simp only [star_mul, star_star, hPQ.isSelfAdjoint.star_eq, mul_assoc]

@[simp] theorem doubledUnitaryRelativeProjectionPath_zero
    (U : unitary (AdjointableMap B E E)) (P Q : AdjointableMap B E E)
    (hU : Commute (U : AdjointableMap B E E) Q) :
    doubledUnitaryRelativeProjectionPath U P Q 0 =
      sumMap ((U : AdjointableMap B E E) * P * star (U : AdjointableMap B E E)) Q := by
  have hQ : star (U : AdjointableMap B E E) * Q * (U : AdjointableMap B E E) = Q :=
    (commute_unitary_iff_star_left_conjugate U.property).mp hU
  simp only [doubledUnitaryRelativeProjectionPath, doubledAdjointableUnitaryPath_zero,
    ← sumMap_star, star_star, ← sumMap_mul, hQ]

@[simp] theorem doubledUnitaryRelativeProjectionPath_one
    (U : unitary (AdjointableMap B E E)) (P Q : AdjointableMap B E E) :
    doubledUnitaryRelativeProjectionPath U P Q 1 = sumMap P Q := by
  simp only [doubledUnitaryRelativeProjectionPath, doubledAdjointableUnitaryPath_one,
    star_one, one_mul, mul_one]

/-- Reference commutation gives an exact factorization through the compact difference. -/
theorem doubledUnitaryRelativeProjectionPath_difference
    (U : unitary (AdjointableMap B E E)) (P Q : AdjointableMap B E E)
    (hU : Commute (U : AdjointableMap B E E) Q) (t : ℝ) :
    doubledUnitaryRelativeProjectionPath U P Q t - sumMap Q Q =
      doubledAdjointableUnitaryPath U t * sumMap (P - Q) 0 *
        star (doubledAdjointableUnitaryPath U t) := by
  let W := doubledAdjointableUnitaryPath U t
  have hW : W * star W = 1 := (doubledAdjointableUnitaryPath_mem_unitary U t).2
  have hcomm : W * sumMap Q Q = sumMap Q Q * W :=
    (doubledAdjointableUnitaryPath_commutes U Q hU t).eq
  have hfix : W * sumMap Q Q * star W = sumMap Q Q := by
    rw [hcomm, mul_assoc, hW, mul_one]
  change W * sumMap P Q * star W - sumMap Q Q = _
  rw [← hfix, ← sub_mul, ← mul_sub, ← sumMap_sub, sub_self]

/-- All compactness is derived from the original compact difference and ideal laws. -/
theorem doubledUnitaryRelativeProjectionPath_difference_isModuleCompact
    (U : unitary (AdjointableMap B E E)) {P Q : AdjointableMap B E E}
    (hU : Commute (U : AdjointableMap B E E) Q)
    (hc : IsModuleCompact (P - Q)) (t : ℝ) :
    IsModuleCompact (doubledUnitaryRelativeProjectionPath U P Q t - sumMap Q Q) := by
  rw [doubledUnitaryRelativeProjectionPath_difference U P Q hU t]
  exact ((hc.sumMap IsModuleCompact.zero).comp_left
    (doubledAdjointableUnitaryPath U t)).comp_right
      (star (doubledAdjointableUnitaryPath U t))

end BC4lean.KKTheory
