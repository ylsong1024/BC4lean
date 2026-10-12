import BC4lean.OddFredholmCommutingPhase
import BC4lean.OddKTheoryMatrixUnitaryCycle

/-! # An explicit actual-module odd Fredholm normal-form homotopy

The arbitrary selfadjoint Fredholm operator F occupies the zero row of the
genuine countable sum of copies of E; all other rows carry the degenerate
sign symmetry. Actual operator-valued reflection phases conjugate this
stabilized operator through a norm-continuous selfadjoint Fredholm path.
Its square defect is always a conjugate of the genuine compact entry
I₀(F²-I)E₀. Neither an abstract homotopy filler nor a Bott map is assumed.
Matching the upper endpoint with circle inverse functional calculus and
finite coefficient reduction remains a subsequent step.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped Topology CStarAlgebra

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

/-- Genuine operator unitary phase exp(iπs(F+I)/2) on the original module. -/
def oddFredholmRowHalfPhase (F : selfAdjoint (AdjointableMap B E E)) (s : ℝ) :
    unitary (AdjointableMap B E E) :=
  selfAdjoint.expUnitary ((Real.pi * s / 2) • (F + 1))

theorem continuous_oddFredholmRowHalfPhase (F : selfAdjoint (AdjointableMap B E E)) :
    Continuous (oddFredholmRowHalfPhase F) :=
  selfAdjoint.continuous_expUnitary.comp (by fun_prop)

@[simp] theorem oddFredholmRowHalfPhase_zero (F : selfAdjoint (AdjointableMap B E E)) :
    oddFredholmRowHalfPhase F 0 = 1 := by
  simp [oddFredholmRowHalfPhase]

/-- The actual operator phase acts coordinatewise on the actual completed
row sum, retaining its genuine unitarity. -/
def oddFredholmRowDiagonalHalfPhase (F : selfAdjoint (AdjointableMap B E E)) (s : ℝ) :
    unitary (OddKTheoryCountableOperator B E) :=
  ⟨countableModuleDiagonal (oddFredholmRowHalfPhase F s : AdjointableMap B E E),
    Unitary.map_mem oddKTheoryCountableDiagonalHom (oddFredholmRowHalfPhase F s).property⟩

theorem continuous_oddFredholmRowDiagonalHalfPhase
    (F : selfAdjoint (AdjointableMap B E E)) : Continuous (oddFredholmRowDiagonalHalfPhase F) :=
  ((map_continuous oddKTheoryCountableDiagonalHom).comp
    (continuous_subtype_val.comp (continuous_oddFredholmRowHalfPhase F))).subtype_mk _

set_option maxHeartbeats 1200000 in
/-- Actual commuting projection phase of an integer-coordinate reflection. -/
def oddFredholmRowReflectionPhase (k : ℤ) (F : selfAdjoint (AdjointableMap B E E)) (s : ℝ) :
    unitary (OddKTheoryCountableOperator B E) := by
  have hcomm : Commute (oddKTheoryRowReflectionOperator (B := B) (E := E) k)
      (oddFredholmRowDiagonalHalfPhase F s : OddKTheoryCountableOperator B E) := by
    change Commute (oddKTheoryRowReflectionOperator (B := B) (E := E) k)
      (countableModuleDiagonal (oddFredholmRowHalfPhase F s : AdjointableMap B E E))
    exact oddKTheoryRowReflection_diagonal_commute k
      (oddFredholmRowHalfPhase F s : AdjointableMap B E E)
  exact oddFredholmCommutingPhase (A := OddKTheoryCountableOperator B E)
    (oddKTheoryRowReflectionOperator (B := B) (E := E) k)
    (oddKTheoryRowReflectionOperator_star k) (oddKTheoryRowReflectionOperator_square k)
    (oddFredholmRowDiagonalHalfPhase F s) hcomm

theorem continuous_oddFredholmRowReflectionPhase (k : ℤ)
    (F : selfAdjoint (AdjointableMap B E E)) : Continuous (oddFredholmRowReflectionPhase k F) := by
  apply Continuous.subtype_mk
  change Continuous (fun s => oddFredholmReflectionPositive (oddKTheoryRowReflectionOperator k) +
    (oddFredholmRowDiagonalHalfPhase F s : OddKTheoryCountableOperator B E) *
      oddFredholmReflectionNegative (oddKTheoryRowReflectionOperator k))
  exact continuous_const.add
    ((continuous_subtype_val.comp (continuous_oddFredholmRowDiagonalHalfPhase F)).mul continuous_const)

set_option maxHeartbeats 1200000 in
@[simp] theorem oddFredholmRowReflectionPhase_zero (k : ℤ)
    (F : selfAdjoint (AdjointableMap B E E)) : oddFredholmRowReflectionPhase k F 0 = 1 := by
  apply Subtype.ext
  change oddFredholmCommutingPhaseElement (oddKTheoryRowReflectionOperator k)
    (oddFredholmRowDiagonalHalfPhase F 0) = 1
  have hzero : oddFredholmRowDiagonalHalfPhase F 0 = 1 := by
    apply Subtype.ext
    simp [oddFredholmRowDiagonalHalfPhase, oddKTheoryCountableDiagonal_one]
  rw [hzero, oddFredholmCommutingPhaseElement_one]

def oddFredholmRowNormalFormConjugator (F : selfAdjoint (AdjointableMap B E E)) (s : ℝ) :
    unitary (OddKTheoryCountableOperator B E) :=
  oddFredholmRowReflectionPhase 0 F s * oddFredholmRowReflectionPhase (-1) F s

/-- Actual stabilized operator: F on the zero row, the sign symmetry on all
other rows. Its coordinate projection is not asserted compact. -/
def oddFredholmRowStabilizedOperator (F : selfAdjoint (AdjointableMap B E E)) :
    OddKTheoryCountableOperator B E :=
  oddKTheoryRowSignOperator + countableModuleDiagonal ((F : AdjointableMap B E E) + 1) *
    oddKTheoryRowZeroProjection

theorem oddFredholmRowStabilizedOperator_isSelfAdjoint
    (F : selfAdjoint (AdjointableMap B E E)) : IsSelfAdjoint (oddFredholmRowStabilizedOperator F) := by
  change star (oddFredholmRowStabilizedOperator F) = _
  have hdiag : star (countableModuleDiagonal ((F : AdjointableMap B E E) + 1)) =
      countableModuleDiagonal (star ((F : AdjointableMap B E E) + 1)) :=
    (map_star oddKTheoryCountableDiagonalHom _).symm
  rw [oddFredholmRowStabilizedOperator, star_add, star_mul, oddKTheoryRowSignOperator_star,
    oddKTheoryRowZeroProjection_star, hdiag]
  have hcoef : star ((F : AdjointableMap B E E) + 1) = (F : AdjointableMap B E E) + 1 := by
    rw [star_add, F.property.star_eq, star_one]
  change oddKTheoryRowSignOperator + oddKTheoryRowZeroProjection *
    countableModuleDiagonal (star ((F : AdjointableMap B E E) + 1)) = _
  rw [hcoef, (oddKTheoryRowZeroProjection_diagonal_commute _).eq]

/-- Actual coefficient-coordinate action of the stabilized operator. -/
theorem oddFredholmRowStabilizedOperator_inclusion
    (F : selfAdjoint (AdjointableMap B E E)) (m : ℤ) (b : E) :
    oddFredholmRowStabilizedOperator F (oddKTheoryRowIntegerInclusion m b) =
      if m = 0 then oddKTheoryRowIntegerInclusion m ((F : AdjointableMap B E E) b)
      else oddKTheoryRowIntegerSign m • oddKTheoryRowIntegerInclusion m b := by
  simp only [oddFredholmRowStabilizedOperator, AdjointableMap.coe_add_apply,
    AdjointableMap.mul_apply, oddKTheoryRowSignOperator_inclusion,
    oddKTheoryRowZeroProjection_inclusion]
  by_cases hm : m = 0
  · subst m
    simp only [if_true, oddKTheoryRowDiagonal_integerInclusion,
      AdjointableMap.coe_add_apply, AdjointableMap.one_apply,
      oddKTheoryRowIntegerSign, le_refl, if_true, neg_one_smul, map_add]
    abel
  · simp only [if_neg hm, map_zero, add_zero]

/-- The actual infinite square defect is one genuine coefficient entry. -/
theorem oddFredholmRowStabilizedOperator_square_defect
    (F : selfAdjoint (AdjointableMap B E E)) :
    oddFredholmRowStabilizedOperator F * oddFredholmRowStabilizedOperator F - 1 =
      ((oddKTheoryRowIntegerInclusion (B := B) (E := E) 0).comp
        ((F : AdjointableMap B E E) * (F : AdjointableMap B E E) - 1)).comp (oddKTheoryRowIntegerEvaluation 0) := by
  apply oddKTheoryRowOperator_ext_integerCoordinates
  intro m b
  by_cases hm : m = 0
  · subst m
    simp only [AdjointableMap.coe_sub_apply, AdjointableMap.mul_apply,
      oddFredholmRowStabilizedOperator_inclusion, if_true, AdjointableMap.one_apply,
      AdjointableMap.comp_apply, oddKTheoryRowIntegerEvaluation_inclusion, if_true,
      AdjointableMap.coe_sub_apply, map_sub]
  · simp only [AdjointableMap.coe_sub_apply, AdjointableMap.mul_apply,
      oddFredholmRowStabilizedOperator_inclusion,
      map_smul (oddFredholmRowStabilizedOperator F).toCLM, AdjointableMap.one_apply,
      AdjointableMap.comp_apply, oddKTheoryRowIntegerEvaluation_inclusion, if_neg hm,
      map_zero, smul_smul]
    by_cases hp : 0 ≤ m <;> simp [oddKTheoryRowIntegerSign, hp]

/-- Conjugate the actual stabilized operator through the explicit reflection
phases. This is a norm-continuous actual operator field on the real parameter. -/
def oddFredholmRowNormalFormOperator (F : selfAdjoint (AdjointableMap B E E)) (s : ℝ) :
    OddKTheoryCountableOperator B E :=
  star (oddFredholmRowNormalFormConjugator F s : OddKTheoryCountableOperator B E) *
    oddFredholmRowStabilizedOperator F *
      (oddFredholmRowNormalFormConjugator F s : OddKTheoryCountableOperator B E)

theorem continuous_oddFredholmRowNormalFormOperator
    (F : selfAdjoint (AdjointableMap B E E)) : Continuous (oddFredholmRowNormalFormOperator F) := by
  have hV := (continuous_oddFredholmRowReflectionPhase 0 F).mul
    (continuous_oddFredholmRowReflectionPhase (-1) F)
  have hVcoe := continuous_subtype_val.comp hV
  exact (hVcoe.star.mul continuous_const).mul hVcoe

@[simp] theorem oddFredholmRowNormalFormOperator_zero
    (F : selfAdjoint (AdjointableMap B E E)) :
    oddFredholmRowNormalFormOperator F 0 = oddFredholmRowStabilizedOperator F := by
  simp [oddFredholmRowNormalFormOperator, oddFredholmRowNormalFormConjugator]

theorem oddFredholmRowNormalFormOperator_isSelfAdjoint
    (F : selfAdjoint (AdjointableMap B E E)) (s : ℝ) :
    IsSelfAdjoint (oddFredholmRowNormalFormOperator F s) := by
  change star (oddFredholmRowNormalFormOperator F s) = _
  simp only [oddFredholmRowNormalFormOperator, star_mul, star_star,
    (oddFredholmRowStabilizedOperator_isSelfAdjoint F).star_eq, mul_assoc]

/-- Every actual normal-form operator has the exact unitary-conjugated
stabilized square defect. -/
theorem oddFredholmRowNormalFormOperator_square_defect
    (F : selfAdjoint (AdjointableMap B E E)) (s : ℝ) :
    oddFredholmRowNormalFormOperator F s * oddFredholmRowNormalFormOperator F s - 1 =
      star (oddFredholmRowNormalFormConjugator F s : OddKTheoryCountableOperator B E) *
        (oddFredholmRowStabilizedOperator F * oddFredholmRowStabilizedOperator F - 1) *
          (oddFredholmRowNormalFormConjugator F s : OddKTheoryCountableOperator B E) := by
  let V := oddFredholmRowNormalFormConjugator F s
  let T := oddFredholmRowStabilizedOperator F
  have hVstar : star (V : OddKTheoryCountableOperator B E) *
      (V : OddKTheoryCountableOperator B E) = 1 :=
    (Unitary.mem_iff.mp V.property).1
  have hVmul : (V : OddKTheoryCountableOperator B E) *
      star (V : OddKTheoryCountableOperator B E) = 1 :=
    (Unitary.mem_iff.mp V.property).2
  change (star (V : OddKTheoryCountableOperator B E) * T * (V : OddKTheoryCountableOperator B E)) *
    (star (V : OddKTheoryCountableOperator B E) * T * (V : OddKTheoryCountableOperator B E)) - 1 = _
  calc
    _ = star (V : OddKTheoryCountableOperator B E) * T *
      ((V : OddKTheoryCountableOperator B E) * star (V : OddKTheoryCountableOperator B E)) * T * (V : OddKTheoryCountableOperator B E) - 1 := by
        simp only [mul_assoc]
    _ = star (V : OddKTheoryCountableOperator B E) * (T * T) *
        (V : OddKTheoryCountableOperator B E) - 1 := by
      rw [hVmul]
      simp only [mul_one, mul_assoc]
    _ = star (V : OddKTheoryCountableOperator B E) * (T * T - 1) *
        (V : OddKTheoryCountableOperator B E) := by
      rw [mul_sub, sub_mul, mul_one, hVstar]

/-- Compactness is retained along the actual arbitrary-module normal-form
path, because F²-I is compact on E. -/
theorem oddFredholmRowNormalFormOperator_square_isModuleCompact
    (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) * (F : AdjointableMap B E E) - 1)) (s : ℝ) :
    IsModuleCompact (oddFredholmRowNormalFormOperator F s * oddFredholmRowNormalFormOperator F s - 1) := by
  rw [oddFredholmRowNormalFormOperator_square_defect, oddFredholmRowStabilizedOperator_square_defect]
  exact mul_mem_moduleCompact_right
    (mul_mem_moduleCompact_left _ ((hF.comp_left (oddKTheoryRowIntegerInclusion 0)).comp_right
      (oddKTheoryRowIntegerEvaluation 0))) _

end BC4lean.KKTheory
