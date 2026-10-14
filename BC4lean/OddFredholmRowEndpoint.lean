import BC4lean.OddFredholmIntervalRowFormula
import BC4lean.OddFredholmRowDecomposition

/-! # The actual arbitrary-F inverse endpoint

The concrete reflection-phase endpoint is the actual periodic unitary
pullback at exp(iπ(F+I)). The proof compares real-interval scalar entries and
transfers them through the genuine CFC of the original selfadjoint
contraction. Thus the explicit homotopy starts in the original odd class and
ends at its actual infinite-row unitary inverse.
-/

noncomputable section
namespace BC4lean.KKTheory

def oddFredholmIntervalReflectionA : C(OddFredholmInterval, ℂ) :=
  (2 : ℂ)⁻¹ • (1 + oddFredholmIntervalHalfPhase)

def oddFredholmIntervalReflectionB : C(OddFredholmInterval, ℂ) :=
  (2 : ℂ)⁻¹ • (1 - oddFredholmIntervalHalfPhase)

theorem oddFredholmIntervalPermutationCoefficient_vector (i : Fin 4) :
    oddFredholmIntervalPermutationCoefficient i =
      ![oddFredholmIntervalReflectionA ^ 2,
        oddFredholmIntervalReflectionA * oddFredholmIntervalReflectionB,
        oddFredholmIntervalReflectionA * oddFredholmIntervalReflectionB,
        oddFredholmIntervalReflectionB ^ 2] i := by
  fin_cases i
  · ext r
    change ((1 + (oddKTheoryHalfPhase (oddFredholmIntervalParameter r) : ℂ)) / 2) ^ 2 =
      ((2 : ℂ)⁻¹ • (1 + (oddKTheoryHalfPhase (oddFredholmIntervalParameter r) : ℂ))) ^ 2
    simp only [smul_eq_mul, div_eq_mul_inv]
    ring
  · ext r
    change ((1 + (oddKTheoryHalfPhase (oddFredholmIntervalParameter r) : ℂ)) / 2) *
        ((1 - (oddKTheoryHalfPhase (oddFredholmIntervalParameter r) : ℂ)) / 2) =
      ((2 : ℂ)⁻¹ • (1 + (oddKTheoryHalfPhase (oddFredholmIntervalParameter r) : ℂ))) *
        ((2 : ℂ)⁻¹ • (1 - (oddKTheoryHalfPhase (oddFredholmIntervalParameter r) : ℂ)))
    simp only [smul_eq_mul, div_eq_mul_inv]
    ring
  · ext r
    change ((1 + (oddKTheoryHalfPhase (oddFredholmIntervalParameter r) : ℂ)) / 2) *
        ((1 - (oddKTheoryHalfPhase (oddFredholmIntervalParameter r) : ℂ)) / 2) =
      ((2 : ℂ)⁻¹ • (1 + (oddKTheoryHalfPhase (oddFredholmIntervalParameter r) : ℂ))) *
        ((2 : ℂ)⁻¹ • (1 - (oddKTheoryHalfPhase (oddFredholmIntervalParameter r) : ℂ)))
    simp only [smul_eq_mul, div_eq_mul_inv]
    ring
  · ext r
    change ((1 - (oddKTheoryHalfPhase (oddFredholmIntervalParameter r) : ℂ)) / 2) ^ 2 =
      ((2 : ℂ)⁻¹ • (1 - (oddKTheoryHalfPhase (oddFredholmIntervalParameter r) : ℂ))) ^ 2
    simp only [smul_eq_mul, div_eq_mul_inv]
    ring

section ActualRows

variable {Γ B E : Type*} [Group Γ] [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

open scoped CStarAlgebra

/-- The actual periodic infinite-row unitary pullback for a genuine
operator unitary on the original coefficient module. -/
def oddFredholmRowUnitaryPullback (u : unitary (AdjointableMap B E E)) :
    OddKTheoryCountableOperator B E :=
  oddKTheoryFiniteRowFormula (oddKTheoryCircleCFC u)
    oddKTheoryLoopTermCoefficient oddKTheoryRowLoopTermOperator

theorem oddFredholmIntervalPermutationFormula_product
    (φ : C(OddFredholmInterval, ℂ) →⋆ₐ[ℂ] AdjointableMap B E E) :
    oddKTheoryFiniteRowFormula φ oddFredholmIntervalPermutationCoefficient
      oddKTheoryRowLoopFixedPermutation =
        (countableModuleDiagonal (φ oddFredholmIntervalReflectionA) +
          countableModuleDiagonal (φ oddFredholmIntervalReflectionB) * oddKTheoryRowReflectionOperator 0) *
        (countableModuleDiagonal (φ oddFredholmIntervalReflectionA) +
          countableModuleDiagonal (φ oddFredholmIntervalReflectionB) * oddKTheoryRowReflectionOperator (-1)) := by
  let ψ := oddKTheoryCountableDiagonalHom.comp φ
  let a := ψ oddFredholmIntervalReflectionA
  let b := ψ oddFredholmIntervalReflectionB
  let R := oddKTheoryRowReflectionOperator (B := B) (E := E) 0
  let S := oddKTheoryRowReflectionOperator (B := B) (E := E) (-1)
  have hRa : R * a = a * R := (oddKTheoryRowReflection_diagonal_commute 0 _).eq
  have hRb : R * b = b * R := (oddKTheoryRowReflection_diagonal_commute 0 _).eq
  have hab : b * a = a * b := by
    change ψ oddFredholmIntervalReflectionB * ψ oddFredholmIntervalReflectionA =
      ψ oddFredholmIntervalReflectionA * ψ oddFredholmIntervalReflectionB
    rw [← map_mul, ← map_mul, mul_comm oddFredholmIntervalReflectionB]
  have hba : (b * R) * a = (a * b) * R := by
    rw [mul_assoc, hRa, ← mul_assoc, hab]
  have hbb : (b * R) * (b * S) = (b * b) * (R * S) := by
    rw [← mul_assoc, mul_assoc b R b, hRb]
    simp only [mul_assoc]
  change (∑ i : Fin 4, ψ (oddFredholmIntervalPermutationCoefficient i) *
    oddKTheoryRowLoopFixedPermutation i) = (a + b * R) * (a + b * S)
  simp only [Fin.sum_univ_four, oddFredholmIntervalPermutationCoefficient_vector,
    oddKTheoryRowLoopFixedPermutation, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons,
    map_pow, map_mul, mul_one]
  change a ^ 2 + a * b * R + a * b * S + b ^ 2 * (R * S) = _
  rw [add_mul, mul_add, mul_add, hba, hbb]
  simp only [pow_two, ← mul_assoc]
  abel

set_option maxHeartbeats 1200000 in
theorem oddFredholmIntervalReflectionFormula_phase
    (F : selfAdjoint (AdjointableMap B E E)) (hF : ‖(F : AdjointableMap B E E)‖ ≤ 1) (k : ℤ) :
    countableModuleDiagonal (oddFredholmIntervalCFC F hF oddFredholmIntervalReflectionA) +
      countableModuleDiagonal (oddFredholmIntervalCFC F hF oddFredholmIntervalReflectionB) *
        oddKTheoryRowReflectionOperator k =
          (oddFredholmRowReflectionPhase k F 1 : OddKTheoryCountableOperator B E) := by
  dsimp only [oddFredholmRowReflectionPhase, oddFredholmCommutingPhase]
  let ψ : C(OddFredholmInterval, ℂ) →⋆ₐ[ℂ] OddKTheoryCountableOperator B E :=
    (oddKTheoryCountableDiagonalHom (B := B) (E := E)).comp
      (oddFredholmIntervalCFC (A := AdjointableMap B E E) F hF)
  have hw : ψ oddFredholmIntervalHalfPhase =
      (oddFredholmRowDiagonalHalfPhase F 1 : OddKTheoryCountableOperator B E) := by
    simpa only [ψ, StarAlgHom.comp_apply, oddKTheoryCountableDiagonalHom,
      oddFredholmRowDiagonalHalfPhase, oddFredholmRowHalfPhase] using!
      congrArg (countableModuleDiagonal (B := B) (E := E))
        (oddFredholmIntervalCFC_halfPhase (A := AdjointableMap B E E) F hF)
  change ψ oddFredholmIntervalReflectionA + ψ oddFredholmIntervalReflectionB *
    oddKTheoryRowReflectionOperator k =
      oddFredholmCommutingPhaseElement (oddKTheoryRowReflectionOperator k)
        (oddFredholmRowDiagonalHalfPhase F 1)
  rw [oddFredholmIntervalReflectionA, oddFredholmIntervalReflectionB,
    map_smul, map_smul, map_add, map_sub, map_one, hw]
  simp only [oddFredholmCommutingPhaseElement, oddFredholmReflectionPositive,
    oddFredholmReflectionNegative, mul_smul_comm, mul_sub, mul_one,
    smul_mul_assoc, sub_mul, one_mul]
  norm_num
  module

theorem oddFredholmIntervalPermutationFormula_conjugator
    (F : selfAdjoint (AdjointableMap B E E)) (hF : ‖(F : AdjointableMap B E E)‖ ≤ 1) :
    oddKTheoryFiniteRowFormula (oddFredholmIntervalCFC F hF)
      oddFredholmIntervalPermutationCoefficient oddKTheoryRowLoopFixedPermutation =
        (oddFredholmRowNormalFormConjugator F 1 : OddKTheoryCountableOperator B E) := by
  rw [oddFredholmIntervalPermutationFormula_product,
    oddFredholmIntervalReflectionFormula_phase, oddFredholmIntervalReflectionFormula_phase]
  rfl

theorem oddFredholmIntervalCrossingFormula_stabilized
    (F : selfAdjoint (AdjointableMap B E E)) (hF : ‖(F : AdjointableMap B E E)‖ ≤ 1) :
    oddKTheoryFiniteRowFormula (oddFredholmIntervalCFC F hF)
      oddFredholmIntervalCrossingCoefficient oddFredholmIntervalCrossingFixed =
        oddFredholmRowStabilizedOperator F := by
  simp only [oddKTheoryFiniteRowFormula, Fin.sum_univ_two,
    oddFredholmIntervalCrossingCoefficient, oddFredholmIntervalCrossingFixed,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_one, map_add,
    oddFredholmIntervalCFC_coordinate, oddKTheoryCountableDiagonal_one, one_mul]
  rfl

/-- The genuine arbitrary-F row homotopy endpoint is exactly the actual
periodic unitary pullback of its actual exponential index unitary. -/
theorem oddFredholmRowNormalFormOperator_one_eq_pullback
    (F : selfAdjoint (AdjointableMap B E E)) (hF : ‖(F : AdjointableMap B E E)‖ ≤ 1) :
    oddFredholmRowNormalFormOperator F 1 =
      oddFredholmRowUnitaryPullback (B := B) (E := E)
        (oddFredholmExponential (A := AdjointableMap B E E) F) := by
  have hraw : oddKTheoryFiniteRowFormula (oddFredholmIntervalCFC F hF)
      oddFredholmIntervalRawCoefficient oddFredholmIntervalRawFixed =
        oddFredholmRowNormalFormOperator F 1 := by
    rw [oddFredholmIntervalRawFormula_conjugation,
      oddFredholmIntervalPermutationFormula_conjugator,
      oddFredholmIntervalCrossingFormula_stabilized]
    dsimp only [oddFredholmRowNormalFormOperator]
  rw [← hraw, oddFredholmIntervalRawFormula_eq_periodic]
  unfold oddFredholmRowUnitaryPullback oddKTheoryFiniteRowFormula
  apply Finset.sum_congr rfl
  intro i _
  rw [oddFredholmCircleCFC_exponential]
  rfl

/-- The actual odd scalar cycle at the infinite-row inverse of the
exponential, with its compact square defect derived from the explicit path. -/
def oddFredholmRowExponentialPullbackCycle (hE : IsCountablyGeneratedModule B E)
    (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) * (F : AdjointableMap B E E) - 1))
    (hnorm : ‖(F : AdjointableMap B E E)‖ ≤ 1) :
    OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B) (CountableHilbertModuleSum B E) :=
  (oddFredholmRowStabilizedCycle (Γ := Γ) (B := B) (E := E) hE F hF).withOperator
    (oddFredholmRowUnitaryPullback (B := B) (E := E)
        (oddFredholmExponential (A := AdjointableMap B E E) F)) (by
      rw [← oddFredholmRowNormalFormOperator_one_eq_pullback F hnorm]
      exact (oddFredholmRowNormalFormHomotopy (Γ := Γ) (B := B) (E := E) hE F hF).target_conditions)

variable [TopologicalSpace.SeparableSpace B]

/-- The explicit arbitrary-F inverse composition already holds in the
actual full quotient on the genuine infinite row module. Finite matrix
compression is a further comparison with the project's OperatorK1. -/
theorem oddFredholmRowExponentialPullbackCycle_class (hE : IsCountablyGeneratedModule B E)
    (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) * (F : AdjointableMap B E E) - 1))
    (hnorm : ‖(F : AdjointableMap B E E)‖ ≤ 1) :
    OddKK.mk (BundledOddKasparovCycle.of
      (oddFredholmRowExponentialPullbackCycle (Γ := Γ) hE F hF hnorm)) =
        OddKK.mk (BundledOddKasparovCycle.of
          (oddKTheoryScalarFredholmCycle (Γ := Γ) hE F F.property hF)) := by
  let c := oddFredholmRowStabilizedCycle (Γ := Γ) (B := B) (E := E) hE F hF
  let H := oddFredholmRowNormalFormHomotopy (Γ := Γ) (B := B) (E := E) hE F hF
  have hsource : c.withOperator (oddFredholmRowStabilizedOperator (B := B) (E := E) F)
      H.source_conditions = c := by
    rfl
  have htarget : c.withOperator (oddFredholmRowNormalFormOperator (B := B) (E := E) F 1)
      H.target_conditions = oddFredholmRowExponentialPullbackCycle (Γ := Γ) hE F hF hnorm := by
    have hreplace {T S : OddKTheoryCountableOperator B E}
        (hT : c.OperatorConditions T) (hS : c.OperatorConditions S) (heq : T = S) :
        c.withOperator T hT = c.withOperator S hS := by
      cases heq
      rfl
    dsimp only [c, oddFredholmRowExponentialPullbackCycle]
    apply hreplace
    exact oddFredholmRowNormalFormOperator_one_eq_pullback (B := B) (E := E) F hnorm
  have hpath := OddKK.mk_eq_of_full
    (c := BundledOddKasparovCycle.of
      (c.withOperator (oddFredholmRowStabilizedOperator (B := B) (E := E) F)
        H.source_conditions))
    (d := BundledOddKasparovCycle.of
      (c.withOperator (oddFredholmRowNormalFormOperator (B := B) (E := E) F 1)
        H.target_conditions))
    (FullOddKasparovHomotopy.ofOperatorHomotopy H)
  rw [hsource, htarget] at hpath
  exact hpath.symm.trans
    (oddFredholmRowStabilizedCycle_class (Γ := Γ) (B := B) (E := E) hE F hF)

end ActualRows
end BC4lean.KKTheory
