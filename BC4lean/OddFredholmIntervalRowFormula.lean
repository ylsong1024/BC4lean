import BC4lean.OddFredholmIntervalFunctionalCalculus
import BC4lean.OddKTheoryLoopSquareTransfer

/-! # Actual finite entry formula for the arbitrary-F endpoint

The scalar interval conjugation and periodic circle pullback have the same
actual signed row entries. Their equality transfers through any genuine
interval coefficient action. The finite formula uses four fixed permutations
and two crossing terms, with no tensor-product identification.
-/

noncomputable section
namespace BC4lean.KKTheory

def oddFredholmIntervalPermutationCoefficient (i : Fin 4) : C(OddFredholmInterval, ℂ) :=
  ⟨fun r => oddKTheoryLoopScalarCoefficients (oddFredholmIntervalParameter r) i,
    (continuous_oddKTheoryLoopScalarCoefficients i).comp (by
      unfold oddFredholmIntervalParameter
      fun_prop)⟩

def oddFredholmIntervalCrossingCoefficient : Fin 2 → C(OddFredholmInterval, ℂ) :=
  ![1, oddFredholmIntervalCoordinate + 1]

def oddFredholmIntervalCrossingTarget : Fin 2 → ℤ → ℤ := ![id, fun _ => 0]
def oddFredholmIntervalCrossingWeight : Fin 2 → ℤ → ℂ :=
  ![oddKTheoryRowIntegerSign, fun m => if m = 0 then 1 else 0]

abbrev OddFredholmIntervalRawTerm := (Fin 4 × Fin 2) × Fin 4

def oddFredholmIntervalRawCoefficient (p : OddFredholmIntervalRawTerm) :
    C(OddFredholmInterval, ℂ) :=
  star (oddFredholmIntervalPermutationCoefficient p.1.1) *
    oddFredholmIntervalCrossingCoefficient p.1.2 * oddFredholmIntervalPermutationCoefficient p.2

def oddFredholmIntervalRawTarget (p : OddFredholmIntervalRawTerm) (m : ℤ) : ℤ :=
  oddKTheoryLoopCoordinateInverse p.1.1
    (oddFredholmIntervalCrossingTarget p.1.2 (oddKTheoryLoopCoordinatePermutation p.2 m))

def oddFredholmIntervalRawWeight (p : OddFredholmIntervalRawTerm) (m : ℤ) : ℂ :=
  oddFredholmIntervalCrossingWeight p.1.2 (oddKTheoryLoopCoordinatePermutation p.2 m)

def oddFredholmIntervalPeriodicCoefficient (i : OddKTheoryLoopTerm) :
    C(OddFredholmInterval, ℂ) := (oddKTheoryLoopTermCoefficient i).comp oddFredholmIntervalCircle

section ActualRows

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

def oddFredholmIntervalCrossingFixed : Fin 2 → OddKTheoryCountableOperator B E :=
  ![oddKTheoryRowSignOperator, oddKTheoryRowZeroProjection]

def oddFredholmIntervalRawFixed (p : OddFredholmIntervalRawTerm) :
    OddKTheoryCountableOperator B E :=
  star (oddKTheoryRowLoopFixedPermutation p.1.1) *
    oddFredholmIntervalCrossingFixed p.1.2 * oddKTheoryRowLoopFixedPermutation p.2

theorem oddFredholmIntervalCrossingFixed_diagonal_commute
    (i : Fin 2) (S : AdjointableMap B E E) :
    Commute (oddFredholmIntervalCrossingFixed i) (countableModuleDiagonal S) := by
  fin_cases i
  · exact oddKTheoryRowSign_diagonal_commute S
  · exact oddKTheoryRowZeroProjection_diagonal_commute S

theorem oddFredholmIntervalCrossingFixed_coordinateRule
    (i : Fin 2) (m : ℤ) (b : E) :
    oddFredholmIntervalCrossingFixed (B := B) (E := E) i (oddKTheoryRowIntegerInclusion m b) =
      oddKTheoryRowIntegerInclusion (oddFredholmIntervalCrossingTarget i m)
        (oddFredholmIntervalCrossingWeight i m • b) := by
  fin_cases i
  · change oddKTheoryRowSignOperator (B := B) (E := E)
      (oddKTheoryRowIntegerInclusion m b) =
        oddKTheoryRowIntegerInclusion m (oddKTheoryRowIntegerSign m • b)
    rw [oddKTheoryRowSignOperator_inclusion]
    exact ((oddKTheoryRowIntegerInclusion (B := B) (E := E) m).toCLM.map_smul
      (oddKTheoryRowIntegerSign m) b).symm
  · change oddKTheoryRowZeroProjection (B := B) (E := E)
      (oddKTheoryRowIntegerInclusion m b) =
        oddKTheoryRowIntegerInclusion 0 ((if m = 0 then (1 : ℂ) else 0) • b)
    rw [oddKTheoryRowZeroProjection_inclusion]
    by_cases hm : m = 0
    · subst m
      simp only [if_true, one_smul]
    · simp only [if_neg hm, zero_smul, map_zero]

theorem oddFredholmIntervalRawFixed_coordinateRule
    (p : OddFredholmIntervalRawTerm) (m : ℤ) (b : E) :
    oddFredholmIntervalRawFixed (B := B) (E := E) p (oddKTheoryRowIntegerInclusion m b) =
      oddKTheoryRowIntegerInclusion (oddFredholmIntervalRawTarget p m)
        (oddFredholmIntervalRawWeight p m • b) := by
  simp only [oddFredholmIntervalRawFixed, AdjointableMap.mul_apply,
    oddKTheoryRowLoopFixedPermutation_coordinateRule,
    oddFredholmIntervalCrossingFixed_coordinateRule,
    oddKTheoryRowLoopFixedPermutation_star_coordinateRule,
    oddFredholmIntervalRawTarget, oddFredholmIntervalRawWeight]

/-- The genuine adjoint finite formula after moving its fixed adjoints
across the actual diagonal coefficient action. -/
theorem oddFredholmFiniteRowFormula_star {X κ : Type*} [TopologicalSpace X] [Fintype κ]
    (φ : C(X, ℂ) →⋆ₐ[ℂ] AdjointableMap B E E)
    (f : κ → C(X, ℂ)) (A : κ → OddKTheoryCountableOperator B E)
    (hcomm : ∀ i, Commute (star (A i)) (countableModuleDiagonal (φ (star (f i))))) :
    star (oddKTheoryFiniteRowFormula φ f A) =
      oddKTheoryFiniteRowFormula φ (fun i => star (f i)) (fun i => star (A i)) := by
  classical
  unfold oddKTheoryFiniteRowFormula
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hdiag : star (countableModuleDiagonal (φ (f i))) =
      countableModuleDiagonal (φ (star (f i))) := by
    change star (oddKTheoryCountableDiagonalHom (B := B) (E := E) (φ (f i))) =
      oddKTheoryCountableDiagonalHom (B := B) (E := E) (φ (star (f i)))
    exact ((congrArg (oddKTheoryCountableDiagonalHom (B := B) (E := E))
      (map_star φ (f i))).trans
        (map_star (oddKTheoryCountableDiagonalHom (B := B) (E := E)) (φ (f i)))).symm
  rw [star_mul, hdiag]
  exact (hcomm i).eq

/-- The raw finite formula is literally V*TV on the actual completed module. -/
theorem oddFredholmIntervalRawFormula_conjugation
    (φ : C(OddFredholmInterval, ℂ) →⋆ₐ[ℂ] AdjointableMap B E E) :
    oddKTheoryFiniteRowFormula φ oddFredholmIntervalRawCoefficient oddFredholmIntervalRawFixed =
      star (oddKTheoryFiniteRowFormula φ oddFredholmIntervalPermutationCoefficient
        oddKTheoryRowLoopFixedPermutation) *
          oddKTheoryFiniteRowFormula φ oddFredholmIntervalCrossingCoefficient
            oddFredholmIntervalCrossingFixed *
              oddKTheoryFiniteRowFormula φ oddFredholmIntervalPermutationCoefficient
                oddKTheoryRowLoopFixedPermutation := by
  rw [oddFredholmFiniteRowFormula_star φ oddFredholmIntervalPermutationCoefficient
    oddKTheoryRowLoopFixedPermutation (fun i =>
      oddKTheoryRowLoopFixedPermutation_star_diagonal_commute i _)]
  rw [oddKTheoryFiniteRowFormula_mul φ _ _ _ _ (fun i _ =>
    oddKTheoryRowLoopFixedPermutation_star_diagonal_commute i _)]
  rw [oddKTheoryFiniteRowFormula_mul φ _ _ _ _ (fun p _ =>
    (oddKTheoryRowLoopFixedPermutation_star_diagonal_commute p.1 _).mul_left
      (oddFredholmIntervalCrossingFixed_diagonal_commute p.2 _))]
  rfl

end ActualRows

section ScalarEntries

local instance oddFredholmIntervalRowFormulaScalarOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance oddFredholmIntervalRowFormulaScalarStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

def oddFredholmIntervalScalarRowAction (r : OddFredholmInterval) :
    C(OddFredholmInterval, ℂ) →⋆ₐ[ℂ] AdjointableMap ℂ ℂᵐᵒᵖ ℂᵐᵒᵖ :=
  (StarAlgHom.ofId ℂ (AdjointableMap ℂ ℂᵐᵒᵖ ℂᵐᵒᵖ)).comp
    (ContinuousMap.evalStarAlgHom ℂ ℂ r)

theorem oddFredholmIntervalScalarRowAction_diagonal (r : OddFredholmInterval)
    (f : C(OddFredholmInterval, ℂ)) :
    countableModuleDiagonal (oddFredholmIntervalScalarRowAction r f) =
      (f r) • (1 : OddKTheoryCountableOperator ℂ ℂᵐᵒᵖ) := by
  change countableModuleDiagonal (algebraMap ℂ (AdjointableMap ℂ ℂᵐᵒᵖ ℂᵐᵒᵖ) (f r)) = _
  rw [Algebra.algebraMap_eq_smul_one, oddKTheoryCountableDiagonal_smul,
    oddKTheoryCountableDiagonal_one]

theorem oddFredholmIntervalScalarRowAction_apply (r : OddFredholmInterval)
    (f : C(OddFredholmInterval, ℂ)) (b : ℂᵐᵒᵖ) :
    oddFredholmIntervalScalarRowAction r f b = (f r) • b := by
  change (algebraMap ℂ (AdjointableMap ℂ ℂᵐᵒᵖ ℂᵐᵒᵖ) (f r)) b = _
  rw [Algebra.algebraMap_eq_smul_one, AdjointableMap.coe_smul_apply, AdjointableMap.one_apply]

theorem oddFredholmIntervalRawFormula_scalar (r : OddFredholmInterval) :
    oddKTheoryFiniteRowFormula (oddFredholmIntervalScalarRowAction r)
      oddFredholmIntervalRawCoefficient oddFredholmIntervalRawFixed =
        oddKTheoryRowUniversalFredholmLoop (B := ℂ) (E := ℂᵐᵒᵖ)
          (oddFredholmIntervalParameter r) := by
  rw [oddFredholmIntervalRawFormula_conjugation]
  have hV : oddKTheoryFiniteRowFormula (B := ℂ) (E := ℂᵐᵒᵖ)
      (oddFredholmIntervalScalarRowAction r) oddFredholmIntervalPermutationCoefficient
      (oddKTheoryRowLoopFixedPermutation (B := ℂ) (E := ℂᵐᵒᵖ)) =
        (oddKTheoryRowLoopConjugator (B := ℂ) (E := ℂᵐᵒᵖ) (oddFredholmIntervalParameter r) :
          OddKTheoryCountableOperator ℂ ℂᵐᵒᵖ) := by
    simp only [oddKTheoryFiniteRowFormula, oddFredholmIntervalScalarRowAction_diagonal,
      oddFredholmIntervalPermutationCoefficient, smul_mul_assoc, one_mul]
    exact (oddKTheoryRowLoopConjugator_finiteExpansion (B := ℂ) (E := ℂᵐᵒᵖ)
      (oddFredholmIntervalParameter r)).symm
  have hT : oddKTheoryFiniteRowFormula (B := ℂ) (E := ℂᵐᵒᵖ)
      (oddFredholmIntervalScalarRowAction r) oddFredholmIntervalCrossingCoefficient
      (oddFredholmIntervalCrossingFixed (B := ℂ) (E := ℂᵐᵒᵖ)) =
        oddKTheoryRowCrossingOperator (B := ℂ) (E := ℂᵐᵒᵖ)
          (oddFredholmIntervalParameter r) := by
    simp only [oddKTheoryFiniteRowFormula, Fin.sum_univ_two,
      oddFredholmIntervalCrossingCoefficient, oddFredholmIntervalCrossingFixed,
      Matrix.cons_val_zero, oddFredholmIntervalScalarRowAction_diagonal,
      ContinuousMap.one_apply, oddFredholmIntervalCoordinate,
      one_smul, one_mul, smul_mul_assoc]
    have hcoefficient : ((r : ℝ) : ℂ) + 1 =
        2 * (oddFredholmIntervalParameter r : ℂ) := by
      unfold oddFredholmIntervalParameter
      push_cast
      ring
    change oddKTheoryRowSignOperator (B := ℂ) (E := ℂᵐᵒᵖ) +
      (((r : ℝ) : ℂ) + 1) • oddKTheoryRowZeroProjection =
        oddKTheoryRowSignOperator (B := ℂ) (E := ℂᵐᵒᵖ) +
          (2 * (oddFredholmIntervalParameter r : ℂ)) • oddKTheoryRowZeroProjection
    rw [hcoefficient]
  rw [hV, hT]
  rfl

theorem oddFredholmIntervalPeriodicCoefficient_apply (i : OddKTheoryLoopTerm)
    (r : OddFredholmInterval) :
    oddFredholmIntervalPeriodicCoefficient i r =
      match i with
      | .inl p => oddKTheoryLoopResidualCoefficient p (oddFredholmIntervalParameter r)
      | .inr (.inl _) => oddKTheoryLoopSignCoefficient (oddFredholmIntervalParameter r)
      | .inr (.inr j) => oddKTheoryLoopFiniteScalarCoefficients (oddFredholmIntervalParameter r) j := by
  cases i with
  | inl p =>
    exact oddKTheoryDescendScalarLoop_apply_interval
      (oddKTheoryLoopResidualCoefficient p) (continuous_oddKTheoryLoopResidualCoefficient p)
      (by simp) (oddFredholmIntervalParameter_mem r)
  | inr i =>
    cases i with
    | inl _ =>
      exact oddKTheoryDescendScalarLoop_apply_interval
        oddKTheoryLoopSignCoefficient continuous_oddKTheoryLoopSignCoefficient
        (by simp) (oddFredholmIntervalParameter_mem r)
    | inr i =>
      exact oddKTheoryDescendScalarLoop_apply_interval
        (fun t => oddKTheoryLoopFiniteScalarCoefficients t i)
        (continuous_oddKTheoryLoopFiniteScalarCoefficients i)
        (by simp) (oddFredholmIntervalParameter_mem r)

set_option maxHeartbeats 1200000 in
theorem oddFredholmIntervalPeriodicFormula_scalar (r : OddFredholmInterval) :
    oddKTheoryFiniteRowFormula (oddFredholmIntervalScalarRowAction r)
      oddFredholmIntervalPeriodicCoefficient oddKTheoryRowLoopTermOperator =
        oddKTheoryRowUniversalFredholmLoop (B := ℂ) (E := ℂᵐᵒᵖ)
          (oddFredholmIntervalParameter r) := by
  calc
    _ = ∑ i : OddKTheoryLoopTerm, (oddFredholmIntervalPeriodicCoefficient i r) •
        oddKTheoryRowLoopTermOperator (B := ℂ) (E := ℂᵐᵒᵖ) i := by
      unfold oddKTheoryFiniteRowFormula
      apply Finset.sum_congr rfl
      intro i _
      rw [oddFredholmIntervalScalarRowAction_diagonal, smul_mul_assoc, one_mul]
    _ = _ := by
      simp only [Fintype.sum_sum_type, oddKTheoryRowLoopTermOperator,
        oddFredholmIntervalPeriodicCoefficient_apply, Fintype.sum_unique]
      simpa only [add_assoc] using
        (oddKTheoryRowUniversalFredholmLoop_fullPeriodicExpansion (B := ℂ) (E := ℂᵐᵒᵖ)
          (oddFredholmIntervalParameter r)).symm

/-- The actual scalar row module separates the common interval entries. -/
theorem oddFredholmInterval_raw_periodic_entries (n m : ℤ) :
    oddKTheoryFiniteCircleEntry oddFredholmIntervalRawCoefficient
      oddFredholmIntervalRawTarget oddFredholmIntervalRawWeight n m =
        oddKTheoryFiniteCircleEntry oddFredholmIntervalPeriodicCoefficient
          oddKTheoryLoopTermTarget oddKTheoryLoopTermWeight n m := by
  ext r
  have hentry {κ : Type} [Fintype κ] (f : κ → C(OddFredholmInterval, ℂ))
      (A : κ → OddKTheoryCountableOperator ℂ ℂᵐᵒᵖ)
      (target : κ → ℤ → ℤ) (weight : κ → ℤ → ℂ)
      (hA : ∀ i m (b : ℂᵐᵒᵖ), A i (oddKTheoryRowIntegerInclusion m b) =
        oddKTheoryRowIntegerInclusion (target i m) (weight i m • b)) :
      (oddKTheoryRowIntegerEvaluation n
        (oddKTheoryFiniteRowFormula (oddFredholmIntervalScalarRowAction r) f A
          (oddKTheoryRowIntegerInclusion m (1 : ℂᵐᵒᵖ)))).unop =
            oddKTheoryFiniteCircleEntry f target weight n m r := by
    rw [oddKTheoryFiniteRowFormula_entry (B := ℂ) (E := ℂᵐᵒᵖ) _ f A target weight hA,
      oddFredholmIntervalScalarRowAction_apply, MulOpposite.unop_smul, MulOpposite.unop_one]
    exact mul_one _
  calc
    oddKTheoryFiniteCircleEntry oddFredholmIntervalRawCoefficient
        oddFredholmIntervalRawTarget oddFredholmIntervalRawWeight n m r =
      (oddKTheoryRowIntegerEvaluation (B := ℂ) (E := ℂᵐᵒᵖ) n
        (oddKTheoryFiniteRowFormula (B := ℂ) (E := ℂᵐᵒᵖ)
          (oddFredholmIntervalScalarRowAction r) oddFredholmIntervalRawCoefficient
          (oddFredholmIntervalRawFixed (B := ℂ) (E := ℂᵐᵒᵖ))
          (oddKTheoryRowIntegerInclusion (B := ℂ) (E := ℂᵐᵒᵖ) m (1 : ℂᵐᵒᵖ)))).unop :=
      (hentry (κ := OddFredholmIntervalRawTerm) oddFredholmIntervalRawCoefficient
        (oddFredholmIntervalRawFixed (B := ℂ) (E := ℂᵐᵒᵖ))
        oddFredholmIntervalRawTarget oddFredholmIntervalRawWeight
        (oddFredholmIntervalRawFixed_coordinateRule (B := ℂ) (E := ℂᵐᵒᵖ))).symm
    _ = (oddKTheoryRowIntegerEvaluation (B := ℂ) (E := ℂᵐᵒᵖ) n
        (oddKTheoryFiniteRowFormula (B := ℂ) (E := ℂᵐᵒᵖ)
          (oddFredholmIntervalScalarRowAction r) oddFredholmIntervalPeriodicCoefficient
          (oddKTheoryRowLoopTermOperator (B := ℂ) (E := ℂᵐᵒᵖ))
          (oddKTheoryRowIntegerInclusion (B := ℂ) (E := ℂᵐᵒᵖ) m (1 : ℂᵐᵒᵖ)))).unop := by
      rw [oddFredholmIntervalRawFormula_scalar, oddFredholmIntervalPeriodicFormula_scalar]
    _ = oddKTheoryFiniteCircleEntry oddFredholmIntervalPeriodicCoefficient
        oddKTheoryLoopTermTarget oddKTheoryLoopTermWeight n m r :=
      hentry (κ := OddKTheoryLoopTerm) oddFredholmIntervalPeriodicCoefficient
        (oddKTheoryRowLoopTermOperator (B := ℂ) (E := ℂᵐᵒᵖ))
        oddKTheoryLoopTermTarget oddKTheoryLoopTermWeight
        (oddKTheoryRowLoopTermOperator_coordinateRule (B := ℂ) (E := ℂᵐᵒᵖ))

end ScalarEntries

section ActualTransfer

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- The concrete scalar endpoint equality transfers through actual interval CFC. -/
theorem oddFredholmIntervalRawFormula_eq_periodic
    (φ : C(OddFredholmInterval, ℂ) →⋆ₐ[ℂ] AdjointableMap B E E) :
    oddKTheoryFiniteRowFormula φ oddFredholmIntervalRawCoefficient oddFredholmIntervalRawFixed =
      oddKTheoryFiniteRowFormula φ oddFredholmIntervalPeriodicCoefficient oddKTheoryRowLoopTermOperator :=
  oddKTheoryFiniteRowFormula_transfer (B := B) (E := E) φ _ _ _ _
    (oddFredholmIntervalRawFixed_coordinateRule (B := B) (E := E))
    _ _ _ _ (oddKTheoryRowLoopTermOperator_coordinateRule (B := B) (E := E))
    oddFredholmInterval_raw_periodic_entries

end ActualTransfer
end BC4lean.KKTheory
