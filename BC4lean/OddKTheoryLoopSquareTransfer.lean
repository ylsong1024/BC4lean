import BC4lean.OddKTheoryLoopCoordinateFormula

/-! # Genuine transfer of the universal-loop square identity

The actual scalar row module separates the common circle entry functions.
The scalar interval loop square identity therefore transfers through every
actual row-module coefficient action. At a matrix unitary this gives the
square defect of the genuine infinite row operator, rather than a formal
operator-valued tensor formula.
-/

noncomputable section
namespace BC4lean.KKTheory

abbrev OddKTheoryLoopDefectTerm := Unit ⊕ Fin 4

def oddKTheoryLoopDefectTermCoefficient : OddKTheoryLoopDefectTerm → C(Circle, ℂ)
  | .inl _ => 1
  | .inr i => oddKTheoryLoopDefectCircleEntry i

def oddKTheoryLoopDefectTermTarget : OddKTheoryLoopDefectTerm → ℤ → ℤ
  | .inl _, m => m
  | .inr i, _ => oddKTheoryLoopFiniteTarget i

def oddKTheoryLoopDefectTermWeight : OddKTheoryLoopDefectTerm → ℤ → ℂ
  | .inl _, _ => 1
  | .inr i, m => if m = oddKTheoryLoopFiniteSource i then 1 else 0

section ActualRows

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

def oddKTheoryRowLoopDefectTermOperator : OddKTheoryLoopDefectTerm → OddKTheoryCountableOperator B E
  | .inl _ => 1
  | .inr i => oddKTheoryRowLoopFixedFiniteOperator i

theorem oddKTheoryRowLoopDefectTermOperator_coordinateRule (i : OddKTheoryLoopDefectTerm)
    (m : ℤ) (b : E) :
    oddKTheoryRowLoopDefectTermOperator (B := B) (E := E) i (oddKTheoryRowIntegerInclusion m b) =
      oddKTheoryRowIntegerInclusion (oddKTheoryLoopDefectTermTarget i m)
        (oddKTheoryLoopDefectTermWeight i m • b) := by
  cases i with
  | inl _ => simp [oddKTheoryRowLoopDefectTermOperator,
      oddKTheoryLoopDefectTermTarget, oddKTheoryLoopDefectTermWeight]
  | inr i => exact oddKTheoryRowLoopFixedFiniteOperator_coordinateRule (B := B) (E := E) i m b

end ActualRows

section ScalarSeparation

local instance oddKTheoryLoopSquareTransferScalarOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance oddKTheoryLoopSquareTransferScalarStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-- Scalar evaluation followed by the actual scalar action on the standard
one-row coefficient module. -/
def oddKTheoryScalarRowAction (z : Circle) : C(Circle, ℂ) →⋆ₐ[ℂ]
    AdjointableMap ℂ ℂᵐᵒᵖ ℂᵐᵒᵖ :=
  (StarAlgHom.ofId ℂ (AdjointableMap ℂ ℂᵐᵒᵖ ℂᵐᵒᵖ)).comp
    (ContinuousMap.evalStarAlgHom ℂ ℂ z)

@[simp] theorem oddKTheoryScalarRowAction_apply (z : Circle) (f : C(Circle, ℂ))
    (b : ℂᵐᵒᵖ) :
    oddKTheoryScalarRowAction z f b = (f z) • b := by
  change (algebraMap ℂ (AdjointableMap ℂ ℂᵐᵒᵖ ℂᵐᵒᵖ) (f z)) b = _
  rw [Algebra.algebraMap_eq_smul_one, AdjointableMap.coe_smul_apply, AdjointableMap.one_apply]

@[simp] theorem oddKTheoryScalarRowAction_diagonal (z : Circle) (f : C(Circle, ℂ)) :
    countableModuleDiagonal (oddKTheoryScalarRowAction z f) =
      (f z) • (1 : OddKTheoryCountableOperator ℂ ℂᵐᵒᵖ) := by
  change countableModuleDiagonal (algebraMap ℂ (AdjointableMap ℂ ℂᵐᵒᵖ ℂᵐᵒᵖ) (f z)) = _
  rw [Algebra.algebraMap_eq_smul_one, oddKTheoryCountableDiagonal_smul,
    oddKTheoryCountableDiagonal_one]

/-- The unit coefficient in the actual scalar row module separates every
common circle entry function at every circle point. -/
theorem oddKTheoryFiniteRowFormula_scalar_entry {κ : Type*} [Fintype κ]
    (f : κ → C(Circle, ℂ)) (A : κ → OddKTheoryCountableOperator ℂ ℂᵐᵒᵖ)
    (target : κ → ℤ → ℤ) (weight : κ → ℤ → ℂ)
    (hA : ∀ i m (b : ℂᵐᵒᵖ), A i (oddKTheoryRowIntegerInclusion m b) =
      oddKTheoryRowIntegerInclusion (target i m) (weight i m • b))
    (z : Circle) (n m : ℤ) :
    (oddKTheoryRowIntegerEvaluation n
      (oddKTheoryFiniteRowFormula (oddKTheoryScalarRowAction z) f A
        (oddKTheoryRowIntegerInclusion m (1 : ℂᵐᵒᵖ)))).unop =
      oddKTheoryFiniteCircleEntry f target weight n m z := by
  rw [oddKTheoryFiniteRowFormula_entry _ f A target weight hA,
    oddKTheoryScalarRowAction_apply, MulOpposite.unop_smul, MulOpposite.unop_one]
  exact mul_one _

/-- Scalar evaluation of the twenty-one-term formula recovers the genuine
universal interval loop at the actual half-open circle representative. -/
theorem oddKTheoryFiniteRowFormula_scalar_loop (z : Circle) :
    oddKTheoryFiniteRowFormula (oddKTheoryScalarRowAction z) oddKTheoryLoopTermCoefficient
      (oddKTheoryRowLoopTermOperator (B := ℂ) (E := ℂᵐᵒᵖ)) =
        oddKTheoryRowUniversalFredholmLoop (oddKTheoryCircleLoopParameter z) := by
  unfold oddKTheoryFiniteRowFormula
  simp only [Fintype.sum_sum_type, oddKTheoryLoopTermCoefficient,
    oddKTheoryRowLoopTermOperator, oddKTheoryScalarRowAction_diagonal,
    Fintype.sum_unique, smul_mul_assoc, one_mul]
  simp only [oddKTheoryLoopResidualCircleCoefficient, oddKTheoryLoopSignCircleCoefficient,
    oddKTheoryLoopFiniteCircleCoefficient, oddKTheoryDescendScalarLoop_apply]
  simpa only [add_assoc] using
    (oddKTheoryRowUniversalFredholmLoop_fullPeriodicExpansion _).symm

/-- The identity and the four descended defect entries similarly recover
the actual scalar square of the universal interval loop. -/
theorem oddKTheoryFiniteRowFormula_scalar_defect (z : Circle) :
    oddKTheoryFiniteRowFormula (oddKTheoryScalarRowAction z) oddKTheoryLoopDefectTermCoefficient
      (oddKTheoryRowLoopDefectTermOperator (B := ℂ) (E := ℂᵐᵒᵖ)) =
        oddKTheoryRowUniversalFredholmLoop (oddKTheoryCircleLoopParameter z) *
          oddKTheoryRowUniversalFredholmLoop (oddKTheoryCircleLoopParameter z) := by
  unfold oddKTheoryFiniteRowFormula
  simp only [Fintype.sum_sum_type, oddKTheoryLoopDefectTermCoefficient,
    oddKTheoryRowLoopDefectTermOperator, oddKTheoryScalarRowAction_diagonal,
    Fintype.sum_unique, ContinuousMap.one_apply, one_smul, one_mul,
    smul_mul_assoc, oddKTheoryLoopDefectCircleEntry, oddKTheoryDescendScalarLoop_apply]
  exact (oddKTheoryRowUniversalFredholmLoop_square_entryFormula _).symm

/-- Equality of the common circle entries of the finite square formula and
the identity plus the four genuine periodic defect entries. -/
theorem oddKTheoryLoop_square_circle_entries (n m : ℤ) :
    oddKTheoryFiniteCircleEntry
      (fun p : OddKTheoryLoopTerm × OddKTheoryLoopTerm =>
        oddKTheoryLoopTermCoefficient p.1 * oddKTheoryLoopTermCoefficient p.2)
      (fun p k => oddKTheoryLoopTermTarget p.1 (oddKTheoryLoopTermTarget p.2 k))
      (fun p k => oddKTheoryLoopTermWeight p.1 (oddKTheoryLoopTermTarget p.2 k) *
        oddKTheoryLoopTermWeight p.2 k) n m =
      oddKTheoryFiniteCircleEntry oddKTheoryLoopDefectTermCoefficient
        oddKTheoryLoopDefectTermTarget oddKTheoryLoopDefectTermWeight n m := by
  ext z
  let A := oddKTheoryRowLoopTermOperator (B := ℂ) (E := ℂᵐᵒᵖ)
  have hA := oddKTheoryRowLoopTermOperator_coordinateRule (B := ℂ) (E := ℂᵐᵒᵖ)
  have hprod := fun p : OddKTheoryLoopTerm × OddKTheoryLoopTerm =>
    oddKTheoryRowCoordinateRule_mul (A p.1) (A p.2)
      (oddKTheoryLoopTermTarget p.1) (oddKTheoryLoopTermTarget p.2)
      (oddKTheoryLoopTermWeight p.1) (oddKTheoryLoopTermWeight p.2)
      (hA p.1) (hA p.2)
  rw [← oddKTheoryFiniteRowFormula_scalar_entry _ (fun p => A p.1 * A p.2)
      _ _ hprod z n m,
    ← oddKTheoryFiniteRowFormula_scalar_entry _
      (oddKTheoryRowLoopDefectTermOperator (B := ℂ) (E := ℂᵐᵒᵖ)) _ _
      oddKTheoryRowLoopDefectTermOperator_coordinateRule z n m]
  have hop : oddKTheoryFiniteRowFormula (oddKTheoryScalarRowAction z)
      (fun p : OddKTheoryLoopTerm × OddKTheoryLoopTerm =>
        oddKTheoryLoopTermCoefficient p.1 * oddKTheoryLoopTermCoefficient p.2)
      (fun p => A p.1 * A p.2) =
      oddKTheoryFiniteRowFormula (oddKTheoryScalarRowAction z)
        oddKTheoryLoopDefectTermCoefficient
        (oddKTheoryRowLoopDefectTermOperator (B := ℂ) (E := ℂᵐᵒᵖ)) := by
    rw [← oddKTheoryFiniteRowFormula_square]
    · rw [oddKTheoryFiniteRowFormula_scalar_loop, oddKTheoryFiniteRowFormula_scalar_defect]
    · intro i j
      exact oddKTheoryRowLoopTermOperator_diagonal_commute i _
  rw [hop]

end ScalarSeparation

section ActualTransfer

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

/-- The exact universal square identity after any genuine row coefficient
circle action. It does not assume a tensor product or a compact projection. -/
theorem oddKTheoryFiniteRowFormula_loop_square
    (φ : C(Circle, ℂ) →⋆ₐ[ℂ] AdjointableMap B E E) :
    oddKTheoryFiniteRowFormula φ oddKTheoryLoopTermCoefficient oddKTheoryRowLoopTermOperator *
        oddKTheoryFiniteRowFormula φ oddKTheoryLoopTermCoefficient oddKTheoryRowLoopTermOperator =
      1 + ∑ i : Fin 4, countableModuleDiagonal (φ (oddKTheoryLoopDefectCircleEntry i)) *
        oddKTheoryRowLoopFixedFiniteOperator i := by
  rw [oddKTheoryFiniteRowFormula_square φ oddKTheoryLoopTermCoefficient
    oddKTheoryRowLoopTermOperator (fun i _ => oddKTheoryRowLoopTermOperator_diagonal_commute i _)]
  have hprod := fun p : OddKTheoryLoopTerm × OddKTheoryLoopTerm =>
    oddKTheoryRowCoordinateRule_mul
      (oddKTheoryRowLoopTermOperator (B := B) (E := E) p.1)
      (oddKTheoryRowLoopTermOperator p.2)
      (oddKTheoryLoopTermTarget p.1) (oddKTheoryLoopTermTarget p.2)
      (oddKTheoryLoopTermWeight p.1) (oddKTheoryLoopTermWeight p.2)
      (oddKTheoryRowLoopTermOperator_coordinateRule p.1)
      (oddKTheoryRowLoopTermOperator_coordinateRule p.2)
  rw [oddKTheoryFiniteRowFormula_transfer φ _ _ _ _ hprod
    oddKTheoryLoopDefectTermCoefficient oddKTheoryRowLoopDefectTermOperator
    oddKTheoryLoopDefectTermTarget oddKTheoryLoopDefectTermWeight
    oddKTheoryRowLoopDefectTermOperator_coordinateRule oddKTheoryLoop_square_circle_entries]
  simp only [oddKTheoryFiniteRowFormula, Fintype.sum_sum_type,
    oddKTheoryLoopDefectTermCoefficient, oddKTheoryRowLoopDefectTermOperator,
    Fintype.sum_unique, map_one, oddKTheoryCountableDiagonal_one, one_mul]

end ActualTransfer
end BC4lean.KKTheory
