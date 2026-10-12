import BC4lean.OddKTheoryMatrixWeightedDefect

/-! # The actual coordinate intertwiner for the weighted defect map

The scalar square-defect eigenoperator identity transfers through actual
finite signed-coordinate entries for every continuous scalar function. It
proves F_u T(g)=T(Xg) for the already constructed bounded operator map T.
This closes the degree-one hypothesis of full weighted functional calculus;
no weighted map or intertwining equation is assumed to exist.
-/

noncomputable section
namespace BC4lean.KKTheory

section ScalarTransfer

local instance oddKTheoryWeightedDefectTransferScalarOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance oddKTheoryWeightedDefectTransferScalarStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

variable (K : Set ℂ)
  (hsegment : Set.range oddKTheoryLoopEigenvalue ⊆ K)

/-- On the scalar circle representative the clamped point has exactly the
actual crossing eigenvalue, including its genuine membership in K. -/
theorem oddKTheoryLoopClampedEigenvalue_coe_parameter (z : Circle) :
    (oddKTheoryLoopClampedEigenvalue K hsegment (oddKTheoryCircleLoopParameter z) : ℂ) =
      2 * (oddKTheoryCircleLoopParameter z : ℂ) - 1 := by
  change 2 * ((Set.projIcc 0 1 (by norm_num)
    (oddKTheoryCircleLoopParameter z) : ℝ) : ℂ) - 1 =
      2 * (oddKTheoryCircleLoopParameter z : ℂ) - 1
  rw [Set.projIcc_of_mem _ (oddKTheoryCircleLoopParameter_mem_Icc z)]

/-- Scalar evaluation of the actual weighted finite formula is the scalar
function value times the genuine infinite scalar-loop square defect. -/
theorem oddKTheoryFiniteRowFormula_scalar_weighted_defect (g : C(K, ℂ)) (z : Circle) :
    oddKTheoryFiniteRowFormula (oddKTheoryScalarRowAction z)
      (oddKTheoryLoopWeightedCircleEntry K hsegment g)
      (oddKTheoryRowLoopFixedFiniteOperator (B := ℂ) (E := ℂᵐᵒᵖ)) =
      g (oddKTheoryLoopClampedEigenvalue K hsegment (oddKTheoryCircleLoopParameter z)) •
        (oddKTheoryRowUniversalFredholmLoop (oddKTheoryCircleLoopParameter z) *
          oddKTheoryRowUniversalFredholmLoop (oddKTheoryCircleLoopParameter z) - 1) := by
  simp only [oddKTheoryFiniteRowFormula, oddKTheoryScalarRowAction_diagonal,
    smul_mul_assoc, one_mul, oddKTheoryLoopWeightedCircleEntry_apply,
    oddKTheoryLoopDefectCircleEntry, oddKTheoryDescendScalarLoop_apply]
  rw [oddKTheoryRowUniversalFredholmLoop_square_entryFormula, add_sub_cancel_left]
  simp only [Finset.smul_sum, smul_smul]

/-- The finite circle entry identity for multiplication of any weighted
square defect by the actual twenty-one-term scalar loop. -/
theorem oddKTheoryLoop_mul_weighted_defect_circle_entries
    (g : C(K, ℂ)) (n m : ℤ) :
    oddKTheoryFiniteCircleEntry
      (fun p : OddKTheoryLoopTerm × Fin 4 => oddKTheoryLoopTermCoefficient p.1 *
        oddKTheoryLoopWeightedCircleEntry K hsegment g p.2)
      (fun p _ => oddKTheoryLoopTermTarget p.1 (oddKTheoryLoopFiniteTarget p.2))
      (fun p r => oddKTheoryLoopTermWeight p.1 (oddKTheoryLoopFiniteTarget p.2) *
        (if r = oddKTheoryLoopFiniteSource p.2 then 1 else 0)) n m =
      oddKTheoryFiniteCircleEntry
        (oddKTheoryLoopWeightedCircleEntry K hsegment (((ContinuousMap.id ℂ).restrict K) * g))
        (fun i _ => oddKTheoryLoopFiniteTarget i)
        (fun i r => if r = oddKTheoryLoopFiniteSource i then 1 else 0) n m := by
  ext z
  let A := oddKTheoryRowLoopTermOperator (B := ℂ) (E := ℂᵐᵒᵖ)
  let C := oddKTheoryRowLoopFixedFiniteOperator (B := ℂ) (E := ℂᵐᵒᵖ)
  have hprod := fun p : OddKTheoryLoopTerm × Fin 4 =>
    oddKTheoryRowCoordinateRule_mul (A p.1) (C p.2)
      (oddKTheoryLoopTermTarget p.1) (fun _ => oddKTheoryLoopFiniteTarget p.2)
      (oddKTheoryLoopTermWeight p.1)
      (fun r => if r = oddKTheoryLoopFiniteSource p.2 then 1 else 0)
      (oddKTheoryRowLoopTermOperator_coordinateRule (B := ℂ) (E := ℂᵐᵒᵖ) p.1)
      (oddKTheoryRowLoopFixedFiniteOperator_coordinateRule (B := ℂ) (E := ℂᵐᵒᵖ) p.2)
  rw [← oddKTheoryFiniteRowFormula_scalar_entry _ (fun p => A p.1 * C p.2)
      _ _ hprod z n m,
    ← oddKTheoryFiniteRowFormula_scalar_entry _ C _ _
      oddKTheoryRowLoopFixedFiniteOperator_coordinateRule z n m]
  have hop : oddKTheoryFiniteRowFormula (oddKTheoryScalarRowAction z)
      (fun p : OddKTheoryLoopTerm × Fin 4 => oddKTheoryLoopTermCoefficient p.1 *
        oddKTheoryLoopWeightedCircleEntry K hsegment g p.2)
      (fun p => A p.1 * C p.2) =
      oddKTheoryFiniteRowFormula (oddKTheoryScalarRowAction z)
        (oddKTheoryLoopWeightedCircleEntry K hsegment (((ContinuousMap.id ℂ).restrict K) * g)) C := by
    rw [← oddKTheoryFiniteRowFormula_mul]
    · rw [oddKTheoryFiniteRowFormula_scalar_loop,
        oddKTheoryFiniteRowFormula_scalar_weighted_defect,
        oddKTheoryFiniteRowFormula_scalar_weighted_defect]
      simp only [ContinuousMap.mul_apply, ContinuousMap.restrict_apply, ContinuousMap.id_apply,
        oddKTheoryLoopClampedEigenvalue_coe_parameter]
      rw [mul_smul_comm, oddKTheoryRowUniversalFredholmLoop_mul_square_defect, smul_smul]
      congr 1
      ring
    · intro i j
      exact oddKTheoryRowLoopTermOperator_diagonal_commute i _
  rw [hop]

end ScalarTransfer

section ActualMatrixTransfer

variable {B ι : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype ι] [DecidableEq ι]
  (K : Set ℂ) [CompactSpace K]
  (hsegment : Set.range oddKTheoryLoopEigenvalue ⊆ K)
  (u : unitary (CStarMatrix ι ι (Unitization ℂ B)))

/-- The genuine matrix Fredholm operator intertwines the actual bounded
weighted entry map with the actual complex coordinate function. -/
theorem oddKTheoryMatrixWeightedDefectCLM_coordinate_intertwine (g : C(K, ℂ)) :
    oddKTheoryMatrixLoopPullback u * oddKTheoryMatrixWeightedDefectCLM K hsegment u g =
      oddKTheoryMatrixWeightedDefectCLM K hsegment u (((ContinuousMap.id ℂ).restrict K) * g) := by
  change oddKTheoryMatrixLoopPullback u *
    oddKTheoryFiniteRowFormula (oddKTheoryMatrixRowCircleAction u)
      (oddKTheoryLoopWeightedCircleEntry K hsegment g) oddKTheoryRowLoopFixedFiniteOperator =
    oddKTheoryFiniteRowFormula (oddKTheoryMatrixRowCircleAction u)
      (oddKTheoryLoopWeightedCircleEntry K hsegment (((ContinuousMap.id ℂ).restrict K) * g))
      oddKTheoryRowLoopFixedFiniteOperator
  rw [oddKTheoryMatrixLoopPullback_finiteFormula, oddKTheoryFiniteRowFormula_mul _ _ _ _ _
    (fun i _ => oddKTheoryRowLoopTermOperator_diagonal_commute i _)]
  have hprod := fun p : OddKTheoryLoopTerm × Fin 4 =>
    oddKTheoryRowCoordinateRule_mul
      (oddKTheoryRowLoopTermOperator (B := B) (E := FiniteStandardModule B ι) p.1)
      (oddKTheoryRowLoopFixedFiniteOperator p.2)
      (oddKTheoryLoopTermTarget p.1) (fun _ => oddKTheoryLoopFiniteTarget p.2)
      (oddKTheoryLoopTermWeight p.1)
      (fun r => if r = oddKTheoryLoopFiniteSource p.2 then 1 else 0)
      (oddKTheoryRowLoopTermOperator_coordinateRule (B := B) (E := FiniteStandardModule B ι) p.1)
      (oddKTheoryRowLoopFixedFiniteOperator_coordinateRule (B := B) (E := FiniteStandardModule B ι) p.2)
  exact oddKTheoryFiniteRowFormula_transfer (oddKTheoryMatrixRowCircleAction u) _ _ _ _ hprod
    (oddKTheoryLoopWeightedCircleEntry K hsegment (((ContinuousMap.id ℂ).restrict K) * g))
    oddKTheoryRowLoopFixedFiniteOperator (fun i _ => oddKTheoryLoopFiniteTarget i)
    (fun i r => if r = oddKTheoryLoopFiniteSource i then 1 else 0)
    oddKTheoryRowLoopFixedFiniteOperator_coordinateRule
    (oddKTheoryLoop_mul_weighted_defect_circle_entries K hsegment g)

end ActualMatrixTransfer
end BC4lean.KKTheory
