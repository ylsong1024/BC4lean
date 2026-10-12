import BC4lean.OddKTheoryFiniteMatrixRecovery
import BC4lean.OddFredholmOperatorK1Index

/-! # Finite exponential recovery in the actual nonunital OperatorK1 kernel

The concrete finite recovery homotopy keeps the full scalar matrix equal to
the identity. Its upper matrix therefore represents the same element of
the genuine scalar kernel `OperatorK1 B` as the original finite unitary.
No faithfulness of the unitized module representation is used.
-/

noncomputable section
namespace BC4lean.KKTheory

open unitInterval
open scoped Matrix CStarAlgebra
open BC4lean.OperatorKTheory

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

local instance oddContinuationOddKTheoryOperatorK1RecoveryLocalInstance01 : PartialOrder (Unitization ℂ B) := CStarAlgebra.spectralOrder _
local instance oddContinuationOddKTheoryOperatorK1RecoveryLocalInstance02 : StarOrderedRing (Unitization ℂ B) := CStarAlgebra.spectralOrderedRing _
local instance oddContinuationOddKTheoryOperatorK1RecoveryLocalInstance03 : PartialOrder ℂ := CStarAlgebra.spectralOrder _
local instance oddContinuationOddKTheoryOperatorK1RecoveryLocalInstance04 : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing _

omit [PartialOrder B] [StarOrderedRing B] in
theorem oddKTheoryRecoveryCircleEntry_scalar
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1)
    (s : I) (i j : Fin 2) :
    matrixMap (scalarQuotient B)
      (oddKTheoryCircleCFC u (oddKTheoryRecoveryCircleEntry s i j)) =
        if i = j then (1 : CStarMatrix ι ι ℂ) else 0 := by
  have h := oddKTheoryCircleCFC_map (matrixMap (scalarQuotient B))
    (map_continuous (matrixMap (scalarQuotient B))) u
    (1 : unitary (CStarMatrix ι ι ℂ)) hu (oddKTheoryRecoveryCircleEntry s i j)
  rw [oddKTheoryCircleCFC_one_algebraMap, oddKTheoryRecoveryCircleEntry_one] at h
  by_cases hij : i = j <;> simpa only [hij, if_true, if_false, map_one, map_zero] using h

omit [PartialOrder B] [StarOrderedRing B] in
/-- Every point of the actual finite norm path has full scalar matrix I. -/
theorem oddKTheoryRecoveryFiniteUnitary_scalar
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1)
    (s : I) :
    unitizationScalarMatrix
      (oddKTheoryRecoveryFiniteUnitary u s : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) (Unitization ℂ B)) = 1 := by
  have hscalar (a : Unitization ℂ B) : (scalarQuotient B) a = a.fst := rfl
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have h := congrArg (fun M : CStarMatrix ι ι ℂ => M i j)
        (oddKTheoryRecoveryCircleEntry_scalar u hu s 0 0)
      simpa [oddKTheoryRecoveryFiniteUnitary, oddKTheoryTwoBlockFlattenUnitary,
        oddKTheoryTwoBlockFlattenHom, matrixMap_apply, oddKTheoryRecoveryNestedUnitary_apply,
        unitizationScalarMatrix, CStarMatrix.one_apply, hscalar] using h
    | inr j =>
      have h := congrArg (fun M : CStarMatrix ι ι ℂ => M i j)
        (oddKTheoryRecoveryCircleEntry_scalar u hu s 0 1)
      simpa [oddKTheoryRecoveryFiniteUnitary, oddKTheoryTwoBlockFlattenUnitary,
        oddKTheoryTwoBlockFlattenHom, matrixMap_apply, oddKTheoryRecoveryNestedUnitary_apply,
        unitizationScalarMatrix, CStarMatrix.one_apply, hscalar] using h
  | inr i =>
    cases j with
    | inl j =>
      have h := congrArg (fun M : CStarMatrix ι ι ℂ => M i j)
        (oddKTheoryRecoveryCircleEntry_scalar u hu s 1 0)
      simpa [oddKTheoryRecoveryFiniteUnitary, oddKTheoryTwoBlockFlattenUnitary,
        oddKTheoryTwoBlockFlattenHom, matrixMap_apply, oddKTheoryRecoveryNestedUnitary_apply,
        unitizationScalarMatrix, CStarMatrix.one_apply, hscalar] using h
    | inr j =>
      have h := congrArg (fun M : CStarMatrix ι ι ℂ => M i j)
        (oddKTheoryRecoveryCircleEntry_scalar u hu s 1 1)
      simpa [oddKTheoryRecoveryFiniteUnitary, oddKTheoryTwoBlockFlattenUnitary,
        oddKTheoryTwoBlockFlattenHom, matrixMap_apply, oddKTheoryRecoveryNestedUnitary_apply,
        unitizationScalarMatrix, CStarMatrix.one_apply, hscalar] using h

omit [PartialOrder B] [StarOrderedRing B] in
theorem oddKTheoryFiniteExponentialRecovery_scalar
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    unitizationScalarMatrix
      (oddKTheoryFiniteExponentialRecovery u : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) (Unitization ℂ B)) = 1 :=
  oddKTheoryRecoveryFiniteUnitary_scalar u hu 1

omit [PartialOrder B] [StarOrderedRing B] in
set_option maxHeartbeats 8000000 in
/-- The four-entry finite exponential recovers the original actual
nonunital operator K1 element, including the full scalar-kernel proof. -/
theorem oddKTheoryFiniteExponentialRecovery_operatorK1
    (u : unitary (CStarMatrix ι ι (Unitization ℂ B)))
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    oddFredholmScalarIdentityUnitaryIndex (B := B) (ι := ι ⊕ ι)
      (oddKTheoryFiniteExponentialRecovery (A := Unitization ℂ B) (ι := ι) u)
      (oddKTheoryFiniteExponentialRecovery_scalar (B := B) (ι := ι) u hu) =
        oddFredholmScalarIdentityUnitaryIndex (B := B) (ι := ι) u hu := by
  apply Subtype.ext
  exact oddKTheoryFiniteExponentialRecovery_k1 u

end BC4lean.KKTheory
