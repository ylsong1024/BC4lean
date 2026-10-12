import BC4lean.OddKTheoryStandardPrefixEquiv
import BC4lean.OddFredholmIdentityAugmentation

/-! # The actual finite matrix index in an aligned standard prefix

The prefix unitary identifies its genuine finite range with the standard
cutoff. A full scalar-identity finite matrix has exactly that compression.
Joint scalar and actual operator faithfulness identifies the chosen index
with the original matrix class, including for zero coefficient algebras.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]

local instance oddContinuationOddKTheoryStandardPrefixIndexLocalInstance01 (n : ℕ) : CompleteSpace (FiniteStandardModule B (Fin n)) := finiteStandardModule_complete
local instance oddContinuationOddKTheoryStandardPrefixIndexLocalInstance02 (n : ℕ) : CompleteSpace (HilbertModuleSum B (FiniteStandardModule B (Fin n))
    (StandardCountableHilbertModule B)) := hilbertModuleSum_complete

theorem oddKTheoryStandardPrefixEquiv_transport_firstProjection (n : ℕ) :
    (oddKTheoryStandardPrefixEquiv (B := B) n).transport
      (sumMap (1 : AdjointableMap B (FiniteStandardModule B (Fin n)) _) 0) =
        standardCountableCutoff n := by
  ext x
  change oddFredholmStandardFiniteInclusion n
    ((oddFredholmStandardFiniteInclusion n).adjoint x) = standardCountableCutoff n x
  exact congrArg (fun T => T x) (oddFredholmStandardFiniteInclusion_comp_adjoint n)

theorem oddKTheoryStandardPrefixEquiv_transport_tailProjection (n : ℕ) :
    (oddKTheoryStandardPrefixEquiv (B := B) n).transport
      (sumMap (0 : AdjointableMap B (FiniteStandardModule B (Fin n)) _) 1) =
        1 - standardCountableCutoff n := by
  have h : sumMap (0 : AdjointableMap B (FiniteStandardModule B (Fin n)) _) 1 =
      1 - sumMap 1 (0 : OddFredholmStandardOperator B) := by
    rw [← sumMap_one, ← sumMap_sub, sub_self, sub_zero]
  rw [h, HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_one,
    oddKTheoryStandardPrefixEquiv_transport_firstProjection]

def oddKTheoryStandardPrefixUnitary (n : ℕ)
    (v : unitary (AdjointableMap B (FiniteStandardModule B (Fin n)) (FiniteStandardModule B (Fin n)))) :
    unitary (OddFredholmStandardOperator B) :=
  oddKTheoryTransportOperatorUnitary (oddKTheoryStandardPrefixEquiv n) (oddKTheorySumOperatorUnitary v 1)

theorem oddKTheoryStandardPrefixUnitary_compact (n : ℕ)
    (v : unitary (AdjointableMap B (FiniteStandardModule B (Fin n)) (FiniteStandardModule B (Fin n))))
    (hv : IsModuleCompact ((v : AdjointableMap B (FiniteStandardModule B (Fin n)) _) - 1)) :
    IsModuleCompact ((oddKTheoryStandardPrefixUnitary n v : OddFredholmStandardOperator B) - 1) :=
  oddKTheoryTransportOperatorUnitary_compact _ _
    (oddKTheorySumOperatorUnitary_compact v 1 hv (by simpa only [sub_self] using IsModuleCompact.zero))

theorem oddKTheoryStandardPrefixUnitary_tail (n : ℕ)
    (v : unitary (AdjointableMap B (FiniteStandardModule B (Fin n)) (FiniteStandardModule B (Fin n)))) :
    (oddKTheoryStandardPrefixUnitary n v : OddFredholmStandardOperator B) *
      (1 - standardCountableCutoff n) = 1 - standardCountableCutoff n := by
  rw [← oddKTheoryStandardPrefixEquiv_transport_tailProjection]
  change (oddKTheoryStandardPrefixEquiv n).transport (sumMap (v : _) 1) *
    (oddKTheoryStandardPrefixEquiv n).transport (sumMap 0 1) = _
  rw [← HilbertModuleEquiv.transport_mul, ← sumMap_mul, mul_zero, one_mul]

theorem oddKTheoryStandardPrefixUnitary_compression (n : ℕ)
    (v : unitary (AdjointableMap B (FiniteStandardModule B (Fin n)) (FiniteStandardModule B (Fin n)))) :
    oddFredholmSupportedUnitaryCompression (oddKTheoryStandardPrefixUnitary n v) n
      (oddKTheoryStandardPrefixUnitary_tail n v) = v := by
  apply Subtype.ext
  ext x
  change (oddFredholmStandardFiniteInclusion n).adjoint
    ((oddKTheoryStandardPrefixEquiv n).transport (sumMap (v : _) 1)
      (oddFredholmStandardFiniteInclusion n x)) = (v : _) x
  rw [HilbertModuleEquiv.transport_apply,
    ← oddKTheoryStandardPrefixEquiv_inl n x, HilbertModuleEquiv.symm_apply_apply]
  simp only [sumMap_apply, sumMk_fst, sumMk_snd, AdjointableMap.one_apply,
    oddKTheoryStandardPrefixEquiv_inl]
  have h := congrArg (fun T => T ((v : _) x))
    (oddFredholmStandardFiniteInclusion_adjoint_comp_self (B := B) n)
  simpa only [AdjointableMap.comp_apply, AdjointableMap.id_apply] using h

theorem oddKTheoryStandardPrefixUnitary_matrixIndex (n : ℕ)
    (v : unitary (CStarMatrix (Fin n) (Fin n) (Unitization ℂ B)))
    (hv : unitizationScalarMatrix (v : CStarMatrix (Fin n) (Fin n) (Unitization ℂ B)) = 1) :
    oddFredholmStandardUnitaryIndex (oddKTheoryStandardPrefixUnitary n (oddKTheoryMatrixOperatorUnitary v))
      (oddKTheoryStandardPrefixUnitary_compact n _ (oddKTheoryMatrixOperatorUnitary_compact v hv)) =
        oddFredholmScalarIdentityUnitaryIndex v hv := by
  rw [oddFredholmStandardUnitaryIndex_eq_supported _ _ n (oddKTheoryStandardPrefixUnitary_tail n _)]
  have hm : oddFredholmSupportedFiniteUnitary
      (oddKTheoryStandardPrefixUnitary n (oddKTheoryMatrixOperatorUnitary v))
      (oddKTheoryStandardPrefixUnitary_compact n _ (oddKTheoryMatrixOperatorUnitary_compact v hv)) n
      (oddKTheoryStandardPrefixUnitary_tail n _) = v := by
    apply Subtype.ext
    apply unitizationMatrix_eq_of_scalar_and_operator_eq
    · exact (oddFredholmSupportedFiniteUnitary_scalar _ _ _ _).trans hv.symm
    · rw [oddFredholmSupportedFiniteUnitary, oddFredholmFiniteCompactUnitaryMatrix_operator]
      exact congrArg Subtype.val (oddKTheoryStandardPrefixUnitary_compression n _)
  rw [hm]

end BC4lean.KKTheory
