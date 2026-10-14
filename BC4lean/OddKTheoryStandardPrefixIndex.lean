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

omit [TopologicalSpace.SeparableSpace B] in
theorem oddKTheoryStandardPrefixEquiv_transport_firstProjection (n : ℕ) :
    (oddKTheoryStandardPrefixEquiv (B := B) n).transport
      (sumMap (1 : AdjointableMap B (FiniteStandardModule B (Fin n)) _) 0) =
        standardCountableCutoff n := by
  have hi : (oddKTheoryStandardPrefixEquiv (B := B) n).toAdjointable.comp
      (sumInl (B := B) (E := FiniteStandardModule B (Fin n))
        (F := StandardCountableHilbertModule B)) = oddFredholmStandardFiniteInclusion (B := B) n := by
    apply AdjointableMap.ext
    intro x
    exact oddKTheoryStandardPrefixEquiv_inl (B := B) n x
  calc
    _ = ((oddKTheoryStandardPrefixEquiv (B := B) n).toAdjointable.comp
        (sumInl (B := B) (E := FiniteStandardModule B (Fin n))
          (F := StandardCountableHilbertModule B))).comp
        (((oddKTheoryStandardPrefixEquiv (B := B) n).toAdjointable.comp
          (sumInl (B := B) (E := FiniteStandardModule B (Fin n))
            (F := StandardCountableHilbertModule B))).adjoint) := by
      apply AdjointableMap.ext
      intro x
      simp only [HilbertModuleEquiv.transport_apply, AdjointableMap.comp_apply,
        AdjointableMap.adjoint_comp, sumInl_adjoint, HilbertModuleEquiv.toAdjointable_adjoint,
        HilbertModuleEquiv.toAdjointable_apply, sumFst_apply, sumInl_apply, sumMap_apply,
        AdjointableMap.one_apply, AdjointableMap.coe_zero_apply]
    _ = standardCountableCutoff (B := B) n := by
      rw [hi]
      exact oddFredholmStandardFiniteInclusion_comp_adjoint (B := B) n

omit [TopologicalSpace.SeparableSpace B] in
theorem oddKTheoryStandardPrefixEquiv_transport_tailProjection (n : ℕ) :
    (oddKTheoryStandardPrefixEquiv (B := B) n).transport
      (sumMap (0 : AdjointableMap B (FiniteStandardModule B (Fin n)) _) 1) =
        1 - standardCountableCutoff n := by
  have h : sumMap (0 : AdjointableMap B (FiniteStandardModule B (Fin n))
        (FiniteStandardModule B (Fin n))) (1 : OddFredholmStandardOperator B) =
      (1 : AdjointableMap B (HilbertModuleSum B (FiniteStandardModule B (Fin n))
        (StandardCountableHilbertModule B))
        (HilbertModuleSum B (FiniteStandardModule B (Fin n)) (StandardCountableHilbertModule B))) -
      sumMap (1 : AdjointableMap B (FiniteStandardModule B (Fin n))
        (FiniteStandardModule B (Fin n))) (0 : OddFredholmStandardOperator B) := by
    have hone := sumMap_one (B := B) (E := FiniteStandardModule B (Fin n))
      (F := StandardCountableHilbertModule B)
    rw [← hone, ← sumMap_sub, sub_self, sub_zero]
  rw [h, HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_one,
    oddKTheoryStandardPrefixEquiv_transport_firstProjection]

def oddKTheoryStandardPrefixUnitary (n : ℕ)
    (v : unitary (AdjointableMap B (FiniteStandardModule B (Fin n)) (FiniteStandardModule B (Fin n)))) :
    unitary (OddFredholmStandardOperator B) :=
  oddKTheoryTransportOperatorUnitary (oddKTheoryStandardPrefixEquiv n) (oddKTheorySumOperatorUnitary v 1)

omit [TopologicalSpace.SeparableSpace B] in
theorem oddKTheoryStandardPrefixUnitary_compact (n : ℕ)
    (v : unitary (AdjointableMap B (FiniteStandardModule B (Fin n)) (FiniteStandardModule B (Fin n))))
    (hv : IsModuleCompact ((v : AdjointableMap B (FiniteStandardModule B (Fin n)) (FiniteStandardModule B (Fin n))) - 1)) :
    IsModuleCompact ((oddKTheoryStandardPrefixUnitary n v : OddFredholmStandardOperator B) - 1) :=
  oddKTheoryTransportOperatorUnitary_compact _ _
    (oddKTheorySumOperatorUnitary_compact v 1 hv (by simpa only [OneMemClass.coe_one, sub_self] using
      (IsModuleCompact.zero : IsModuleCompact (0 : OddFredholmStandardOperator B))))

omit [TopologicalSpace.SeparableSpace B] in
theorem oddKTheoryStandardPrefixUnitary_tail (n : ℕ)
    (v : unitary (AdjointableMap B (FiniteStandardModule B (Fin n)) (FiniteStandardModule B (Fin n)))) :
    (oddKTheoryStandardPrefixUnitary n v : OddFredholmStandardOperator B) *
      (1 - standardCountableCutoff n) = 1 - standardCountableCutoff n := by
  rw [← oddKTheoryStandardPrefixEquiv_transport_tailProjection]
  change (oddKTheoryStandardPrefixEquiv (B := B) n).transport (sumMap (v : AdjointableMap B (FiniteStandardModule B (Fin n)) (FiniteStandardModule B (Fin n))) (1 : OddFredholmStandardOperator B)) *
    (oddKTheoryStandardPrefixEquiv (B := B) n).transport (sumMap (0 : AdjointableMap B (FiniteStandardModule B (Fin n)) (FiniteStandardModule B (Fin n))) (1 : OddFredholmStandardOperator B)) = _
  rw [← HilbertModuleEquiv.transport_mul, ← sumMap_mul, mul_zero, one_mul]

omit [TopologicalSpace.SeparableSpace B] in
theorem oddKTheoryStandardPrefixUnitary_compression (n : ℕ)
    (v : unitary (AdjointableMap B (FiniteStandardModule B (Fin n)) (FiniteStandardModule B (Fin n)))) :
    oddFredholmSupportedUnitaryCompression (oddKTheoryStandardPrefixUnitary n v) n
      (oddKTheoryStandardPrefixUnitary_tail n v) = v := by
  apply Subtype.ext
  apply AdjointableMap.ext
  intro x
  change (oddFredholmStandardFiniteInclusion (B := B) n).adjoint
    ((oddKTheoryStandardPrefixEquiv (B := B) n).transport (sumMap (v : AdjointableMap B (FiniteStandardModule B (Fin n)) (FiniteStandardModule B (Fin n))) (1 : OddFredholmStandardOperator B))
      (oddFredholmStandardFiniteInclusion n x)) = (v : AdjointableMap B (FiniteStandardModule B (Fin n)) (FiniteStandardModule B (Fin n))) x
  rw [HilbertModuleEquiv.transport_apply,
    ← oddKTheoryStandardPrefixEquiv_inl n x, HilbertModuleEquiv.symm_apply_apply]
  simp only [sumMap_apply, sumMk_fst, sumMk_snd, AdjointableMap.one_apply,
    oddKTheoryStandardPrefixEquiv_inl]
  have h := congrArg (fun T => T ((v : AdjointableMap B (FiniteStandardModule B (Fin n)) (FiniteStandardModule B (Fin n))) x))
    (oddFredholmStandardFiniteInclusion_adjoint_comp_self (B := B) n)
  simpa only [AdjointableMap.comp_apply, AdjointableMap.id_apply] using h

omit [TopologicalSpace.SeparableSpace B] in
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
    · rw [oddFredholmSupportedFiniteUnitary, oddFredholmFiniteCompactUnitary, oddFredholmFiniteCompactUnitaryMatrix_operator]
      exact congrArg Subtype.val (oddKTheoryStandardPrefixUnitary_compression n _)
  simp only [hm]

end BC4lean.KKTheory
