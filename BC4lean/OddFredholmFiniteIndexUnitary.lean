import BC4lean.OddKTheoryCountableDiagonal
import BC4lean.OddFredholmPolarTail
import BC4lean.OddFredholmStandardCoordinates

/-! # Actual finite matrix unitaries from compact standard-module unitaries

Polar correction of the genuine strong cutoff retains the exact identity
tail. Its finite coordinate compression is therefore an actual unitary.
Compact coordinate extraction produces a genuine matrix over the forced
unitization with full scalar quotient I; joint scalar/operator faithfulness
proves both matrix unitary identities even for nonunital or zero B.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped Ring CStarAlgebra

section FiniteReflection

variable {B ι : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype ι] [DecidableEq ι]

def oddFredholmFiniteCompactUnitaryMatrix
    (v : unitary (AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι)))
    (hv : IsModuleCompact ((v : AdjointableMap B (FiniteStandardModule B ι)
      (FiniteStandardModule B ι)) - 1)) : CStarMatrix ι ι (Unitization ℂ B) :=
  1 + unitizationCoefficientMatrix (finiteModuleCompactMatrix
    ((v : AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι)) - 1) hv)

theorem oddFredholmFiniteCompactUnitaryMatrix_scalar
    (v : unitary (AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι)))
    (hv : IsModuleCompact ((v : AdjointableMap B (FiniteStandardModule B ι)
      (FiniteStandardModule B ι)) - 1)) :
    unitizationScalarMatrix (oddFredholmFiniteCompactUnitaryMatrix v hv) = 1 := by
  rw [oddFredholmFiniteCompactUnitaryMatrix, unitizationScalarMatrix_add,
    unitizationScalarMatrix_coefficient, add_zero]
  change OperatorKTheory.matrixMap (OperatorKTheory.scalarQuotient B) 1 = 1
  exact map_one _

theorem oddFredholmFiniteCompactUnitaryMatrix_operator
    (v : unitary (AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι)))
    (hv : IsModuleCompact ((v : AdjointableMap B (FiniteStandardModule B ι)
      (FiniteStandardModule B ι)) - 1)) :
    unitizedModuleMatrixRepresentation (oddFredholmFiniteCompactUnitaryMatrix v hv) =
      (v : AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι)) := by
  rw [oddFredholmFiniteCompactUnitaryMatrix, map_add, oddKTheoryUnitizedRowMatrix_one,
    unitizedModuleMatrixRepresentation_coefficient,
    moduleMatrixRepresentation_finiteModuleCompactMatrix]
  abel

theorem oddFredholmFiniteCompactUnitaryMatrix_mem_unitary
    (v : unitary (AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι)))
    (hv : IsModuleCompact ((v : AdjointableMap B (FiniteStandardModule B ι)
      (FiniteStandardModule B ι)) - 1)) :
    oddFredholmFiniteCompactUnitaryMatrix v hv ∈ unitary (CStarMatrix ι ι (Unitization ℂ B)) := by
  apply Unitary.mem_iff.mpr
  constructor
  · apply unitizationMatrix_eq_of_scalar_and_operator_eq
    · rw [unitizationScalarMatrix_mul, unitizationScalarMatrix_star,
        oddFredholmFiniteCompactUnitaryMatrix_scalar]
      change star (1 : CStarMatrix ι ι ℂ) * 1 =
        OperatorKTheory.matrixMap (OperatorKTheory.scalarQuotient B) 1
      simp only [star_one, one_mul, map_one]
    · rw [map_mul, map_star, oddFredholmFiniteCompactUnitaryMatrix_operator,
        Unitary.coe_star_mul_self, oddKTheoryUnitizedRowMatrix_one]
  · apply unitizationMatrix_eq_of_scalar_and_operator_eq
    · rw [unitizationScalarMatrix_mul, unitizationScalarMatrix_star,
        oddFredholmFiniteCompactUnitaryMatrix_scalar]
      change (1 : CStarMatrix ι ι ℂ) * star 1 =
        OperatorKTheory.matrixMap (OperatorKTheory.scalarQuotient B) 1
      simp only [star_one, one_mul, map_one]
    · rw [map_mul, map_star, oddFredholmFiniteCompactUnitaryMatrix_operator,
        oddKTheoryUnitizedRowMatrix_one]
      simpa only [Unitary.coe_star] using Unitary.coe_mul_star_self v

/-- Genuine finite matrix unitary, with no faithfulness assumption for the
unitization representation alone. -/
def oddFredholmFiniteCompactUnitary
    (v : unitary (AdjointableMap B (FiniteStandardModule B ι) (FiniteStandardModule B ι)))
    (hv : IsModuleCompact ((v : AdjointableMap B (FiniteStandardModule B ι)
      (FiniteStandardModule B ι)) - 1)) : unitary (CStarMatrix ι ι (Unitization ℂ B)) :=
  ⟨oddFredholmFiniteCompactUnitaryMatrix v hv, oddFredholmFiniteCompactUnitaryMatrix_mem_unitary v hv⟩

end FiniteReflection

section Compression

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

omit [StarOrderedRing B] [CompleteSpace E] [CompleteSpace F] in
/-- Compress an actual unitary to an actual invariant isometric range. -/
theorem oddFredholmIsometricCompression_mem_unitary (J : AdjointableMap B E F)
    (hJ : J.adjoint.comp J = AdjointableMap.id) (v : unitary (AdjointableMap B F F))
    (hv : Commute (J.comp J.adjoint) (v : AdjointableMap B F F)) :
    (J.adjoint.comp (v : AdjointableMap B F F)).comp J ∈ unitary (AdjointableMap B E E) := by
  have hJx (x : E) : J.adjoint (J x) = x := by
    simpa only [AdjointableMap.comp_apply, AdjointableMap.id_apply] using
      congrArg (fun T => T x) hJ
  have hQx (x : E) : (J.comp J.adjoint) (J x) = J x := by
    simp only [AdjointableMap.comp_apply, hJx]
  have hQstar : star (J.comp J.adjoint) = J.comp J.adjoint := by
    ext x
    rfl
  have hvs : Commute (J.comp J.adjoint) (star (v : AdjointableMap B F F)) := by
    rw [commute_iff_eq]
    simpa only [star_mul, hQstar] using (congrArg star hv.eq).symm
  have hmul (w : unitary (AdjointableMap B F F))
      (hw : Commute (J.comp J.adjoint) (w : AdjointableMap B F F)) (x : E) :
      J.adjoint (star (w : AdjointableMap B F F)
        (J (J.adjoint ((w : AdjointableMap B F F) (J x))))) = x := by
    have hcomm := congrArg (fun T : AdjointableMap B F F => T (J x)) hw.eq
    change J (J.adjoint ((w : AdjointableMap B F F) (J x))) =
      (w : AdjointableMap B F F) ((J.comp J.adjoint) (J x)) at hcomm
    rw [hcomm, hQx]
    have hcancel := congrArg (fun T : AdjointableMap B F F => T (J x))
      (Unitary.coe_star_mul_self w)
    change star (w : AdjointableMap B F F) ((w : AdjointableMap B F F) (J x)) = J x at hcancel
    rw [hcancel, hJx]
  apply Unitary.mem_iff.mpr
  constructor
  · ext x
    change J.adjoint (star (v : AdjointableMap B F F)
      (J (J.adjoint ((v : AdjointableMap B F F) (J x))))) = x
    exact hmul v hv x
  · ext x
    change J.adjoint ((v : AdjointableMap B F F)
      (J (J.adjoint (star (v : AdjointableMap B F F) (J x))))) = x
    simpa only [Unitary.coe_star, star_star] using hmul (star v) hvs x

end Compression

section StandardCutoff

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
local instance oddContinuationOddFredholmFiniteIndexUnitaryLocalInstance01 : PartialOrder (OddFredholmStandardOperator B) := CStarAlgebra.spectralOrder _
local instance oddContinuationOddFredholmFiniteIndexUnitaryLocalInstance02 : StarOrderedRing (OddFredholmStandardOperator B) := CStarAlgebra.spectralOrderedRing _

def oddFredholmStandardCutoffPolarUnitary (U : unitary (OddFredholmStandardOperator B)) (n : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : OddFredholmStandardOperator B)‖ < 1) :
    unitary (OddFredholmStandardOperator B) :=
  oddFredholmPolarUnitary (oddFredholmUnitaryCutoff U n)
    (oddFredholmIsUnit_of_norm_sub_unitary_lt_one_all _ U hn)

theorem oddFredholmUnitaryCutoff_right_tail (U : unitary (OddFredholmStandardOperator B)) (n : ℕ) :
    oddFredholmUnitaryCutoff U n * (1 - standardCountableCutoff n) = 1 - standardCountableCutoff n := by
  have hq : standardCountableCutoff (B := B) n * (1 - standardCountableCutoff n) = 0 := by
    rw [mul_sub, mul_one, standardCountableCutoff_mul_self, sub_self]
  simp only [oddFredholmUnitaryCutoff, add_mul, one_mul, mul_assoc, hq, mul_zero, add_zero]

theorem oddFredholmUnitaryCutoff_left_tail (U : unitary (OddFredholmStandardOperator B)) (n : ℕ) :
    (1 - standardCountableCutoff n) * oddFredholmUnitaryCutoff U n = 1 - standardCountableCutoff n := by
  have hq : (1 - standardCountableCutoff (B := B) n) * standardCountableCutoff n = 0 := by
    rw [sub_mul, one_mul, standardCountableCutoff_mul_self, sub_self]
  simp only [oddFredholmUnitaryCutoff, mul_add, mul_one, ← mul_assoc, hq, zero_mul, add_zero]

theorem oddFredholmStandardCutoffPolarUnitary_right_tail
    (U : unitary (OddFredholmStandardOperator B)) (n : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : OddFredholmStandardOperator B)‖ < 1) :
    (oddFredholmStandardCutoffPolarUnitary U n hn : OddFredholmStandardOperator B) *
      (1 - standardCountableCutoff n) = 1 - standardCountableCutoff n :=
  oddFredholmPolarElement_right_tail _ _
    (oddFredholmIsUnit_of_norm_sub_unitary_lt_one_all _ U hn)
    (by rw [star_sub, star_one, standardCountableCutoff_star])
    (oddFredholmUnitaryCutoff_right_tail U n) (oddFredholmUnitaryCutoff_left_tail U n)

theorem oddFredholmStandardCutoffPolarUnitary_commutes_cutoff
    (U : unitary (OddFredholmStandardOperator B)) (n : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : OddFredholmStandardOperator B)‖ < 1) :
    Commute (standardCountableCutoff n)
      (oddFredholmStandardCutoffPolarUnitary U n hn : OddFredholmStandardOperator B) := by
  have hr := oddFredholmStandardCutoffPolarUnitary_right_tail U n hn
  have hl := oddFredholmUnitary_left_tail (A := OddFredholmStandardOperator B)
    (oddFredholmStandardCutoffPolarUnitary U n hn)
    (1 - standardCountableCutoff (B := B) n)
    (by rw [star_sub, star_one, standardCountableCutoff_star]) hr
  rw [commute_iff_eq]
  rw [mul_sub, mul_one] at hr
  rw [sub_mul, one_mul] at hl
  have heq := hl.trans hr.symm
  exact sub_right_inj.mp heq

/-- The genuine finite compression of the cutoff polar unitary. -/
def oddFredholmStandardFinitePolarUnitary (U : unitary (OddFredholmStandardOperator B)) (n : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : OddFredholmStandardOperator B)‖ < 1) :
    unitary (AdjointableMap B (FiniteStandardModule B (Fin n)) (FiniteStandardModule B (Fin n))) :=
  ⟨((oddFredholmStandardFiniteInclusion (B := B) n).adjoint.comp
    (oddFredholmStandardCutoffPolarUnitary U n hn : OddFredholmStandardOperator B)).comp
      (oddFredholmStandardFiniteInclusion (B := B) n),
    oddFredholmIsometricCompression_mem_unitary _ (oddFredholmStandardFiniteInclusion_adjoint_comp_self (B := B) n)
      (oddFredholmStandardCutoffPolarUnitary U n hn) (by
        rw [oddFredholmStandardFiniteInclusion_comp_adjoint]
        exact oddFredholmStandardCutoffPolarUnitary_commutes_cutoff U n hn)⟩

theorem oddFredholmStandardFinitePolarUnitary_sub_one_isModuleCompact
    (U : unitary (OddFredholmStandardOperator B))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) (n : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : OddFredholmStandardOperator B)‖ < 1) :
    IsModuleCompact ((oddFredholmStandardFinitePolarUnitary U n hn :
      AdjointableMap B (FiniteStandardModule B (Fin n)) (FiniteStandardModule B (Fin n))) - 1) := by
  have hv := oddFredholmPolarElement_sub_one_isModuleCompact (oddFredholmUnitaryCutoff U n)
    (oddFredholmIsUnit_of_norm_sub_unitary_lt_one_all _ U hn)
    (oddFredholmUnitaryCutoff_sub_one_isModuleCompact U hU n)
  have hc := (hv.comp_left (oddFredholmStandardFiniteInclusion (B := B) n).adjoint).comp_right
    (oddFredholmStandardFiniteInclusion (B := B) n)
  convert hc using 1
  apply AdjointableMap.ext
  intro x
  simp only [oddFredholmStandardFinitePolarUnitary, oddFredholmStandardCutoffPolarUnitary,
    oddFredholmPolarUnitary, AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
    AdjointableMap.one_apply]
  rw [(oddFredholmStandardFiniteInclusion (B := B) n).adjoint.toCLM.map_sub]
  have hh := congrArg
    (fun T : AdjointableMap B (FiniteStandardModule B (Fin n))
      (FiniteStandardModule B (Fin n)) => T x)
    (oddFredholmStandardFiniteInclusion_adjoint_comp_self (B := B) n)
  simpa only [AdjointableMap.comp_apply, AdjointableMap.id_apply] using congrArg
    (fun z => (oddFredholmStandardFiniteInclusion (B := B) n).adjoint
      ((oddFredholmPolarElement (oddFredholmUnitaryCutoff U n) : OddFredholmStandardOperator B)
        (oddFredholmStandardFiniteInclusion (B := B) n x)) - z) hh.symm

/-- Actual finite B-unitization matrix index unitary of a genuine compact
standard-module unitary, after the proved eventual cutoff criterion. -/
def oddFredholmStandardFiniteIndexUnitary (U : unitary (OddFredholmStandardOperator B))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) (n : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : OddFredholmStandardOperator B)‖ < 1) :
    unitary (CStarMatrix (Fin n) (Fin n) (Unitization ℂ B)) :=
  oddFredholmFiniteCompactUnitary (oddFredholmStandardFinitePolarUnitary U n hn)
    (oddFredholmStandardFinitePolarUnitary_sub_one_isModuleCompact U hU n hn)

theorem oddFredholmStandardFiniteIndexUnitary_scalar
    (U : unitary (OddFredholmStandardOperator B))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) (n : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : OddFredholmStandardOperator B)‖ < 1) :
    unitizationScalarMatrix (oddFredholmStandardFiniteIndexUnitary U hU n hn :
      CStarMatrix (Fin n) (Fin n) (Unitization ℂ B)) = 1 :=
  oddFredholmFiniteCompactUnitaryMatrix_scalar _ _

end StandardCutoff
end BC4lean.KKTheory
