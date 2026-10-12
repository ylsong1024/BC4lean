import BC4lean.StandardCountableHilbertModuleFibre
import BC4lean.StandardCountablePairedModuleFibre
import BC4lean.UnitizationContinuousProjectionEvaluation
import BC4lean.OddFredholmOperatorK1Index

/-! # Genuine fibre naturality of the exponential and finite polar odd index

Actual completed-module evaluation commutes with the exponential, compact
cutoff, polar normalization, and finite coordinate compression. Full scalar
matrix and actual finite module action together identify the evaluated
unitization matrix, retaining the nonunital coefficient information.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped Matrix Ring CStarAlgebra
open BC4lean.OperatorKTheory

variable {B X : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [StarOrderedRing B] [TopologicalSpace X] [CompactSpace X]

local instance standardFibreIndexSpectralOrder (A : Type*) [CStarAlgebra A] : PartialOrder A :=
  CStarAlgebra.spectralOrder A
local instance standardFibreIndexSpectralOrderedRing (A : Type*) [CStarAlgebra A] : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

def oddFredholmStandardFibreSelfAdjoint (t : X)
    (F : selfAdjoint (OddFredholmStandardOperator C(X, B))) :
    selfAdjoint (OddFredholmStandardOperator B) :=
  ⟨standardCountableFibreOperatorHom (B := B) (X := X) t (F : OddFredholmStandardOperator C(X, B)),
    F.property.map (standardCountableFibreOperatorHom (B := B) (X := X) t)⟩

theorem oddFredholmStandardFibre_exponential (t : X)
    (F : selfAdjoint (OddFredholmStandardOperator C(X, B))) :
    standardCountableFibreUnitary (B := B) (X := X) t (oddFredholmExponential (A := OddFredholmStandardOperator C(X, B)) F) =
      oddFredholmExponential (A := OddFredholmStandardOperator B) (oddFredholmStandardFibreSelfAdjoint t F) := by
  apply Subtype.ext
  change standardCountableFibreOperatorHom (B := B) (X := X) t (oddFredholmExponential (A := OddFredholmStandardOperator C(X, B)) F : OddFredholmStandardOperator C(X, B)) = _
  rw [oddFredholmExponential_eq_cfc, oddFredholmExponential_eq_cfc]
  exact (standardCountableFibreOperatorHom (B := B) (X := X) t).map_cfc _ _

@[simp] theorem oddFredholmStandardFibre_cutoff (t : X)
    (U : unitary (OddFredholmStandardOperator C(X, B))) (n : ℕ) :
    standardCountableFibreOperatorHom (B := B) (X := X) t (oddFredholmUnitaryCutoff U n) =
      oddFredholmUnitaryCutoff (standardCountableFibreUnitary (B := B) (X := X) t U) n := by
  simp only [oddFredholmUnitaryCutoff, map_add, map_mul, map_sub, map_one,
    standardCountableFibreOperatorHom_cutoff, standardCountableFibreUnitary]

theorem oddFredholmStandardFibre_cutoff_near (t : X)
    (U : unitary (OddFredholmStandardOperator C(X, B))) (n : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : OddFredholmStandardOperator C(X, B))‖ < 1) :
    ‖oddFredholmUnitaryCutoff (standardCountableFibreUnitary (B := B) (X := X) t U) n -
      (standardCountableFibreUnitary (B := B) (X := X) t U : OddFredholmStandardOperator B)‖ < 1 := by
  have h := standardCountableFibreOperatorHom_norm_le t
    (oddFredholmUnitaryCutoff U n - (U : OddFredholmStandardOperator C(X, B)))
  rw [map_sub, oddFredholmStandardFibre_cutoff] at h
  exact lt_of_le_of_lt h hn

theorem oddFredholmStandardFibre_cutoffPolar (t : X)
    (U : unitary (OddFredholmStandardOperator C(X, B))) (n : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : OddFredholmStandardOperator C(X, B))‖ < 1) :
    standardCountableFibreUnitary (B := B) (X := X) t (oddFredholmStandardCutoffPolarUnitary U n hn) =
      oddFredholmStandardCutoffPolarUnitary (standardCountableFibreUnitary (B := B) (X := X) t U) n
        (oddFredholmStandardFibre_cutoff_near t U n hn) := by
  apply Subtype.ext
  change standardCountableFibreOperatorHom (B := B) (X := X) t
      (oddFredholmPolarElement (oddFredholmUnitaryCutoff U n)) =
    oddFredholmPolarElement (oddFredholmUnitaryCutoff (standardCountableFibreUnitary (B := B) (X := X) t U) n)
  rw [oddFredholmPolarElement_map _ _
    (oddFredholmIsUnit_of_norm_sub_unitary_lt_one_all _ U hn),
    oddFredholmStandardFibre_cutoff]

theorem oddFredholmStandardCoefficientEvaluation_finiteInclusion (t : X) (n : ℕ)
    (x : FiniteStandardModule C(X, B) (Fin n)) :
    standardCountableCoefficientEvaluation t (oddFredholmStandardFiniteInclusion (B := C(X, B)) n x) =
      oddFredholmStandardFiniteInclusion (B := B) n (finiteStandardCoefficientEvaluationVector (B := B) (X := X) t x) := by
  rw [oddFredholmStandardFiniteInclusion_apply, map_sum]
  simp only [standardCountableCoefficientEvaluation_inclusion,
    oddFredholmStandardFiniteInclusion_apply, finiteStandardCoefficientEvaluationVector_apply]

theorem oddFredholmStandardCoefficientEvaluation_finiteInclusion_adjoint (t : X) (n : ℕ)
    (x : StandardCountableHilbertModule C(X, B)) :
    finiteStandardCoefficientEvaluationVector (B := B) (X := X) t ((oddFredholmStandardFiniteInclusion (B := C(X, B)) n).adjoint x) =
      (oddFredholmStandardFiniteInclusion (B := B) n).adjoint (standardCountableCoefficientEvaluation t x) := by
  ext i
  simp only [finiteStandardCoefficientEvaluationVector_apply,
    oddFredholmStandardFiniteInclusion_adjoint_apply,
    standardCountableCoefficientEvaluation_coordinate]

theorem oddFredholmStandardFibre_finitePolar_evaluation (t : X)
    (U : unitary (OddFredholmStandardOperator C(X, B))) (n : ℕ)
    (hn : ‖oddFredholmUnitaryCutoff U n - (U : OddFredholmStandardOperator C(X, B))‖ < 1)
    (x : FiniteStandardModule C(X, B) (Fin n)) :
    finiteStandardCoefficientEvaluationVector (B := B) (X := X) t ((oddFredholmStandardFinitePolarUnitary U n hn :
      AdjointableMap C(X, B) (FiniteStandardModule C(X, B) (Fin n))
        (FiniteStandardModule C(X, B) (Fin n))) x) =
      (oddFredholmStandardFinitePolarUnitary (standardCountableFibreUnitary (B := B) (X := X) t U) n
        (oddFredholmStandardFibre_cutoff_near t U n hn) :
          AdjointableMap B (FiniteStandardModule B (Fin n)) (FiniteStandardModule B (Fin n)))
          (finiteStandardCoefficientEvaluationVector (B := B) (X := X) t x) := by
  change finiteStandardCoefficientEvaluationVector (B := B) (X := X) t
      ((oddFredholmStandardFiniteInclusion (B := C(X, B)) n).adjoint
        ((oddFredholmStandardCutoffPolarUnitary U n hn : OddFredholmStandardOperator C(X, B))
          (oddFredholmStandardFiniteInclusion (B := C(X, B)) n x))) = _
  rw [oddFredholmStandardCoefficientEvaluation_finiteInclusion_adjoint]
  have he := standardCountableFibreOperatorHom_evaluation t
    (oddFredholmStandardCutoffPolarUnitary U n hn : OddFredholmStandardOperator C(X, B)) (oddFredholmStandardFiniteInclusion (B := C(X, B)) n x)
  have hp := congrArg (fun v : unitary (OddFredholmStandardOperator B) =>
    (v : OddFredholmStandardOperator B)) (oddFredholmStandardFibre_cutoffPolar t U n hn)
  change standardCountableFibreOperatorHom (B := B) (X := X) t
    (oddFredholmStandardCutoffPolarUnitary U n hn : OddFredholmStandardOperator C(X, B)) = _ at hp
  rw [hp] at he
  rw [← he, oddFredholmStandardCoefficientEvaluation_finiteInclusion]
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def oddFredholmFiniteCoefficientConstant (x : FiniteStandardModule B ι) :
    FiniteStandardModule C(X, B) ι :=
  (WithCStarModule.equiv _ _).symm (fun i =>
    MulOpposite.op (ContinuousMap.const X (MulOpposite.unop (x i))))

omit [PartialOrder B] [StarOrderedRing B] [CompactSpace X] [Fintype ι] [DecidableEq ι] in
@[simp] theorem oddFredholmFiniteCoefficientEvaluation_constant
    [PartialOrder B] [StarOrderedRing B] [CompactSpace X] [Fintype ι] [DecidableEq ι] (t : X)
    (x : FiniteStandardModule B ι) :
    finiteStandardCoefficientEvaluationVector (B := B) (X := X) t (oddFredholmFiniteCoefficientConstant x) = x := by
  ext i
  rfl

theorem oddFredholmUnitizedLeftMul_evaluation (t : X)
    (a : Unitization ℂ C(X, B)) (x : C(X, B)ᵐᵒᵖ) :
    standardCoefficientEvaluationLinear (B := B) (X := X) t (unitizedStandardLeftMul (B := C(X, B)) a x) =
      unitizedStandardLeftMul (B := B) (unitizationContinuousEvaluation (B := B) (X := X) t a)
        (standardCoefficientEvaluationLinear (B := B) (X := X) t x) := by
  simp [unitizedStandardLeftMul_apply, standardLeftMul_apply,
    standardCoefficientEvaluationLinear, unitizationContinuousEvaluation_apply,
    Unitization.algebraMap_eq_inl]

omit [PartialOrder B] [StarOrderedRing B] in
/-- Entrywise evaluation of the genuine full unitization matrix at any
finite index universe; its original Type0 version is recovered below. -/
def oddFredholmUnitizationContinuousMatrixEvaluation (t : X)
    (M : CStarMatrix ι ι (Unitization ℂ C(X, B))) : CStarMatrix ι ι (Unitization ℂ B) :=
  matrixMap (A := Unitization ℂ C(X, B)) (B := Unitization ℂ B) (ι := ι)
    (unitizationContinuousEvaluation (B := B) (X := X) t) M

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem oddFredholmUnitizationContinuousMatrixEvaluation_apply (t : X)
    (M : CStarMatrix ι ι (Unitization ℂ C(X, B))) (i j : ι) :
    oddFredholmUnitizationContinuousMatrixEvaluation (B := B) (X := X) (ι := ι) t M i j =
      unitizationContinuousEvaluation (B := B) (X := X) t (M i j) := rfl

omit [PartialOrder B] [StarOrderedRing B] in
/-- The existing native small-index matrix evaluation retains every entry. -/
theorem oddFredholmUnitizationContinuousMatrixEvaluation_small {κ : Type}
    [Fintype κ] [DecidableEq κ] (t : X)
    (M : CStarMatrix κ κ (Unitization ℂ C(X, B))) :
    oddFredholmUnitizationContinuousMatrixEvaluation (B := B) (X := X) (ι := κ) t M =
      unitizationContinuousMatrixEvaluation (B := B) (X := X) (ι := κ) t M := rfl

theorem oddFredholmUnitizedMatrix_evaluation (t : X)
    (M : CStarMatrix ι ι (Unitization ℂ C(X, B)))
    (x : FiniteStandardModule C(X, B) ι) :
    finiteStandardCoefficientEvaluationVector (B := B) (X := X) t (unitizedModuleMatrixRepresentation (B := C(X, B)) (ι := ι) M x) =
      unitizedModuleMatrixRepresentation (B := B) (ι := ι) (oddFredholmUnitizationContinuousMatrixEvaluation (B := B) (X := X) (ι := ι) t M)
        (finiteStandardCoefficientEvaluationVector (B := B) (X := X) t x) := by
  ext i
  simp only [finiteStandardCoefficientEvaluationVector_apply,
    unitizedModuleMatrixRepresentation_apply, oddFredholmUnitizationContinuousMatrixEvaluation_apply]
  change standardCoefficientEvaluationLinear (B := B) (X := X) t
      (∑ j, unitizedStandardLeftMul (B := C(X, B)) (M i j) (x j)) =
    ∑ j, unitizedStandardLeftMul (B := B) (unitizationContinuousEvaluation (B := B) (X := X) t (M i j))
      (standardCoefficientEvaluationLinear (B := B) (X := X) t (x j))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact oddFredholmUnitizedLeftMul_evaluation t _ _

/-- The evaluated finite polar index matrix is exactly the matrix constructed
from the actual fibre unitary at the same cutoff size. -/
theorem oddFredholmStandardFiniteIndexUnitary_evaluation (t : X)
    (U : unitary (OddFredholmStandardOperator C(X, B)))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator C(X, B)) - 1))
    (n : ℕ) (hn : ‖oddFredholmUnitaryCutoff U n - (U : OddFredholmStandardOperator C(X, B))‖ < 1) :
    unitizationContinuousMatrixEvaluation (B := B) (X := X) (ι := Fin n) t
      (oddFredholmStandardFiniteIndexUnitary U hU n hn :
        CStarMatrix (Fin n) (Fin n) (Unitization ℂ C(X, B))) =
        (oddFredholmStandardFiniteIndexUnitary (standardCountableFibreUnitary (B := B) (X := X) t U)
          (standardCountableFibreUnitary_sub_one_isModuleCompact t U hU) n
          (oddFredholmStandardFibre_cutoff_near t U n hn) :
            CStarMatrix (Fin n) (Fin n) (Unitization ℂ B)) := by
  apply unitizationMatrix_eq_of_scalar_and_operator_eq
  · rw [unitizationScalarMatrix_continuousEvaluation]
    exact (oddFredholmStandardFiniteIndexUnitary_scalar U hU n hn).trans
      (oddFredholmStandardFiniteIndexUnitary_scalar _ _ n _).symm
  · apply AdjointableMap.ext
    intro x
    let y := oddFredholmFiniteCoefficientConstant (X := X) x
    have hy : finiteStandardCoefficientEvaluationVector (B := B) (X := X) t y = x :=
      oddFredholmFiniteCoefficientEvaluation_constant t x
    rw [← hy]
    rw [← oddFredholmUnitizationContinuousMatrixEvaluation_small (B := B) (X := X)
      (κ := Fin n) t (oddFredholmStandardFiniteIndexUnitary U hU n hn :
        CStarMatrix (Fin n) (Fin n) (Unitization ℂ C(X, B)))]
    rw [← oddFredholmUnitizedMatrix_evaluation (B := B) (X := X) (ι := Fin n) t
      (oddFredholmStandardFiniteIndexUnitary U hU n hn :
        CStarMatrix (Fin n) (Fin n) (Unitization ℂ C(X, B))) y]
    change finiteStandardCoefficientEvaluationVector (B := B) (X := X) t
        (unitizedModuleMatrixRepresentation (B := C(X, B)) (ι := Fin n)
          (oddFredholmFiniteCompactUnitaryMatrix _ _) y) = _
    rw [oddFredholmFiniteCompactUnitaryMatrix_operator,
      oddFredholmStandardFibre_finitePolar_evaluation]
    change _ = unitizedModuleMatrixRepresentation (B := B) (ι := Fin n)
      (oddFredholmFiniteCompactUnitaryMatrix _ _)
      (finiteStandardCoefficientEvaluationVector (B := B) (X := X) t y)
    rw [oddFredholmFiniteCompactUnitaryMatrix_operator]

end BC4lean.KKTheory
