import BC4lean.StandardCountableRelativeProjectionPathIndex
import BC4lean.StandardCountablePairedModuleFibre
import BC4lean.UnitizationContinuousProjectionEvaluation

/-! # Genuine finite relative projection index on completed coefficient fibres

The actual paired radical-quotient fibre is identified by its whole evaluated
form and the explicit constant lift. Its endomorphism homomorphism preserves
reference projection, cutoffs, compactness, and CFC rounding. The entire scalar
matrix and actual finite action identify the evaluated canonical corner
matrix. One genuine interval corner then proves endpoint index equality.
-/

noncomputable section
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory
open unitInterval
open scoped Matrix

variable {B X : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X]

local notation:max "StdPair" B:arg => PairedStandardModule B
local notation:max "StdEnd" B:arg => AdjointableMap B (StdPair B) (StdPair B)

local instance fibreIndexOperatorOrder (A : Type*) [CStarAlgebra A] : PartialOrder A :=
  CStarAlgebra.spectralOrder A
local instance fibreIndexOperatorStarOrder (A : Type*) [CStarAlgebra A] : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

/-- Actual unital endomorphism evaluation through the whole paired fibre unitary. -/
def pairedStandardFibreOperatorHom (t : X) : StdEnd C(X, B) →⋆ₐ[ℂ] StdEnd B :=
  (pairedStandardModuleFibreEquiv (B := B) t).transportStarAlgEquiv.toStarAlgHom.comp
    (hilbertModuleFibreOperatorHom (B := B) (M := StdPair C(X, B)) t)

set_option maxHeartbeats 800000 in
theorem pairedStandardFibreOperatorHom_evaluation (t : X) (T : StdEnd C(X, B))
    (x : StdPair C(X, B)) :
    pairedStandardFibreOperatorHom t T (pairedStandardCoefficientEvaluation t x) =
      pairedStandardCoefficientEvaluation t (T x) := by
  let u : HilbertModuleEquiv B (HilbertModuleFibre B (StdPair C(X, B)) t) (StdPair B) :=
    pairedStandardModuleFibreEquiv (B := B) t
  let Q : AdjointableMap B (HilbertModuleFibre B (StdPair C(X, B)) t)
      (HilbertModuleFibre B (StdPair C(X, B)) t) :=
    hilbertModuleFibreOperator (B := B) (M := StdPair C(X, B)) t T
  have hu (v : StdPair C(X, B)) :
      u (hilbertModuleFibreMk (B := B) t v) = pairedStandardCoefficientEvaluation (B := B) t v :=
    pairedStandardModuleFibreEquiv_mk (B := B) t v
  have hinv : u.symm (pairedStandardCoefficientEvaluation (B := B) t x) =
      hilbertModuleFibreMk (B := B) t x := by
    calc
      _ = u.symm (u (hilbertModuleFibreMk (B := B) t x)) :=
        congrArg (fun y : StdPair B => u.symm y) (hu x).symm
      _ = _ := u.symm_apply_apply (hilbertModuleFibreMk (B := B) t x)
  calc
    pairedStandardFibreOperatorHom (B := B) t T (pairedStandardCoefficientEvaluation (B := B) t x) =
        u (Q (u.symm (pairedStandardCoefficientEvaluation (B := B) t x))) := by
      change u.transport Q (pairedStandardCoefficientEvaluation (B := B) t x) = _
      exact HilbertModuleEquiv.transport_apply u Q (pairedStandardCoefficientEvaluation (B := B) t x)
    _ = u (Q (hilbertModuleFibreMk (B := B) t x)) :=
      congrArg (fun v : HilbertModuleFibre B (StdPair C(X, B)) t => u (Q v)) hinv
    _ = u (hilbertModuleFibreMk (B := B) t (T x)) :=
      congrArg (fun v : HilbertModuleFibre B (StdPair C(X, B)) t => u v)
        (hilbertModuleFibreOperator_mk (B := B) (M := StdPair C(X, B)) t T x)
    _ = pairedStandardCoefficientEvaluation (B := B) t (T x) := hu (T x)

theorem pairedStandardFibreOperatorHom_norm_le (t : X) (T : StdEnd C(X, B)) :
    ‖pairedStandardFibreOperatorHom t T‖ ≤ ‖T‖ := by
  change ‖(pairedStandardModuleFibreEquiv t).transport (hilbertModuleFibreOperator t T)‖ ≤ _
  rw [HilbertModuleEquiv.transport_norm]
  exact hilbertModuleFibreOperator_norm_le t T

set_option maxHeartbeats 800000 in
theorem pairedStandardFibreOperatorHom_compact (t : X) (T : StdEnd C(X, B))
    (hT : IsModuleCompact T) : IsModuleCompact (pairedStandardFibreOperatorHom t T) := by
  have hF : IsModuleCompact (hilbertModuleFibreOperator (B := B) (M := StdPair C(X, B)) t T) :=
    IsModuleCompact.fibre (B := B) (M := StdPair C(X, B)) hT t
  change IsModuleCompact ((pairedStandardModuleFibreEquiv (B := B) t).transport
    (hilbertModuleFibreOperator (B := B) (M := StdPair C(X, B)) t T))
  exact (pairedStandardModuleFibreEquiv (B := B) t).transportMap_isModuleCompact
    (pairedStandardModuleFibreEquiv (B := B) t) hF

@[simp] theorem pairedStandardFibreOperatorHom_cutoff (t : X) (n : ℕ) :
    pairedStandardFibreOperatorHom (B := B) t (standardCountablePairedCutoff n) =
      standardCountablePairedCutoff n := by
  apply AdjointableMap.ext
  intro x
  rw [← pairedStandardCoefficientEvaluation_constant t x,
    pairedStandardFibreOperatorHom_evaluation, pairedStandardCoefficientEvaluation_cutoff,
    pairedStandardCoefficientEvaluation_constant]

@[simp] theorem pairedStandardFibreOperatorHom_reference (t : X) :
    pairedStandardFibreOperatorHom (B := B) t standardCountablePairedReferenceProjection =
      standardCountablePairedReferenceProjection := by
  apply AdjointableMap.ext
  intro x
  rw [← pairedStandardCoefficientEvaluation_constant t x,
    pairedStandardFibreOperatorHom_evaluation, pairedStandardCoefficientEvaluation_reference,
    pairedStandardCoefficientEvaluation_constant]

@[simp] theorem pairedStandardFibreOperatorHom_compression (t : X)
    (P : StdEnd C(X, B)) (n : ℕ) :
    pairedStandardFibreOperatorHom t (standardCountableReferenceCompression P n) =
      standardCountableReferenceCompression (pairedStandardFibreOperatorHom t P) n := by
  simp only [standardCountableReferenceCompression, map_add, map_mul, map_sub,
    pairedStandardFibreOperatorHom_reference, pairedStandardFibreOperatorHom_cutoff]

/-- A globally admissible actual cutoff remains admissible on each actual fibre. -/
theorem pairedStandardFibreOperatorHom_compression_near (t : X)
    (P : StdEnd C(X, B)) (n : ℕ)
    (hn : ‖standardCountableReferenceCompression P n - P‖ < 1 / 64) :
    ‖standardCountableReferenceCompression (pairedStandardFibreOperatorHom t P) n -
      pairedStandardFibreOperatorHom t P‖ < 1 / 64 := by
  have h := pairedStandardFibreOperatorHom_norm_le t (standardCountableReferenceCompression P n - P)
  rw [map_sub, pairedStandardFibreOperatorHom_compression] at h
  exact lt_of_le_of_lt h hn

set_option maxHeartbeats 800000 in
@[simp] theorem pairedStandardFibreOperatorHom_rounding (t : X)
    (P : StdEnd C(X, B)) (hP : IsSelfAdjoint P) (n : ℕ) :
    pairedStandardFibreOperatorHom t (spectralGapRoundedProjection (standardCountableReferenceCompression P n)) =
      spectralGapRoundedProjection (standardCountableReferenceCompression (pairedStandardFibreOperatorHom t P) n) := by
  have hEval : Continuous (pairedStandardFibreOperatorHom (B := B) t) :=
    AddMonoidHomClass.continuous_of_bound (pairedStandardFibreOperatorHom (B := B) t) 1
      (fun T => by simpa only [one_mul] using pairedStandardFibreOperatorHom_norm_le t T)
  have hCompression : IsSelfAdjoint
      (standardCountableReferenceCompression (B := C(X, B)) P n) :=
    standardCountableReferenceCompression_isSelfAdjoint (B := C(X, B)) P hP n
  have hFibreCompression : IsSelfAdjoint
      (pairedStandardFibreOperatorHom (B := B) t
        (standardCountableReferenceCompression (B := C(X, B)) P n)) :=
    hCompression.map (pairedStandardFibreOperatorHom (B := B) t)
  have hCfc := (pairedStandardFibreOperatorHom (B := B) t).map_cfc projectionRoundCutoff
    (standardCountableReferenceCompression (B := C(X, B)) P n)
    continuous_projectionRoundCutoff.continuousOn hEval hCompression hFibreCompression
  unfold spectralGapRoundedProjection
  rw [hCfc, pairedStandardFibreOperatorHom_compression]

set_option maxHeartbeats 800000 in
/-- Relative compactness is evaluated through the actual compact ideal map. -/
theorem pairedStandardFibreProjection_compact (t : X) (P : StdEnd C(X, B))
    (hc : IsModuleCompact (P - standardCountablePairedReferenceProjection)) :
    IsModuleCompact (pairedStandardFibreOperatorHom t P - standardCountablePairedReferenceProjection) := by
  have h := pairedStandardFibreOperatorHom_compact (B := B) t
    (P - standardCountablePairedReferenceProjection (B := C(X, B))) hc
  simpa only [map_sub, pairedStandardFibreOperatorHom_reference] using h

section Finite
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def finiteStandardCoefficientConstantVector (x : FiniteStandardModule B ι) :
    FiniteStandardModule C(X, B) ι :=
  (WithCStarModule.equiv _ _).symm fun i =>
    MulOpposite.op (ContinuousMap.const X (MulOpposite.unop (x i)))

omit B X ι [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X] [Fintype ι] [DecidableEq ι] in
@[simp] theorem finiteStandardCoefficientEvaluation_constant
    {B X : Type*} [NonUnitalCStarAlgebra B] [hOrder : PartialOrder B]
    [hStarOrder : StarOrderedRing B] [TopologicalSpace X] [hCompact : CompactSpace X]
    {ι : Type*} [hFinite : Fintype ι] [hDecidable : DecidableEq ι] (t : X)
    (x : FiniteStandardModule B ι) :
    finiteStandardCoefficientEvaluationVector t (finiteStandardCoefficientConstantVector x) = x := by
  let _ := hOrder
  let _ := hStarOrder
  let _ := hCompact
  let _ := hFinite
  let _ := hDecidable
  ext i
  rfl

theorem unitizedStandardLeftMul_coefficient_evaluation (t : X)
    (a : Unitization ℂ C(X, B)) (x : C(X, B)ᵐᵒᵖ) :
    standardCoefficientEvaluationLinear t (unitizedStandardLeftMul a x) =
      unitizedStandardLeftMul (unitizationContinuousEvaluation t a)
        (standardCoefficientEvaluationLinear t x) := by
  simp [unitizedStandardLeftMul_apply, standardLeftMul_apply,
    standardCoefficientEvaluationLinear, unitizationContinuousEvaluation_apply,
    Unitization.algebraMap_eq_inl]

theorem unitizedModuleMatrixRepresentation_coefficient_evaluation (t : X)
    (M : CStarMatrix ι ι (Unitization ℂ C(X, B)))
    (x : FiniteStandardModule C(X, B) ι) :
    finiteStandardCoefficientEvaluationVector t (unitizedModuleMatrixRepresentation M x) =
      unitizedModuleMatrixRepresentation (B := B)
        (CStarMatrix.ofMatrix fun i j => unitizationContinuousEvaluation (B := B) t (M i j))
        (finiteStandardCoefficientEvaluationVector (B := B) t x) := by
  ext i
  simp only [finiteStandardCoefficientEvaluationVector_apply,
    unitizedModuleMatrixRepresentation_apply]
  change standardCoefficientEvaluationLinear t
      (∑ j, unitizedStandardLeftMul (M i j) (x j)) =
    ∑ j, unitizedStandardLeftMul (unitizationContinuousEvaluation t (M i j))
      (standardCoefficientEvaluationLinear t (x j))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact unitizedStandardLeftMul_coefficient_evaluation t _ _

end Finite

omit B X [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X] in
@[simp] theorem pairedStandardFiniteReferenceMatrix_evaluation
    {B X : Type*} [NonUnitalCStarAlgebra B] [hOrder : PartialOrder B]
    [hStarOrder : StarOrderedRing B] [TopologicalSpace X] [CompactSpace X] (t : X) (n : ℕ) :
    unitizationContinuousMatrixEvaluation t (pairedStandardFiniteReferenceMatrix (B := C(X, B)) n) =
      pairedStandardFiniteReferenceMatrix (B := B) n := by
  let _ := hOrder
  let _ := hStarOrder
  apply CStarMatrix.ext
  intro i j
  simp only [unitizationContinuousMatrixEvaluation_apply, pairedStandardFiniteReferenceMatrix,
    CStarMatrix.ofMatrix_apply, Matrix.diagonal_apply]
  split_ifs <;> cases i <;> simp

/-- Actual finite compression commutes with whole coefficient evaluation. -/
theorem pairedStandardFiniteCompression_evaluation (t : X) (n : ℕ)
    (P : StdEnd C(X, B)) (x : FiniteStandardModule C(X, B) (PairedStandardFiniteIndex n)) :
    finiteStandardCoefficientEvaluationVector t (pairedStandardFiniteCompression n P x) =
      pairedStandardFiniteCompression n (pairedStandardFibreOperatorHom t P)
        (finiteStandardCoefficientEvaluationVector t x) := by
  change finiteStandardCoefficientEvaluationVector t
    ((pairedStandardFiniteInclusion n).adjoint (P (pairedStandardFiniteInclusion n x))) = _
  rw [pairedStandardCoefficientEvaluation_finiteInclusion_adjoint,
    ← pairedStandardFibreOperatorHom_evaluation, pairedStandardCoefficientEvaluation_finiteInclusion]
  rfl

set_option maxHeartbeats 800000 in
/-- Full scalar and actual finite action jointly identify the evaluated matrix. -/
theorem standardCountableRelativeFiniteMatrix_fibre (t : X)
    (R : StdEnd C(X, B)) (hc : IsModuleCompact (R - standardCountablePairedReferenceProjection)) (n : ℕ) :
    unitizationContinuousMatrixEvaluation t (standardCountableRelativeFiniteMatrix R hc n) =
      standardCountableRelativeFiniteMatrix (pairedStandardFibreOperatorHom t R)
        (pairedStandardFibreProjection_compact t R hc) n := by
  apply unitizationMatrix_eq_of_scalar_and_operator_eq
  · rw [unitizationScalarMatrix_continuousEvaluation, standardCountableRelativeFiniteMatrix_scalar,
      standardCountableRelativeFiniteMatrix_scalar,
      ← pairedStandardFiniteReferenceMatrix_evaluation (B := B) t n,
      unitizationScalarMatrix_continuousEvaluation]
  · apply AdjointableMap.ext
    intro x
    let y : FiniteStandardModule C(X, B) (PairedStandardFiniteIndex n) :=
      finiteStandardCoefficientConstantVector (B := B) (X := X) x
    have hy : finiteStandardCoefficientEvaluationVector (B := B) t y = x :=
      finiteStandardCoefficientEvaluation_constant (B := B) (X := X)
        (ι := PairedStandardFiniteIndex n) t x
    change unitizedModuleMatrixRepresentation (B := B)
      (CStarMatrix.ofMatrix fun i j => unitizationContinuousEvaluation t
        (standardCountableRelativeFiniteMatrix R hc n i j)) x = _
    rw [← hy, ← unitizedModuleMatrixRepresentation_coefficient_evaluation,
      standardCountableRelativeFiniteMatrix_operator, pairedStandardFiniteCompression_evaluation,
      standardCountableRelativeFiniteMatrix_operator]


/-- The actual canonical rounded finite matrix at one globally chosen cutoff. -/
def standardCountableRoundedFiniteMatrix (P : StdEnd C(X, B)) (hP : IsStarProjection P)
    (hc : IsModuleCompact (P - standardCountablePairedReferenceProjection)) (n : ℕ) :=
  standardCountableRelativeFiniteMatrix
    (spectralGapRoundedProjection (standardCountableReferenceCompression P n))
    (standardCountableRoundedProjection_compact P hP hc n) n

theorem standardCountableRoundedFiniteMatrix_isStarProjection
    (P : StdEnd C(X, B)) (hP : IsStarProjection P)
    (hc : IsModuleCompact (P - standardCountablePairedReferenceProjection)) (n : ℕ)
    (hn : ‖standardCountableReferenceCompression P n - P‖ < 1 / 64) :
    IsStarProjection (standardCountableRoundedFiniteMatrix P hP hc n) :=
  standardCountableRelativeFiniteMatrix_isStarProjection _
    (standardCountableRoundedProjection_isStarProjection P hP n hn)
    (standardCountableRoundedProjection_compact P hP hc n) n
    (standardCountableRelativeCorner_commutes_cutoff n _
      (spectralGapRoundedReferenceCompression_sub_eq_cutoff P hP.isSelfAdjoint n))

/-- The full scalar matrix of the rounded projection is the actual reference. -/
theorem standardCountableRoundedFiniteMatrix_scalar
    (P : StdEnd C(X, B)) (hP : IsStarProjection P)
    (hc : IsModuleCompact (P - standardCountablePairedReferenceProjection)) (n : ℕ) :
    unitizationScalarMatrix (standardCountableRoundedFiniteMatrix P hP hc n) =
      unitizationScalarMatrix (pairedStandardFiniteReferenceMatrix (B := C(X, B)) n) :=
  standardCountableRelativeFiniteMatrix_scalar _ _ _

set_option maxHeartbeats 1600000 in
/-- The genuine fibre index equals evaluation of the one global finite pair. -/
theorem standardCountableRelativeProjectionIndex_fibre_eq_finiteEvaluation (t : X)
    (P : StdEnd C(X, B)) (hP : IsStarProjection P)
    (hc : IsModuleCompact (P - standardCountablePairedReferenceProjection)) (n : ℕ)
    (hn : ‖standardCountableReferenceCompression P n - P‖ < 1 / 64) :
    standardCountableRelativeProjectionIndex (pairedStandardFibreOperatorHom t P)
      (hP.map (pairedStandardFibreOperatorHom t)) (pairedStandardFibreProjection_compact t P hc) =
      unitizationRelativeProjectionEvaluationK0 t
        (standardCountableRoundedFiniteMatrix P hP hc n)
        (pairedStandardFiniteReferenceMatrix (B := C(X, B)) n)
        (standardCountableRoundedFiniteMatrix_isStarProjection P hP hc n hn)
        (pairedStandardFiniteReferenceMatrix_isStarProjection n)
        (standardCountableRoundedFiniteMatrix_scalar P hP hc n) := by
  rw [standardCountableRelativeProjectionIndex_eq_admissible _ _ _ n
    (pairedStandardFibreOperatorHom_compression_near t P n hn)]
  apply operatorK0Inclusion_injective B
  simp only [standardCountableRoundedProjectionIndex, standardCountableSupportedProjectionIndex,
    unitizationRelativeProjectionEvaluationK0, operatorK0Inclusion_unitizationRelativeProjectionK0]
  have hMatrix : unitizationContinuousMatrixEvaluation t
      (standardCountableRoundedFiniteMatrix P hP hc n) =
      standardCountableRelativeFiniteMatrix
        (spectralGapRoundedProjection
          (standardCountableReferenceCompression (pairedStandardFibreOperatorHom t P) n))
        (standardCountableRoundedProjection_compact _ (hP.map (pairedStandardFibreOperatorHom t))
          (pairedStandardFibreProjection_compact t P hc) n) n := by
    unfold standardCountableRoundedFiniteMatrix
    have hEvaluation := standardCountableRelativeFiniteMatrix_fibre (B := B) t
        (spectralGapRoundedProjection (standardCountableReferenceCompression (B := C(X, B)) P n))
        (standardCountableRoundedProjection_compact (B := C(X, B)) P hP hc n) n
    have hFiniteMatrixCongr (R S : StdEnd B)
        (hR : IsModuleCompact (R - standardCountablePairedReferenceProjection))
        (hS : IsModuleCompact (S - standardCountablePairedReferenceProjection)) (hRS : R = S) :
        standardCountableRelativeFiniteMatrix R hR n =
          standardCountableRelativeFiniteMatrix S hS n := by
      subst S
      rfl
    exact hEvaluation.trans (hFiniteMatrixCongr _ _ _ _
      (pairedStandardFibreOperatorHom_rounding (B := B) t P hP.isSelfAdjoint n))
  simp only [hMatrix, pairedStandardFiniteReferenceMatrix_evaluation (B := B) t n]

set_option maxHeartbeats 1600000 in
/-- A genuine interval relative projection has the same actual index on its
completed endpoint fibres. The interval object is an adjointable operator
on H_{C(I,B)} rather than an assumed norm-continuous operator family on H_B. -/
theorem standardCountableRelativeProjectionIndex_fibre_endpoints
    (P : StdEnd C(I, B)) (hP : IsStarProjection P)
    (hc : IsModuleCompact (P - standardCountablePairedReferenceProjection)) :
    standardCountableRelativeProjectionIndex (pairedStandardFibreOperatorHom (0 : I) P)
        (hP.map (pairedStandardFibreOperatorHom 0)) (pairedStandardFibreProjection_compact 0 P hc) =
      standardCountableRelativeProjectionIndex (pairedStandardFibreOperatorHom (1 : I) P)
        (hP.map (pairedStandardFibreOperatorHom 1)) (pairedStandardFibreProjection_compact 1 P hc) := by
  obtain ⟨n, hn⟩ := exists_standardCountableAdmissibleProjectionCutoff (B := C(I, B)) P hc
  rw [standardCountableRelativeProjectionIndex_fibre_eq_finiteEvaluation (B := B) (0 : I) P hP hc n hn,
    standardCountableRelativeProjectionIndex_fibre_eq_finiteEvaluation (B := B) (1 : I) P hP hc n hn]
  exact unitizationRelativeProjectionEvaluation_k0_endpoints_eq (B := B)
    (standardCountableRoundedFiniteMatrix (B := B) P hP hc n)
    (pairedStandardFiniteReferenceMatrix (B := C(I, B)) n)
    (standardCountableRoundedFiniteMatrix_isStarProjection (B := B) P hP hc n hn)
    (pairedStandardFiniteReferenceMatrix_isStarProjection (B := C(I, B)) n)
    (standardCountableRoundedFiniteMatrix_scalar (B := B) P hP hc n)

end BC4lean.KKTheory
