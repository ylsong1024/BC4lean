import BC4lean.StandardCountableModuleFibre
import BC4lean.StandardCountableFiniteCoordinates

/-! # Paired standard fibres and finite-coordinate evaluation

The paired evaluation is constructed from the two actual coefficient
evaluations. Its coefficient-inner-product identity and explicit constant
right inverse identify its genuine evaluated fibre with H_B ⊕ H_B.
The cutoffs, signed grading, interleaving, and finite coordinate inclusion
commute with this evaluation.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B X : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [StarOrderedRing B] [TopologicalSpace X] [CompactSpace X]

abbrev PairedStandardModule (B : Type*) [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] :=
  HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)

def pairedStandardCoefficientEvaluation (t : X) :
    PairedStandardModule C(X, B) →L[ℂ] PairedStandardModule B :=
  sumInlCLM.comp ((standardCountableCoefficientEvaluation t).comp sumFstCLM) +
    sumInrCLM.comp ((standardCountableCoefficientEvaluation t).comp sumSndCLM)

def pairedStandardCoefficientConstant :
    PairedStandardModule B →L[ℂ] PairedStandardModule C(X, B) :=
  sumInlCLM.comp (standardCountableCoefficientConstant.comp sumFstCLM) +
    sumInrCLM.comp (standardCountableCoefficientConstant.comp sumSndCLM)

@[simp] theorem pairedStandardCoefficientEvaluation_apply (t : X)
    (x : PairedStandardModule C(X, B)) :
    pairedStandardCoefficientEvaluation t x =
      sumMk (standardCountableCoefficientEvaluation t x.fst)
        (standardCountableCoefficientEvaluation t x.snd) := by
  change sumMk (B := B) (standardCountableCoefficientEvaluation (B := B) t x.fst)
      (0 : StandardCountableHilbertModule B) +
    sumMk (B := B) (0 : StandardCountableHilbertModule B)
      (standardCountableCoefficientEvaluation (B := B) t x.snd) = _
  simp only [sumMk_add, add_zero, zero_add]

@[simp] theorem pairedStandardCoefficientConstant_apply (x : PairedStandardModule B) :
    pairedStandardCoefficientConstant (X := X) x =
      sumMk (standardCountableCoefficientConstant x.fst) (standardCountableCoefficientConstant x.snd) := by
  change sumMk (B := C(X, B)) (standardCountableCoefficientConstant (B := B) (X := X) x.fst)
      (0 : StandardCountableHilbertModule C(X, B)) +
    sumMk (B := C(X, B)) (0 : StandardCountableHilbertModule C(X, B))
      (standardCountableCoefficientConstant (B := B) (X := X) x.snd) = _
  simp only [sumMk_add, add_zero, zero_add]

theorem pairedStandardCoefficientEvaluation_inner (t : X)
    (x y : PairedStandardModule C(X, B)) :
    ⟪pairedStandardCoefficientEvaluation t x, pairedStandardCoefficientEvaluation t y⟫_(Bᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪x, y⟫_(C(X, B)ᵐᵒᵖ) t) := by
  simp only [pairedStandardCoefficientEvaluation_apply, inner_sum, sumMk_fst, sumMk_snd,
    standardCountableCoefficientEvaluation_inner, MulOpposite.unop_add, ContinuousMap.add_apply,
    MulOpposite.op_add]

@[simp] theorem pairedStandardCoefficientEvaluation_constant (t : X) (x : PairedStandardModule B) :
    pairedStandardCoefficientEvaluation t (pairedStandardCoefficientConstant x) = x := by
  simp only [pairedStandardCoefficientEvaluation_apply, pairedStandardCoefficientConstant_apply,
    sumMk_fst, sumMk_snd, standardCountableCoefficientEvaluation_constant, sumMk_eta]

/-- The paired fibre identification is derived from the actual evaluated form. -/
def pairedStandardModuleFibreEquiv (t : X) :
    HilbertModuleEquiv B (HilbertModuleFibre B (PairedStandardModule C(X, B)) t)
      (PairedStandardModule B) :=
  hilbertModuleFibreEquivOfEvaluation t (pairedStandardCoefficientEvaluation t)
    (pairedStandardCoefficientEvaluation_inner t)
    (fun x => ⟨pairedStandardCoefficientConstant x, pairedStandardCoefficientEvaluation_constant t x⟩)

@[simp] theorem pairedStandardModuleFibreEquiv_mk (t : X)
    (x : PairedStandardModule C(X, B)) :
    pairedStandardModuleFibreEquiv (B := B) t (hilbertModuleFibreMk (B := B) t x) =
      pairedStandardCoefficientEvaluation t x :=
  hilbertModuleFibreEquivOfEvaluation_mk t _ _ _ x

theorem pairedStandardCoefficientEvaluation_cutoff (t : X) (n : ℕ)
    (x : PairedStandardModule C(X, B)) :
    pairedStandardCoefficientEvaluation t (standardCountablePairedCutoff n x) =
      standardCountablePairedCutoff n (pairedStandardCoefficientEvaluation t x) := by
  simp only [standardCountablePairedCutoff, sumMap_apply, pairedStandardCoefficientEvaluation_apply,
    sumMk_fst, sumMk_snd, standardCountableCoefficientEvaluation_cutoff]

theorem pairedStandardModuleFibreEquiv_cutoff (t : X) (n : ℕ)
    (x : HilbertModuleFibre B (PairedStandardModule C(X, B)) t) :
    pairedStandardModuleFibreEquiv (B := B) t
        (hilbertModuleFibreOperator (B := B) (M := PairedStandardModule C(X, B))
          t (standardCountablePairedCutoff n) x) =
      standardCountablePairedCutoff n (pairedStandardModuleFibreEquiv (B := B) t x) := by
  refine (hilbertModuleFibreMk_denseRange (B := B)
    (M := PairedStandardModule C(X, B)) t).induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro v
    calc
      _ = pairedStandardModuleFibreEquiv (B := B) t
          (hilbertModuleFibreMk (B := B) t
            (standardCountablePairedCutoff (B := C(X, B)) n v)) :=
        congrArg (fun z : HilbertModuleFibre B (PairedStandardModule C(X, B)) t =>
          pairedStandardModuleFibreEquiv (B := B) t z)
          (hilbertModuleFibreOperator_mk (B := B) (M := PairedStandardModule C(X, B))
            t (standardCountablePairedCutoff (B := C(X, B)) n) v)
      _ = pairedStandardCoefficientEvaluation (B := B) t
          (standardCountablePairedCutoff (B := C(X, B)) n v) :=
        pairedStandardModuleFibreEquiv_mk (B := B) t
          (standardCountablePairedCutoff (B := C(X, B)) n v)
      _ = standardCountablePairedCutoff (B := B) n
          (pairedStandardCoefficientEvaluation (B := B) t v) :=
        pairedStandardCoefficientEvaluation_cutoff (B := B) t n v
      _ = _ := congrArg (fun y : PairedStandardModule B =>
        (standardCountablePairedCutoff (B := B) n).toCLM y)
        (pairedStandardModuleFibreEquiv_mk (B := B) t v).symm

/-- The canonical reference Q=diag(0,I) is preserved by actual evaluation. -/
theorem pairedStandardCoefficientEvaluation_reference (t : X)
    (x : PairedStandardModule C(X, B)) :
    pairedStandardCoefficientEvaluation t (standardCountablePairedReferenceProjection x) =
      standardCountablePairedReferenceProjection (pairedStandardCoefficientEvaluation t x) := by
  simp [standardCountablePairedReferenceProjection, pairedStandardCoefficientEvaluation_apply, sumMap_apply]

theorem pairedStandardModuleFibreEquiv_reference (t : X)
    (x : HilbertModuleFibre B (PairedStandardModule C(X, B)) t) :
    pairedStandardModuleFibreEquiv (B := B) t
        (hilbertModuleFibreOperator (B := B) (M := PairedStandardModule C(X, B))
          t standardCountablePairedReferenceProjection x) =
      standardCountablePairedReferenceProjection (pairedStandardModuleFibreEquiv (B := B) t x) := by
  refine (hilbertModuleFibreMk_denseRange (B := B)
    (M := PairedStandardModule C(X, B)) t).induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro v
    calc
      _ = pairedStandardModuleFibreEquiv (B := B) t
          (hilbertModuleFibreMk (B := B) t
            (standardCountablePairedReferenceProjection (B := C(X, B)) v)) :=
        congrArg (fun z : HilbertModuleFibre B (PairedStandardModule C(X, B)) t =>
          pairedStandardModuleFibreEquiv (B := B) t z)
          (hilbertModuleFibreOperator_mk (B := B) (M := PairedStandardModule C(X, B))
            t (standardCountablePairedReferenceProjection (B := C(X, B))) v)
      _ = pairedStandardCoefficientEvaluation (B := B) t
          (standardCountablePairedReferenceProjection (B := C(X, B)) v) :=
        pairedStandardModuleFibreEquiv_mk (B := B) t
          (standardCountablePairedReferenceProjection (B := C(X, B)) v)
      _ = standardCountablePairedReferenceProjection (B := B)
          (pairedStandardCoefficientEvaluation (B := B) t v) :=
        pairedStandardCoefficientEvaluation_reference (B := B) t v
      _ = _ := congrArg (fun y : PairedStandardModule B =>
        (standardCountablePairedReferenceProjection (B := B)).toCLM y)
        (pairedStandardModuleFibreEquiv_mk (B := B) t v).symm

/-- The signed operator is the actual even/odd coordinate grading. -/
def pairedStandardSign : AdjointableMap B (PairedStandardModule B) (PairedStandardModule B) :=
  sumMap 1 (-1)

@[simp] theorem pairedStandardSign_apply (x : PairedStandardModule B) :
    pairedStandardSign x = sumMk x.fst (-x.snd) := by
  simp [pairedStandardSign, sumMap_apply]

theorem pairedStandardCoefficientEvaluation_sign (t : X) (x : PairedStandardModule C(X, B)) :
    pairedStandardCoefficientEvaluation t (pairedStandardSign x) =
      pairedStandardSign (pairedStandardCoefficientEvaluation t x) := by
  simp only [pairedStandardSign_apply, pairedStandardCoefficientEvaluation_apply,
    sumMk_fst, sumMk_snd, map_neg]

theorem pairedStandardModuleFibreEquiv_sign (t : X)
    (x : HilbertModuleFibre B (PairedStandardModule C(X, B)) t) :
    pairedStandardModuleFibreEquiv (B := B) t
        (hilbertModuleFibreOperator (B := B) (M := PairedStandardModule C(X, B))
          t pairedStandardSign x) =
      pairedStandardSign (pairedStandardModuleFibreEquiv (B := B) t x) := by
  refine (hilbertModuleFibreMk_denseRange (B := B)
    (M := PairedStandardModule C(X, B)) t).induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro v
    calc
      _ = pairedStandardModuleFibreEquiv (B := B) t
          (hilbertModuleFibreMk (B := B) t (pairedStandardSign (B := C(X, B)) v)) :=
        congrArg (fun z : HilbertModuleFibre B (PairedStandardModule C(X, B)) t =>
          pairedStandardModuleFibreEquiv (B := B) t z)
          (hilbertModuleFibreOperator_mk (B := B) (M := PairedStandardModule C(X, B))
            t (pairedStandardSign (B := C(X, B))) v)
      _ = pairedStandardCoefficientEvaluation (B := B) t
          (pairedStandardSign (B := C(X, B)) v) :=
        pairedStandardModuleFibreEquiv_mk (B := B) t (pairedStandardSign (B := C(X, B)) v)
      _ = pairedStandardSign (B := B) (pairedStandardCoefficientEvaluation (B := B) t v) :=
        pairedStandardCoefficientEvaluation_sign (B := B) t v
      _ = _ := congrArg (fun y : PairedStandardModule B => (pairedStandardSign (B := B)).toCLM y)
        (pairedStandardModuleFibreEquiv_mk (B := B) t v).symm

theorem pairedStandardCoefficientEvaluation_interleave (t : X) (e : ℕ ⊕ ℕ ≃ ℕ)
    (x : PairedStandardModule C(X, B)) :
    standardCountableCoefficientEvaluation t (standardCountableInterleave e x) =
      standardCountableInterleave e (pairedStandardCoefficientEvaluation t x) := by
  simp only [standardCountableInterleave_apply, pairedStandardCoefficientEvaluation_apply,
    sumMk_fst, sumMk_snd, map_add, standardCountableCoefficientEvaluation_embedding]

/-- Actual coefficient evaluation of a finite coordinate vector. -/
def finiteStandardCoefficientEvaluationVector {ι : Type*} (t : X)
    (x : FiniteStandardModule C(X, B) ι) : FiniteStandardModule B ι :=
  (WithCStarModule.equiv _ _).symm fun i => MulOpposite.op (MulOpposite.unop (x i) t)

omit [PartialOrder B] [StarOrderedRing B] [CompactSpace X] in
@[simp] theorem finiteStandardCoefficientEvaluationVector_apply {ι : Type*} (t : X)
    (x : FiniteStandardModule C(X, B) ι) (i : ι) :
    finiteStandardCoefficientEvaluationVector t x i = MulOpposite.op (MulOpposite.unop (x i) t) := rfl

theorem standardCountableCoefficientEvaluation_inclusion (t : X) (i : ℕ) (b : C(X, B)ᵐᵒᵖ) :
    standardCountableCoefficientEvaluation t (standardCountableInclusion i b) =
      standardCountableInclusion i (MulOpposite.op (MulOpposite.unop b t)) := by
  simp only [standardCountableInclusion_apply, standardCountableCoefficientEvaluation_mk]
  congr 1
  ext j
  simp only [standardFiniteCoefficientEvaluation_apply, Finsupp.single_apply]
  split_ifs <;> simp

theorem pairedStandardCoefficientEvaluation_coordinate (t : X) (n : ℕ)
    (i : PairedStandardFiniteIndex n) (b : C(X, B)ᵐᵒᵖ) :
    pairedStandardCoefficientEvaluation t (pairedStandardCoordinateInclusion n i b) =
      pairedStandardCoordinateInclusion n i (MulOpposite.op (MulOpposite.unop b t)) := by
  cases i with
  | inl j =>
    change pairedStandardCoefficientEvaluation (B := B) t
        (sumMk (B := C(X, B)) (standardCountableInclusion (B := C(X, B)) j.val b)
          (0 : StandardCountableHilbertModule C(X, B))) =
      sumMk (B := B)
        (standardCountableInclusion (B := B) j.val (MulOpposite.op (MulOpposite.unop b t)))
        (0 : StandardCountableHilbertModule B)
    simp only [pairedStandardCoefficientEvaluation_apply, sumMk_fst, sumMk_snd, map_zero]
    rw [standardCountableCoefficientEvaluation_inclusion]
  | inr j =>
    change pairedStandardCoefficientEvaluation (B := B) t
        (sumMk (B := C(X, B)) (0 : StandardCountableHilbertModule C(X, B))
          (standardCountableInclusion (B := C(X, B)) j.val b)) =
      sumMk (B := B) (0 : StandardCountableHilbertModule B)
        (standardCountableInclusion (B := B) j.val (MulOpposite.op (MulOpposite.unop b t)))
    simp only [pairedStandardCoefficientEvaluation_apply, sumMk_fst, sumMk_snd, map_zero]
    rw [standardCountableCoefficientEvaluation_inclusion]

/-- Evaluation preserves the actual finite isometry J_n, coefficient by coefficient. -/
theorem pairedStandardCoefficientEvaluation_finiteInclusion (t : X) (n : ℕ)
    (x : FiniteStandardModule C(X, B) (PairedStandardFiniteIndex n)) :
    pairedStandardCoefficientEvaluation t (pairedStandardFiniteInclusion n x) =
      pairedStandardFiniteInclusion n (finiteStandardCoefficientEvaluationVector t x) := by
  rw [pairedStandardFiniteInclusion_apply, map_sum]
  simp only [pairedStandardCoefficientEvaluation_coordinate, pairedStandardFiniteInclusion_apply,
    finiteStandardCoefficientEvaluationVector_apply]

theorem pairedStandardModuleFibreEquiv_finiteInclusion_mk (t : X) (n : ℕ)
    (x : FiniteStandardModule C(X, B) (PairedStandardFiniteIndex n)) :
    pairedStandardModuleFibreEquiv (B := B) t
        (hilbertModuleFibreMk (B := B) t (pairedStandardFiniteInclusion n x)) =
      pairedStandardFiniteInclusion n (finiteStandardCoefficientEvaluationVector t x) := by
  rw [pairedStandardModuleFibreEquiv_mk, pairedStandardCoefficientEvaluation_finiteInclusion]

theorem standardCountableCoefficientEvaluation_coordinate (t : X) (i : ℕ)
    (x : StandardCountableHilbertModule C(X, B)) :
    MulOpposite.op (MulOpposite.unop (standardCountableEvaluation i x) t) =
      standardCountableEvaluation i (standardCountableCoefficientEvaluation t x) := by
  refine (standardCountableMk_denseRange (B := C(X, B))).induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro v
    simp only [standardCountableEvaluation_mk, standardCountableCoefficientEvaluation_mk,
      standardFiniteCoefficientEvaluation_apply]

/-- The adjoint of J_n extracts the same actual finite coordinates after evaluation. -/
theorem pairedStandardCoefficientEvaluation_finiteInclusion_adjoint (t : X) (n : ℕ)
    (x : PairedStandardModule C(X, B)) :
    finiteStandardCoefficientEvaluationVector t ((pairedStandardFiniteInclusion n).adjoint x) =
      (pairedStandardFiniteInclusion n).adjoint (pairedStandardCoefficientEvaluation t x) := by
  ext i
  simp only [finiteStandardCoefficientEvaluationVector_apply,
    pairedStandardFiniteInclusion_adjoint_apply]
  cases i <;> simp only [pairedStandardCoordinateInclusion_adjoint_apply,
    pairedStandardCoefficientEvaluation_apply, sumMk_fst, sumMk_snd,
    standardCountableCoefficientEvaluation_coordinate]

theorem pairedStandardModuleFibreEquiv_interleave_mk (t : X) (e : ℕ ⊕ ℕ ≃ ℕ)
    (x : PairedStandardModule C(X, B)) :
    standardCountableModuleFibreEquiv (B := B) t
        (hilbertModuleFibreMk (B := B) t (standardCountableInterleave e x)) =
      standardCountableInterleave e
        (pairedStandardModuleFibreEquiv (B := B) t (hilbertModuleFibreMk (B := B) t x)) := by
  calc
    _ = standardCountableCoefficientEvaluation (B := B) t
        (standardCountableInterleave (B := C(X, B)) e x) :=
      standardCountableModuleFibreEquiv_mk (B := B) t
        (standardCountableInterleave (B := C(X, B)) e x)
    _ = standardCountableInterleave (B := B) e
        (pairedStandardCoefficientEvaluation (B := B) t x) :=
      pairedStandardCoefficientEvaluation_interleave (B := B) t e x
    _ = _ := congrArg (fun y : PairedStandardModule B =>
      (standardCountableInterleave (B := B) e).toCLM y)
      (pairedStandardModuleFibreEquiv_mk (B := B) t x).symm

end BC4lean.KKTheory
