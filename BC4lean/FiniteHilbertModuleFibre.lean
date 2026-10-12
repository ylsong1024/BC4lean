import BC4lean.FiniteHilbertModuleSum
import BC4lean.GradedMatrixMoritaFibreEvaluation
import BC4lean.IntervalModuleCompactFibre

/-! # Completed fibres of actual finite Hilbert module sums

Coordinate evaluation preserves the whole coefficient-valued pairing. It
therefore descends through the evaluated radical and completion. Surjectivity
comes from actual preimages in each completed module fibre.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B X M ι : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, B)ᵐᵒᵖ M]
  [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M] [Fintype ι] [DecidableEq ι]

local instance oddContinuationFiniteHilbertModuleFibreLocalInstance01 : CompleteSpace (FiniteHilbertModuleSum C(X, B) M ι) := finiteHilbertModuleSum_complete
local instance oddContinuationFiniteHilbertModuleFibreLocalInstance02 (t : X) : CompleteSpace (FiniteHilbertModuleSum B (HilbertModuleFibre B M t) ι) :=
  finiteHilbertModuleSum_complete

def finiteHilbertModuleFibreEvaluationLinear (t : X) :
    FiniteHilbertModuleSum C(X, B) M ι →ₗ[ℂ]
      FiniteHilbertModuleSum B (HilbertModuleFibre B M t) ι where
  toFun x := (WithCStarModule.equiv _ _).symm (fun i => hilbertModuleFibreMk (B := B) t (x i))
  map_add' x y := by ext i; exact map_add (hilbertModuleFibreMk (B := B) t) (x i) (y i)
  map_smul' c x := by ext i; exact map_smul (hilbertModuleFibreMk (B := B) t) c (x i)

omit [T2Space X] [CompleteSpace M] [Fintype ι] [DecidableEq ι] in
@[simp] theorem finiteHilbertModuleFibreEvaluationLinear_apply (t : X)
    (x : FiniteHilbertModuleSum C(X, B) M ι) (i : ι) :
    finiteHilbertModuleFibreEvaluationLinear t x i = hilbertModuleFibreMk (B := B) t (x i) := rfl

omit [T2Space X] [CompleteSpace M] [DecidableEq ι] in
theorem finiteHilbertModuleFibreEvaluationLinear_inner (t : X)
    (x y : FiniteHilbertModuleSum C(X, B) M ι) :
    ⟪finiteHilbertModuleFibreEvaluationLinear t x, finiteHilbertModuleFibreEvaluationLinear t y⟫_(Bᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪x, y⟫_(C(X, B)ᵐᵒᵖ) t) := by
  simp only [WithCStarModule.pi_inner, finiteHilbertModuleFibreEvaluationLinear_apply,
    hilbertModuleFibre_inner_mk, Finset.unop_sum, ContinuousMap.coe_sum, Finset.sum_apply,
    Finset.op_sum]

omit [T2Space X] [CompleteSpace M] [DecidableEq ι] in
theorem finiteHilbertModuleFibreEvaluationLinear_norm_le (t : X)
    (x : FiniteHilbertModuleSum C(X, B) M ι) :
    ‖finiteHilbertModuleFibreEvaluationLinear t x‖ ≤ 1 * ‖x‖ := by
  rw [one_mul, CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ)
      (E := FiniteHilbertModuleSum B (HilbertModuleFibre B M t) ι)
      (finiteHilbertModuleFibreEvaluationLinear (B := B) (M := M) (ι := ι) t x),
    CStarModule.norm_eq_sqrt_norm_inner_self (A := C(X, B)ᵐᵒᵖ)
      (E := FiniteHilbertModuleSum C(X, B) M ι) x,
    finiteHilbertModuleFibreEvaluationLinear_inner]
  apply Real.sqrt_le_sqrt
  simpa only [MulOpposite.norm_op, MulOpposite.norm_unop] using
    (MulOpposite.unop ⟪x, x⟫_(C(X, B)ᵐᵒᵖ)).norm_coe_le_norm t

def finiteHilbertModuleFibreEvaluation (t : X) :
    FiniteHilbertModuleSum C(X, B) M ι →L[ℂ]
      FiniteHilbertModuleSum B (HilbertModuleFibre B M t) ι :=
  (finiteHilbertModuleFibreEvaluationLinear (B := B) (X := X) (M := M) (ι := ι) t).mkContinuous 1
    (finiteHilbertModuleFibreEvaluationLinear_norm_le (B := B) (X := X) (M := M) (ι := ι) t)

def finiteHilbertModuleFibreIsometry (t : X) :
    HilbertModuleFibre B (FiniteHilbertModuleSum C(X, B) M ι) t →ₗᵢ[ℂ]
      FiniteHilbertModuleSum B (HilbertModuleFibre B M t) ι :=
  GradedMatrixMoritaFibreEvaluation.completedIsometry (B := B) (X := X)
    (M := FiniteHilbertModuleSum C(X, B) M ι)
    (H := FiniteHilbertModuleSum B (HilbertModuleFibre B M t) ι) t
    (finiteHilbertModuleFibreEvaluation (B := B) (X := X) (M := M) (ι := ι) t)
    (finiteHilbertModuleFibreEvaluationLinear_inner (B := B) (X := X) (M := M) (ι := ι) t)

omit [T2Space X] [CompleteSpace M] [DecidableEq ι] in
@[simp] theorem finiteHilbertModuleFibreIsometry_mk (t : X)
    (x : FiniteHilbertModuleSum C(X, B) M ι) :
    finiteHilbertModuleFibreIsometry t (hilbertModuleFibreMk (B := B) t x) =
      finiteHilbertModuleFibreEvaluation t x :=
  GradedMatrixMoritaFibreEvaluation.completedIsometry_mk (B := B) (X := X)
    (M := FiniteHilbertModuleSum C(X, B) M ι)
    (H := FiniteHilbertModuleSum B (HilbertModuleFibre B M t) ι) t
    (finiteHilbertModuleFibreEvaluation (B := B) (X := X) (M := M) (ι := ι) t)
    (finiteHilbertModuleFibreEvaluationLinear_inner (B := B) (X := X) (M := M) (ι := ι) t) x

omit [DecidableEq ι] in
theorem finiteHilbertModuleFibreIsometry_surjective (t : X) :
    Function.Surjective (finiteHilbertModuleFibreIsometry (B := B) (M := M) (ι := ι) t) := by
  intro y
  choose x hx using fun i => hilbertModuleFibreMk_surjective (B := B) (M := M) t (y i)
  refine ⟨hilbertModuleFibreMk (B := B) t ((WithCStarModule.equiv _ _).symm x), ?_⟩
  rw [finiteHilbertModuleFibreIsometry_mk]
  ext i
  exact hx i

def finiteHilbertModuleFibreEquiv (t : X) :
    HilbertModuleEquiv B (HilbertModuleFibre B (FiniteHilbertModuleSum C(X, B) M ι) t)
      (FiniteHilbertModuleSum B (HilbertModuleFibre B M t) ι) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective
    (finiteHilbertModuleFibreIsometry (B := B) (X := X) (M := M) (ι := ι) t)
    (finiteHilbertModuleFibreIsometry_surjective (B := B) (X := X) (M := M) (ι := ι) t)
  inner_map := GradedMatrixMoritaFibreEvaluation.completedIsometry_inner (B := B) (X := X)
    (M := FiniteHilbertModuleSum C(X, B) M ι)
    (H := FiniteHilbertModuleSum B (HilbertModuleFibre B M t) ι) t
    (finiteHilbertModuleFibreEvaluation (B := B) (X := X) (M := M) (ι := ι) t)
    (finiteHilbertModuleFibreEvaluationLinear_inner (B := B) (X := X) (M := M) (ι := ι) t)

omit [DecidableEq ι] in
@[simp] theorem finiteHilbertModuleFibreEquiv_mk (t : X)
    (x : FiniteHilbertModuleSum C(X, B) M ι) (i : ι) :
    finiteHilbertModuleFibreEquiv t (hilbertModuleFibreMk (B := B) t x) i =
      hilbertModuleFibreMk (B := B) t (x i) := by
  change finiteHilbertModuleFibreIsometry t (hilbertModuleFibreMk (B := B) t x) i = _
  rw [finiteHilbertModuleFibreIsometry_mk]
  rfl

end BC4lean.KKTheory
