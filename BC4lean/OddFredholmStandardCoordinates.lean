import BC4lean.StandardCountableCutoff
import BC4lean.FiniteModuleCompactMatrix

/-! # Actual finite coordinates for odd standard-module compression

The actual first-n coordinates define an adjointable isometry B^n→H_B
whose range projection is exactly the genuine standard cutoff. No coordinate
projection is declared compact for a nonunital coefficient algebra.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def oddFredholmStandardFiniteInclusion (n : ℕ) :
    AdjointableMap B (FiniteStandardModule B (Fin n)) (StandardCountableHilbertModule B) :=
  ∑ i : Fin n, (standardCountableInclusion i.val).comp (finiteStandardEvaluation i)

@[simp] theorem oddFredholmStandardFiniteInclusion_apply (n : ℕ)
    (x : FiniteStandardModule B (Fin n)) :
    oddFredholmStandardFiniteInclusion n x =
      ∑ i : Fin n, standardCountableInclusion i.val (x i) := by
  simp only [oddFredholmStandardFiniteInclusion, finiteAdjointable_sum_apply,
    AdjointableMap.comp_apply, finiteStandardEvaluation_apply]

@[simp] theorem oddFredholmStandardFiniteInclusion_adjoint_apply (n : ℕ)
    (x : StandardCountableHilbertModule B) (i : Fin n) :
    (oddFredholmStandardFiniteInclusion n).adjoint x i = standardCountableEvaluation i.val x := by
  rw [oddFredholmStandardFiniteInclusion, finiteAdjointable_sum_adjoint]
  simp only [AdjointableMap.adjoint_comp, finiteStandardEvaluation,
    AdjointableMap.adjoint_adjoint, finiteAdjointable_sum_apply, AdjointableMap.comp_apply]
  change finiteStandardEvaluation (B := B) i
      (∑ j : Fin n, finiteStandardInclusion (B := B) j
        (standardCountableEvaluation (B := B) j.val x)) = _
  rw [map_sum (finiteStandardEvaluation (B := B) i).toCLM]
  simp [finiteStandardEvaluation_apply, finiteStandardInclusion_apply,
    finiteStandardSingle_apply, Pi.single_apply]

@[simp] theorem oddFredholmStandardFiniteInclusion_adjoint_comp_self (n : ℕ) :
    (oddFredholmStandardFiniteInclusion (B := B) n).adjoint.comp
      (oddFredholmStandardFiniteInclusion n) = AdjointableMap.id := by
  ext x i
  simp only [AdjointableMap.comp_apply, oddFredholmStandardFiniteInclusion_adjoint_apply,
    oddFredholmStandardFiniteInclusion_apply]
  rw [map_sum (standardCountableEvaluation (B := B) i.val).toCLM]
  simp only [standardCountableEvaluation_inclusion, Fin.val_inj, AdjointableMap.id_apply]
  exact Fintype.sum_ite_eq' i (fun j : Fin n => x j)

@[simp] theorem oddFredholmStandardFiniteInclusion_comp_adjoint (n : ℕ) :
    (oddFredholmStandardFiniteInclusion (B := B) n).comp
      (oddFredholmStandardFiniteInclusion n).adjoint = standardCountableCutoff n := by
  ext x
  simp only [AdjointableMap.comp_apply, oddFredholmStandardFiniteInclusion_apply,
    oddFredholmStandardFiniteInclusion_adjoint_apply]
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => standardCountableInclusion (B := B) i
      (standardCountableEvaluation (B := B) i x)) n]
  exact (standardCountableCutoff_apply n x).symm

theorem oddFredholmStandardCutoff_mul_finiteInclusion (n : ℕ) :
    (standardCountableCutoff (B := B) n).comp (oddFredholmStandardFiniteInclusion n) =
      oddFredholmStandardFiniteInclusion n := by
  rw [← oddFredholmStandardFiniteInclusion_comp_adjoint]
  ext x
  change oddFredholmStandardFiniteInclusion n
    ((oddFredholmStandardFiniteInclusion n).adjoint
      (oddFredholmStandardFiniteInclusion n x)) = oddFredholmStandardFiniteInclusion n x
  have hh := congrArg (fun T => T x) (oddFredholmStandardFiniteInclusion_adjoint_comp_self (B := B) n)
  rw [AdjointableMap.comp_apply, AdjointableMap.id_apply] at hh
  rw [hh]

theorem oddFredholmStandardFiniteAdjoint_comp_cutoff (n : ℕ) :
    (oddFredholmStandardFiniteInclusion (B := B) n).adjoint.comp
      (standardCountableCutoff (B := B) n) =
      (oddFredholmStandardFiniteInclusion (B := B) n).adjoint := by
  have hh := congrArg
    (fun T : AdjointableMap B (FiniteStandardModule B (Fin n))
      (StandardCountableHilbertModule B) => T.adjoint)
    (oddFredholmStandardCutoff_mul_finiteInclusion (B := B) n)
  simpa only [AdjointableMap.adjoint_comp, AdjointableMap.adjoint_adjoint,
    ← AdjointableMap.star_eq_adjoint, standardCountableCutoff_star] using hh

end BC4lean.KKTheory
