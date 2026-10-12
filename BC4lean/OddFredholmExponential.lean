import BC4lean.CompactModuleStrongCutoff
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Tactic.Ring

/-! # The actual exponential unitary of a selfadjoint odd Fredholm operator

The scalar function `exp(iπ(z+1)) - 1` has zeros at both endpoints ±1.
Two divided differences give a globally continuous factor through `z²-1`.
Complex continuous functional calculus then proves that the actual exponential
unitary differs from the identity by a genuine compact module operator.

No quotient-algebra functional calculus, Bott periodicity, or operator K-group
identification is assumed. Finite-coordinate compression is proved to converge
in the operator norm; its eventual polar correction and the infinite-module
inverse to the odd index remain separate constructions.
-/

noncomputable section
namespace BC4lean.KKTheory

open Filter
open scoped Topology

/-- The scalar exponential defect has precisely the Fredholm endpoint zeros. -/
def oddFredholmExponentialDefect (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (Real.pi : ℂ) * (z + 1)) - 1

@[simp] theorem oddFredholmExponentialDefect_neg_one :
    oddFredholmExponentialDefect (-1) = 0 := by
  simp [oddFredholmExponentialDefect]

@[simp] theorem oddFredholmExponentialDefect_one :
    oddFredholmExponentialDefect 1 = 0 := by
  have h : Complex.I * (Real.pi : ℂ) * ((1 : ℂ) + 1) =
      2 * (Real.pi : ℂ) * Complex.I := by ring
  rw [oddFredholmExponentialDefect, h, Complex.exp_two_pi_mul_I, sub_self]

theorem oddFredholmExponentialDefect_differentiable :
    Differentiable ℂ oddFredholmExponentialDefect := by
  intro z
  exact (((differentiableAt_id.add_const 1).const_mul
    (Complex.I * (Real.pi : ℂ))).cexp).sub_const 1

theorem oddFredholmExponentialDefect_continuous :
    Continuous oddFredholmExponentialDefect :=
  oddFredholmExponentialDefect_differentiable.continuous

/-- Remove the first endpoint zero by its actual differentiable divided difference. -/
def oddFredholmFirstDividedDifference : ℂ → ℂ :=
  dslope oddFredholmExponentialDefect (-1)

theorem oddFredholmFirstDividedDifference_continuous :
    Continuous oddFredholmFirstDividedDifference := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z = -1
  · subst z
    exact continuousAt_dslope_same.mpr (oddFredholmExponentialDefect_differentiable (-1))
  · exact (continuousAt_dslope_of_ne hz).mpr
      oddFredholmExponentialDefect_continuous.continuousAt

@[simp] theorem oddFredholmFirstDividedDifference_one :
    oddFredholmFirstDividedDifference 1 = 0 := by
  change dslope oddFredholmExponentialDefect (-1) 1 = 0
  rw [dslope_of_ne _ (show (1 : ℂ) ≠ -1 by norm_num), slope_def_field,
    oddFredholmExponentialDefect_one, oddFredholmExponentialDefect_neg_one]
  simp

/-- Remove the second endpoint zero. The first divided difference is smooth
at `1` because its first exceptional point is `-1`. -/
def oddFredholmExponentialFactor : ℂ → ℂ :=
  dslope oddFredholmFirstDividedDifference 1

theorem oddFredholmExponentialFactor_continuous :
    Continuous oddFredholmExponentialFactor := by
  have hdiff : DifferentiableAt ℂ oddFredholmFirstDividedDifference 1 :=
    (differentiableAt_dslope_of_ne (show (1 : ℂ) ≠ -1 by norm_num)).mpr
      (oddFredholmExponentialDefect_differentiable 1)
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z = 1
  · subst z
    exact continuousAt_dslope_same.mpr hdiff
  · exact (continuousAt_dslope_of_ne hz).mpr
      oddFredholmFirstDividedDifference_continuous.continuousAt

/-- An exact factorization, valid also at both removable singularities. -/
theorem oddFredholmExponentialDefect_factor (z : ℂ) :
    oddFredholmExponentialDefect z = (z ^ 2 - 1) * oddFredholmExponentialFactor z := by
  have hfirst := sub_smul_dslope oddFredholmExponentialDefect (-1) z
  have hsecond := sub_smul_dslope oddFredholmFirstDividedDifference 1 z
  change (z - (-1)) • oddFredholmFirstDividedDifference z =
    oddFredholmExponentialDefect z - oddFredholmExponentialDefect (-1) at hfirst
  change (z - 1) • oddFredholmExponentialFactor z =
    oddFredholmFirstDividedDifference z - oddFredholmFirstDividedDifference 1 at hsecond
  simp only [oddFredholmExponentialDefect_neg_one,
    oddFredholmFirstDividedDifference_one, sub_zero, smul_eq_mul] at hfirst hsecond
  calc
    oddFredholmExponentialDefect z = (z + 1) * oddFredholmFirstDividedDifference z := by
      simpa only [sub_neg_eq_add] using hfirst.symm
    _ = (z + 1) * ((z - 1) * oddFredholmExponentialFactor z) := by rw [hsecond]
    _ = (z ^ 2 - 1) * oddFredholmExponentialFactor z := by ring

section Algebra

variable {A : Type*} [CStarAlgebra A]

/-- The genuine unitary `exp(iπ(F+1))` of a selfadjoint operator. -/
def oddFredholmExponential (F : selfAdjoint A) : unitary A :=
  selfAdjoint.expUnitary (Real.pi • (F + 1))

theorem continuous_oddFredholmExponential :
    Continuous (oddFredholmExponential : selfAdjoint A → unitary A) :=
  selfAdjoint.continuous_expUnitary.comp (by fun_prop)

/-- The operator exponential and the complex functional-calculus exponential
are the same actual element. -/
theorem oddFredholmExponential_eq_cfc (F : selfAdjoint A) :
    (oddFredholmExponential F : A) =
      cfc (fun z : ℂ => Complex.exp (Complex.I * (Real.pi : ℂ) * (z + 1))) (F : A) := by
  let phase : ℂ → ℂ := fun z => Complex.I * (Real.pi : ℂ) * (z + 1)
  have hnormal : IsStarNormal (F : A) := inferInstance
  have hphase : cfc phase (F : A) =
      Complex.I • (Real.pi • ((F : A) + 1)) := by
    dsimp only [phase]
    rw [cfc_const_mul (Complex.I * (Real.pi : ℂ)) (fun z : ℂ => z + 1)
      (F : A) (by fun_prop),
      cfc_add_const (1 : ℂ) (fun z : ℂ => z) (F : A)
        continuous_id.continuousOn hnormal,
      cfc_id' ℂ (F : A) hnormal]
    simp only [map_one, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
    change (Complex.I * (Real.pi : ℂ)) • ((F : A) + 1) =
      (Complex.I * (Real.pi : ℂ)) • ((F : A) + 1)
    rfl
  change NormedSpace.exp (Complex.I • (Real.pi • ((F : A) + 1))) = _
  rw [← hphase, ← CFC.complex_exp_eq_normedSpace_exp
    (a := cfc phase (F : A)) (cfc_predicate phase (F : A))]
  exact (cfc_comp' Complex.exp phase (F : A) (by fun_prop) (by fun_prop) hnormal).symm

/-- The compactness proof uses the full, exact scalar factorization and the
genuine CFC multiplication theorem. -/
theorem oddFredholmExponential_sub_one_factor (F : selfAdjoint A) :
    (oddFredholmExponential F : A) - 1 =
      ((F : A) ^ 2 - 1) * cfc oddFredholmExponentialFactor (F : A) := by
  have hnormal : IsStarNormal (F : A) := inferInstance
  have hdefect : (oddFredholmExponential F : A) - 1 =
      cfc oddFredholmExponentialDefect (F : A) := by
    rw [oddFredholmExponential_eq_cfc]
    change cfc (fun z : ℂ => Complex.exp (Complex.I * (Real.pi : ℂ) * (z + 1)))
        (F : A) - 1 =
      cfc (fun z : ℂ => Complex.exp (Complex.I * (Real.pi : ℂ) * (z + 1)) - 1) (F : A)
    rw [cfc_sub (fun z : ℂ => Complex.exp (Complex.I * (Real.pi : ℂ) * (z + 1)))
      (fun _ : ℂ => 1) (F : A) (by fun_prop) continuous_const.continuousOn,
      cfc_const_one ℂ (F : A) hnormal]
  rw [hdefect]
  calc
    cfc oddFredholmExponentialDefect (F : A) =
        cfc (fun z : ℂ => (z ^ 2 - 1) * oddFredholmExponentialFactor z) (F : A) :=
      cfc_congr (fun z _ => oddFredholmExponentialDefect_factor z)
    _ = cfc (fun z : ℂ => z ^ 2 - 1) (F : A) *
        cfc oddFredholmExponentialFactor (F : A) :=
      cfc_mul (fun z : ℂ => z ^ 2 - 1) oddFredholmExponentialFactor (F : A)
        (by fun_prop) oddFredholmExponentialFactor_continuous.continuousOn
    _ = ((F : A) ^ 2 - 1) * cfc oddFredholmExponentialFactor (F : A) := by
      rw [cfc_sub (fun z : ℂ => z ^ 2) (fun _ : ℂ => 1) (F : A)
        (by fun_prop) continuous_const.continuousOn,
        cfc_pow_id (R := ℂ) (F : A) 2 hnormal,
        cfc_const_one ℂ (F : A) hnormal]

end Algebra

section Module

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

/-- The actual exponential index unitary differs from the identity by a
genuine compact module operator. Contractivity is not needed for this fact. -/
theorem oddFredholmExponential_sub_one_isModuleCompact
    (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact
      ((F : AdjointableMap B E E) * (F : AdjointableMap B E E) - 1)) :
    IsModuleCompact ((oddFredholmExponential F : AdjointableMap B E E) - 1) := by
  rw [oddFredholmExponential_sub_one_factor]
  apply mul_mem_moduleCompact_right
  change IsModuleCompact ((F : AdjointableMap B E E) ^ 2 - 1)
  simpa only [pow_two] using hF

/-- The genuine finite-coordinate approximants converge in the operator norm
to the actual odd index unitary. They are not asserted to be unitary yet. -/
theorem oddFredholmExponential_standardCutoff_tendsto
    (F : selfAdjoint (AdjointableMap B (StandardCountableHilbertModule B)
      (StandardCountableHilbertModule B)))
    (hF : IsModuleCompact ((F : AdjointableMap B (StandardCountableHilbertModule B)
      (StandardCountableHilbertModule B)) *
        (F : AdjointableMap B (StandardCountableHilbertModule B)
          (StandardCountableHilbertModule B)) - 1)) :
    Tendsto (fun n => 1 + standardCountableCutoff n *
      ((oddFredholmExponential F : AdjointableMap B (StandardCountableHilbertModule B)
        (StandardCountableHilbertModule B)) - 1) * standardCountableCutoff n)
      atTop (𝓝 (oddFredholmExponential F : AdjointableMap B (StandardCountableHilbertModule B)
        (StandardCountableHilbertModule B))) := by
  have h := standardCountableCutoff_mul_mul_tendsto
    (oddFredholmExponential_sub_one_isModuleCompact F hF)
  simpa only [add_sub_cancel] using h.const_add 1

end Module
end BC4lean.KKTheory
