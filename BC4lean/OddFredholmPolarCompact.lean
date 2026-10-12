import BC4lean.OddFredholmPolarUnitary
import BC4lean.LocalizedModuleFunctionalCalculus

/-! # Compact-preserving polar interpolation and genuine cutoff unitaries

An invertible compact perturbation of the identity polar-normalizes to an
actual compact perturbation unitary. The proof applies the proved real CFC
compact-ideal lemma to the positive Gram square root and uses an actual ring
inverse. Radius-one approximation gives an explicit norm-continuous unitary
path, preserving the compact ideal throughout. Applied to the genuine strong
standard-module cutoffs, this supplies eventual actual unitary approximants.
-/

noncomputable section
namespace BC4lean.KKTheory

open Filter
open scoped Ring Topology unitInterval

section Interpolation

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- The radius-one criterion also covers the zero C*-algebra. -/
theorem oddFredholmIsUnit_of_norm_sub_unitary_lt_one_all
    (a : A) (U : unitary A) (h : ‖a - (U : A)‖ < 1) : IsUnit a := by
  by_cases hA : Nontrivial A
  · let := hA
    exact oddFredholmIsUnit_of_norm_sub_unitary_lt_one a U h
  · have : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
    rw [Subsingleton.elim a 1]
    exact isUnit_one

omit [PartialOrder A] [StarOrderedRing A] in
/-- The actual affine interpolation is inside the radius-one invertible
neighborhood whenever its endpoint is inside that neighborhood. -/
theorem oddFredholmPolarInterpolation_isUnit (U : unitary A) (a : A)
    (h : ‖a - (U : A)‖ < 1) (t : I) :
    IsUnit ((U : A) + (t : ℂ) • (a - U)) := by
  apply oddFredholmIsUnit_of_norm_sub_unitary_lt_one_all _ U
  have heq : (U : A) + (t : ℂ) • (a - U) - U = (t : ℂ) • (a - U) := by abel
  rw [heq, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg t.2.1]
  calc
    (t : ℝ) * ‖a - (U : A)‖ ≤ 1 * ‖a - (U : A)‖ :=
      mul_le_mul_of_nonneg_right t.2.2 (norm_nonneg _)
    _ < 1 := by simpa only [one_mul] using h

/-- A concrete actual unitary path joins the input unitary to its nearby
approximant's polar correction. -/
def oddFredholmPolarInterpolation (U : unitary A) (a : A)
    (h : ‖a - (U : A)‖ < 1) :
    Path U (oddFredholmPolarUnitary a
      (oddFredholmIsUnit_of_norm_sub_unitary_lt_one_all a U h)) where
  toFun t := oddFredholmPolarUnitary ((U : A) + (t : ℂ) • (a - U))
    (oddFredholmPolarInterpolation_isUnit U a h t)
  continuous_toFun :=
    (continuousOn_oddFredholmPolarElement.comp_continuous (by fun_prop)
      (oddFredholmPolarInterpolation_isUnit U a h)).subtype_mk _
  source' := by
    apply Subtype.ext
    simp only [Set.Icc.coe_zero, Complex.ofReal_zero, zero_smul, add_zero,
      oddFredholmPolarUnitary, oddFredholmPolarElement_unitary]
  target' := by
    apply Subtype.ext
    have heq : (U : A) + (a - U) = a := by abel
    simp only [Set.Icc.coe_one, Complex.ofReal_one, one_smul,
      oddFredholmPolarUnitary, heq]

end Interpolation

section Module

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

local instance oddContinuationOddFredholmPolarCompactLocalInstance01 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance oddContinuationOddFredholmPolarCompactLocalInstance02 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _

omit [CompleteSpace E] in
/-- Actual inverse preserves the compact perturbation ideal at invertibles. -/
theorem oddFredholmRingInverse_sub_one_isModuleCompact
    (a : AdjointableMap B E E) (ha : IsUnit a) (hcompact : IsModuleCompact (a - 1)) :
    IsModuleCompact (a⁻¹ʳ - 1) := by
  have heq : a⁻¹ʳ - 1 = -(a⁻¹ʳ * (a - 1)) := by
    rw [mul_sub, Ring.inverse_mul_cancel a ha, mul_one]
    abel
  rw [heq]
  exact IsModuleCompact.neg (mul_mem_moduleCompact_left a⁻¹ʳ hcompact)

omit [CompleteSpace E] in
theorem oddFredholmGram_sub_one_isModuleCompact
    (a : AdjointableMap B E E) (hcompact : IsModuleCompact (a - 1)) :
    IsModuleCompact (star a * a - 1) := by
  have hstar : IsModuleCompact (star a - 1) := by
    have h := hcompact.adjoint
    change IsModuleCompact (star (a - 1)) at h
    simpa only [star_sub, star_one] using h
  have heq : star a * a - 1 = star a * (a - 1) + (star a - 1) := by noncomm_ring
  rw [heq]
  exact IsModuleCompact.add (mul_mem_moduleCompact_left (star a) hcompact) hstar

/-- Genuine continuous functional calculus preserves this compact Gram
defect. The real square-root function is globally continuous. -/
theorem oddFredholmGramSqrt_sub_one_isModuleCompact
    (a : AdjointableMap B E E) (hcompact : IsModuleCompact (a - 1)) :
    IsModuleCompact (CFC.sqrt (star a * a) - 1) := by
  have hgram := oddFredholmGram_sub_one_isModuleCompact a hcompact
  have h := cfc_sub_value_mul_isModuleCompact (star a * a) 1
    (IsSelfAdjoint.star_mul_self a) 1 (by simpa only [map_one, mul_one] using hgram)
    Real.sqrt Real.continuous_sqrt
  rw [CFC.sqrt_eq_real_sqrt _ (star_mul_self_nonneg a), cfcₙ_eq_cfc]
  simpa only [Real.sqrt_one, map_one, mul_one] using h

/-- The polar correction is a genuine compact perturbation unitary. -/
theorem oddFredholmPolarElement_sub_one_isModuleCompact
    (a : AdjointableMap B E E) (ha : IsUnit a) (hcompact : IsModuleCompact (a - 1)) :
    IsModuleCompact (oddFredholmPolarElement a - 1) := by
  have hs := oddFredholmGramSqrt_sub_one_isModuleCompact a hcompact
  have hinv := oddFredholmRingInverse_sub_one_isModuleCompact _
    (oddFredholmGramSqrt_isUnit a ha) hs
  have heq : oddFredholmPolarElement a - 1 =
      a * ((CFC.sqrt (star a * a))⁻¹ʳ - 1) + (a - 1) := by
    rw [oddFredholmPolarElement]
    noncomm_ring
  rw [heq]
  exact IsModuleCompact.add (mul_mem_moduleCompact_left a hinv) hcompact

/-- The explicit nearby-unitary path stays inside the genuine compact
perturbations of the identity at every point. -/
theorem oddFredholmPolarInterpolation_sub_one_isModuleCompact
    (U : unitary (AdjointableMap B E E)) (a : AdjointableMap B E E)
    (h : ‖a - (U : AdjointableMap B E E)‖ < 1)
    (hU : IsModuleCompact ((U : AdjointableMap B E E) - 1))
    (ha : IsModuleCompact (a - 1)) (t : I) :
    IsModuleCompact ((oddFredholmPolarInterpolation U a h t : AdjointableMap B E E) - 1) := by
  apply oddFredholmPolarElement_sub_one_isModuleCompact _
    (oddFredholmPolarInterpolation_isUnit U a h t)
  have heq : (U : AdjointableMap B E E) + (t : ℂ) • (a - U) - 1 =
      (U - 1) + (t : ℂ) • ((a - 1) - (U - 1)) := by module
  rw [heq]
  exact hU.add ((ha.sub hU).smul (t : ℂ))

end Module

abbrev OddFredholmStandardOperator (B : Type*) [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] :=
  AdjointableMap B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)

section StandardCutoff

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

local instance oddContinuationOddFredholmPolarCompactLocalInstance03 : PartialOrder (OddFredholmStandardOperator B) := CStarAlgebra.spectralOrder _
local instance oddContinuationOddFredholmPolarCompactLocalInstance04 : StarOrderedRing (OddFredholmStandardOperator B) := CStarAlgebra.spectralOrderedRing _

/-- The actual finite-coordinate compact perturbation before polar correction. -/
def oddFredholmUnitaryCutoff (U : unitary (OddFredholmStandardOperator B)) (n : ℕ) :
    OddFredholmStandardOperator B :=
  1 + standardCountableCutoff n * ((U : OddFredholmStandardOperator B) - 1) *
    standardCountableCutoff n

theorem oddFredholmUnitaryCutoff_sub_one_isModuleCompact
    (U : unitary (OddFredholmStandardOperator B))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) (n : ℕ) :
    IsModuleCompact (oddFredholmUnitaryCutoff U n - 1) := by
  simp only [oddFredholmUnitaryCutoff, add_sub_cancel_left]
  exact mul_mem_moduleCompact_right
    (mul_mem_moduleCompact_left (standardCountableCutoff n) hU) _

theorem oddFredholmUnitaryCutoff_tendsto
    (U : unitary (OddFredholmStandardOperator B))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) :
    Tendsto (oddFredholmUnitaryCutoff U) atTop (𝓝 (U : OddFredholmStandardOperator B)) := by
  change Tendsto
    (fun n => (1 : AdjointableMap B (StandardCountableHilbertModule B)
      (StandardCountableHilbertModule B)) + standardCountableCutoff n *
        ((U : AdjointableMap B (StandardCountableHilbertModule B)
          (StandardCountableHilbertModule B)) - 1) * standardCountableCutoff n)
    atTop (𝓝 (U : AdjointableMap B (StandardCountableHilbertModule B)
      (StandardCountableHilbertModule B)))
  have h := standardCountableCutoff_mul_mul_tendsto hU
  simpa only [add_sub_cancel] using h.const_add 1

/-- Genuine strong compact cutoffs eventually lie inside the concrete
radius-one polar neighborhood of the actual index unitary. -/
theorem oddFredholmUnitaryCutoff_eventually_near
    (U : unitary (OddFredholmStandardOperator B))
    (hU : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1)) :
    ∀ᶠ n in atTop, ‖oddFredholmUnitaryCutoff U n - (U : OddFredholmStandardOperator B)‖ < 1 := by
  have h := ((oddFredholmUnitaryCutoff_tendsto U hU).sub_const
    (U : OddFredholmStandardOperator B)).norm
  have hn : Tendsto (fun n => ‖oddFredholmUnitaryCutoff U n - (U : OddFredholmStandardOperator B)‖)
      atTop (𝓝 (0 : ℝ)) := by simpa only [sub_self, norm_zero] using h
  exact hn.eventually (gt_mem_nhds zero_lt_one)

end StandardCutoff
end BC4lean.KKTheory
