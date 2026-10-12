import BC4lean.NonunitalOperatorK
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

/-! # Periodic scalar coefficients and genuine unitary functional calculus

A scalar interval loop with equal endpoints descends continuously to the
actual unit circle. The common-circle functional calculus evaluates such
coefficients at an actual unitary in a C*-algebra. Its naturality proves that
a coefficient vanishing at the circle base point has scalar part zero when
evaluated at a scalar-one unitization unitary, hence is an actual B coefficient.
No Bott map or odd comparison is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory

/-- Descend an actual continuous scalar interval loop using the endpoints
quotient and the genuine additive-circle homeomorphism. -/
def oddKTheoryDescendScalarLoop (f : ℝ → ℂ) (hf : Continuous f) (hends : f 0 = f 1) :
    C(Circle, ℂ) where
  toFun z := AddCircle.liftIco (1 : ℝ) 0 f
    ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm z)
  continuous_toFun :=
    (AddCircle.liftIco_zero_continuous hends hf.continuousOn).comp
      (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.continuous

/-- The actual half-open interval representative used only for scalar loop
evaluation; continuity belongs to the descended loop with equal endpoints. -/
def oddKTheoryCircleLoopParameter (z : Circle) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0
    ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm z) : ℝ)

theorem oddKTheoryDescendScalarLoop_apply
    (f : ℝ → ℂ) (hf : Continuous f) (hends : f 0 = f 1) (z : Circle) :
    oddKTheoryDescendScalarLoop f hf hends z = f (oddKTheoryCircleLoopParameter z) := rfl

@[simp] theorem oddKTheoryDescendScalarLoop_one
    (f : ℝ → ℂ) (hf : Continuous f) (hends : f 0 = f 1) :
    oddKTheoryDescendScalarLoop f hf hends 1 = f 0 := by
  let e := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have he : e.symm (1 : Circle) = 0 := by
    apply e.injective
    rw [e.apply_symm_apply]
    simp [e, AddCircle.homeomorphCircle_apply]
  change AddCircle.liftIco (1 : ℝ) 0 f (e.symm 1) = f 0
  rw [he]
  exact AddCircle.liftIco_zero_coe_apply (by norm_num : (0 : ℝ) ∈ Set.Ico 0 1)

/-- On the actual closed interval the descended function recovers its original
coefficient, including the identified upper endpoint. -/
theorem oddKTheoryDescendScalarLoop_apply_interval
    (f : ℝ → ℂ) (hf : Continuous f) (hends : f 0 = f 1)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    oddKTheoryDescendScalarLoop f hf hends (Circle.exp (2 * Real.pi * t)) = f t := by
  let e := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have he : e (t : AddCircle (1 : ℝ)) = Circle.exp (2 * Real.pi * t) := by
    rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk, div_one]
  rw [← he]
  change AddCircle.liftIco (1 : ℝ) 0 f (e.symm (e (t : AddCircle (1 : ℝ)))) = f t
  rw [e.symm_apply_apply]
  rcases lt_or_eq_of_le ht.2 with hlt | rfl
  · exact AddCircle.liftIco_zero_coe_apply ⟨ht.1, hlt⟩
  · have hp : ((1 : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      exact AddCircle.coe_period (p := (1 : ℝ))
    rw [hp]
    exact (AddCircle.liftIco_zero_coe_apply
      (by norm_num : (0 : ℝ) ∈ Set.Ico 0 1)).trans hends

section CircleCFC

variable {A C : Type*} [CStarAlgebra A] [CStarAlgebra C]

/-- The genuine continuous functional calculus with the whole unit circle as
its common domain. It is defined by the actual spectrum of the unitary. -/
def oddKTheoryCircleCFC (u : unitary A) : C(Circle, ℂ) →⋆ₐ[ℂ] A :=
  cfcHomSuperset (show IsStarNormal (u : A) from inferInstance)
    (Unitary.spectrum_subset_circle (𝕜 := ℂ) u)

theorem continuous_oddKTheoryCircleCFC (u : unitary A) :
    Continuous (oddKTheoryCircleCFC u) :=
  cfcHomSuperset_continuous _ _

/-- The circle coordinate evaluates to the actual input unitary. -/
@[simp] theorem oddKTheoryCircleCFC_coordinate (u : unitary A) :
    oddKTheoryCircleCFC u ((ContinuousMap.id ℂ).restrict (Metric.sphere 0 1)) = (u : A) :=
  cfcHomSuperset_id _ _

/-- Functional calculus of fixed continuous circle coefficients varies
continuously with actual coefficient unitaries. -/
theorem continuous_oddKTheoryCircleCFC_unitary (f : C(Circle, ℂ)) :
    Continuous (fun u : unitary A => oddKTheoryCircleCFC u f) :=
  continuous_cfcHomSuperset_left (isCompact_sphere (0 : ℂ) 1) f
    (fun u : unitary A => (u : A)) continuous_subtype_val
      (fun u => Unitary.spectrum_subset_circle (𝕜 := ℂ) u)

/-- Naturality uses the uniqueness of the actual continuous circle calculus;
both homomorphisms agree on the actual coordinate function. -/
theorem oddKTheoryCircleCFC_map (φ : A →⋆ₐ[ℂ] C) (hφ : Continuous φ)
    (u : unitary A) (v : unitary C) (huv : φ (u : A) = (v : C))
    (f : C(Circle, ℂ)) :
    φ (oddKTheoryCircleCFC u f) = oddKTheoryCircleCFC v f := by
  have hh : φ.comp (oddKTheoryCircleCFC u) = oddKTheoryCircleCFC v := by
    apply ContinuousMap.UniqueHom.eq_of_continuous_of_map_id (Metric.sphere (0 : ℂ) 1)
      _ _ (hφ.comp (continuous_oddKTheoryCircleCFC u)) (continuous_oddKTheoryCircleCFC v)
    change φ (oddKTheoryCircleCFC u ((ContinuousMap.id ℂ).restrict (Metric.sphere 0 1))) =
      oddKTheoryCircleCFC v ((ContinuousMap.id ℂ).restrict (Metric.sphere 0 1))
    rw [oddKTheoryCircleCFC_coordinate, oddKTheoryCircleCFC_coordinate, huv]
  exact DFunLike.congr_fun hh f

/-- At the scalar unitary 1 the genuine circle calculus is base-point
evaluation, as a consequence of uniqueness. -/
@[simp] theorem oddKTheoryCircleCFC_one (f : C(Circle, ℂ)) :
    oddKTheoryCircleCFC (1 : unitary ℂ) f = f 1 := by
  have hh : oddKTheoryCircleCFC (1 : unitary ℂ) =
      ContinuousMap.evalStarAlgHom ℂ ℂ (1 : Circle) := by
    apply ContinuousMap.UniqueHom.eq_of_continuous_of_map_id (Metric.sphere (0 : ℂ) 1)
      _ _ (continuous_oddKTheoryCircleCFC _) (continuous_eval_const _)
    change oddKTheoryCircleCFC (1 : unitary ℂ)
      ((ContinuousMap.id ℂ).restrict (Metric.sphere 0 1)) = ((1 : unitary ℂ) : ℂ)
    exact oddKTheoryCircleCFC_coordinate _
  exact DFunLike.congr_fun hh f

/-- At the identity of any actual C*-algebra the circle calculus is scalar
base-point evaluation followed by its genuine scalar inclusion. -/
theorem oddKTheoryCircleCFC_one_algebraMap (f : C(Circle, ℂ)) :
    oddKTheoryCircleCFC (1 : unitary A) f = algebraMap ℂ A (f 1) := by
  let ψ : C(Circle, ℂ) →⋆ₐ[ℂ] A :=
    (StarAlgHom.ofId ℂ A).comp (ContinuousMap.evalStarAlgHom ℂ ℂ (1 : Circle))
  have hh : oddKTheoryCircleCFC (1 : unitary A) = ψ := by
    apply ContinuousMap.UniqueHom.eq_of_continuous_of_map_id (Metric.sphere (0 : ℂ) 1)
      _ _ (continuous_oddKTheoryCircleCFC _)
        ((continuous_algebraMap ℂ A).comp (continuous_eval_const _))
    change oddKTheoryCircleCFC (1 : unitary A)
      ((ContinuousMap.id ℂ).restrict (Metric.sphere 0 1)) = algebraMap ℂ A 1
    exact (oddKTheoryCircleCFC_coordinate (1 : unitary A)).trans
      (map_one (algebraMap ℂ A)).symm
  exact DFunLike.congr_fun hh f

end CircleCFC

variable {B : Type*} [NonUnitalCStarAlgebra B]

/-- Scalar-one unitization unitaries evaluate each circle coefficient with
the correct scalar base-point value. -/
theorem oddKTheoryCircleCFC_scalar_part
    (u : unitary (Unitization ℂ B)) (hu : (u : Unitization ℂ B).fst = 1)
    (f : C(Circle, ℂ)) :
    (oddKTheoryCircleCFC u f).fst = f 1 := by
  have h := oddKTheoryCircleCFC_map (OperatorKTheory.scalarQuotient B)
    Unitization.continuous_fst u (1 : unitary ℂ) hu f
  change (oddKTheoryCircleCFC u f).fst = oddKTheoryCircleCFC (1 : unitary ℂ) f at h
  exact h.trans (oddKTheoryCircleCFC_one f)

/-- A base-point-vanishing circle coefficient has an actual coefficient in B,
extracted from the genuine forced unitization. -/
def oddKTheoryCircleCFCCoefficient (u : unitary (Unitization ℂ B))
    (f : C(Circle, ℂ)) : B := (oddKTheoryCircleCFC u f).snd

theorem oddKTheoryCircleCFC_eq_coefficient
    (u : unitary (Unitization ℂ B)) (hu : (u : Unitization ℂ B).fst = 1)
    (f : C(Circle, ℂ)) (hf : f 1 = 0) :
    oddKTheoryCircleCFC u f =
      (oddKTheoryCircleCFCCoefficient (B := B) u f : Unitization ℂ B) := by
  apply Unitization.ext
  · rw [oddKTheoryCircleCFC_scalar_part u hu f, hf, Unitization.fst_inr]
  · rfl

theorem continuous_oddKTheoryCircleCFCCoefficient (f : C(Circle, ℂ)) :
    Continuous (fun u : unitary (Unitization ℂ B) => oddKTheoryCircleCFCCoefficient u f) :=
  Unitization.continuous_snd.comp (continuous_oddKTheoryCircleCFC_unitary f)

end BC4lean.KKTheory
