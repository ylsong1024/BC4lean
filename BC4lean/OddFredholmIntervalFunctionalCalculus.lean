import BC4lean.OddFredholmRowNormalForm
import Mathlib.Topology.ContinuousMap.Star

/-! # Genuine interval functional calculus of a selfadjoint contraction

Complex CFC on the actual spectrum is pulled back from the real interval
[-1,1], using the proved real spectrum and norm bound. The scalar half-phase
evaluates to the actual operator half-phase; circle coefficients pulled back
along exp(iπ(r+1)) evaluate to the actual circle CFC of the exponential index.
The zero operator algebra is included, through its empty spectrum.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped CStarAlgebra

abbrev OddFredholmInterval := Set.Icc (-1 : ℝ) 1

def oddFredholmIntervalCoordinate : C(OddFredholmInterval, ℂ) :=
  ⟨fun r => ((r : ℝ) : ℂ), Complex.continuous_ofReal.comp continuous_subtype_val⟩

def oddFredholmIntervalParameter (r : OddFredholmInterval) : ℝ := ((r : ℝ) + 1) / 2

theorem oddFredholmIntervalParameter_mem (r : OddFredholmInterval) :
    oddFredholmIntervalParameter r ∈ Set.Icc 0 1 := by
  obtain ⟨hl, hu⟩ := r.property
  constructor <;> dsimp only [oddFredholmIntervalParameter] <;> linarith

def oddFredholmIntervalCircle : C(OddFredholmInterval, Circle) :=
  ⟨fun r => Circle.exp (2 * Real.pi * oddFredholmIntervalParameter r), by
    unfold oddFredholmIntervalParameter
    fun_prop⟩

def oddFredholmIntervalHalfPhase : C(OddFredholmInterval, ℂ) :=
  ⟨fun r => (oddKTheoryHalfPhase (oddFredholmIntervalParameter r) : ℂ),
    continuous_subtype_val.comp (continuous_oddKTheoryHalfPhase.comp (by
      unfold oddFredholmIntervalParameter
      fun_prop))⟩

variable {A : Type*} [CStarAlgebra A]

/-- The actual norm bound locates every complex spectral point in the
real interval, including the empty-spectrum zero algebra case. -/
theorem oddFredholmSpectrum_re_mem_interval (F : selfAdjoint A) (hF : ‖(F : A)‖ ≤ 1)
    {z : ℂ} (hz : z ∈ spectrum ℂ (F : A)) : z.re ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · let := hA
    simp only [spectrum.of_subsingleton, Set.mem_empty_iff_false] at hz
  · let := hA
    have hb : |z.re| ≤ 1 := (Complex.abs_re_le_norm z).trans
      ((spectrum.norm_le_norm_of_mem hz).trans hF)
    exact abs_le.mp hb

def oddFredholmSpectrumIntervalMap (F : selfAdjoint A) (hF : ‖(F : A)‖ ≤ 1) :
    C(spectrum ℂ (F : A), OddFredholmInterval) :=
  ⟨fun z => ⟨(z : ℂ).re, oddFredholmSpectrum_re_mem_interval F hF z.property⟩,
    (Complex.continuous_re.comp continuous_subtype_val).subtype_mk _⟩

/-- Actual complex functional calculus with the common real interval domain. -/
def oddFredholmIntervalCFC (F : selfAdjoint A) (hF : ‖(F : A)‖ ≤ 1) :
    C(OddFredholmInterval, ℂ) →⋆ₐ[ℂ] A :=
  (cfcHom (show IsStarNormal (F : A) from inferInstance) :
      C(spectrum ℂ (F : A), ℂ) →⋆ₐ[ℂ] A).comp
    (ContinuousMap.compStarAlgHom' ℂ ℂ (oddFredholmSpectrumIntervalMap F hF))

/-- A global continuous function restricted to the real interval evaluates
to its ordinary complex CFC at the actual selfadjoint contraction. -/
theorem oddFredholmIntervalCFC_eq_cfc (F : selfAdjoint A) (hF : ‖(F : A)‖ ≤ 1)
    (f : C(OddFredholmInterval, ℂ)) (g : ℂ → ℂ) (hg : Continuous g)
    (hfg : ∀ r : OddFredholmInterval, f r = g ((r : ℝ) : ℂ)) :
    oddFredholmIntervalCFC F hF f = cfc g (F : A) := by
  change (cfcHom (show IsStarNormal (F : A) from inferInstance) :
    C(spectrum ℂ (F : A), ℂ) →⋆ₐ[ℂ] A)
      (f.comp (oddFredholmSpectrumIntervalMap F hF)) = cfc g (F : A)
  rw [cfc_apply g (F : A) (show IsStarNormal (F : A) from inferInstance) hg.continuousOn]
  congr 1
  ext z
  rw [ContinuousMap.comp_apply, hfg]
  change g ((z : ℂ).re : ℂ) = g (z : ℂ)
  rw [← F.property.mem_spectrum_eq_re z.property]

@[simp] theorem oddFredholmIntervalCFC_coordinate (F : selfAdjoint A)
    (hF : ‖(F : A)‖ ≤ 1) :
    oddFredholmIntervalCFC F hF oddFredholmIntervalCoordinate = (F : A) := by
  rw [oddFredholmIntervalCFC_eq_cfc F hF _ id continuous_id (fun _ => rfl)]
  change cfc (fun x : ℂ => x) (F : A) = (F : A)
  exact cfc_id' ℂ (F : A)

/-- The actual half-phase is its full complex continuous functional calculus. -/
theorem oddFredholmRowHalfPhase_eq_cfc (F : selfAdjoint A) (s : ℝ) :
    (selfAdjoint.expUnitary ((Real.pi * s / 2) • (F + 1)) : A) =
      cfc (fun z : ℂ => Complex.exp
        (Complex.I * (((Real.pi * s / 2) : ℝ) : ℂ) * (z + 1))) (F : A) := by
  let phase : ℂ → ℂ := fun z => Complex.I * (((Real.pi * s / 2) : ℝ) : ℂ) * (z + 1)
  have hnormal : IsStarNormal (F : A) := inferInstance
  have hphase : cfc phase (F : A) =
      Complex.I • ((Real.pi * s / 2) • ((F : A) + 1)) := by
    dsimp only [phase]
    rw [cfc_const_mul (Complex.I * (((Real.pi * s / 2) : ℝ) : ℂ))
        (fun z : ℂ => z + 1) (F : A) (by fun_prop),
      cfc_add_const (1 : ℂ) (fun z : ℂ => z) (F : A)
        continuous_id.continuousOn hnormal,
      cfc_id' ℂ (F : A) hnormal]
    simp only [map_one, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
    change (Complex.I * (((Real.pi * s / 2) : ℝ) : ℂ)) • ((F : A) + 1) =
      (Complex.I * (((Real.pi * s / 2) : ℝ) : ℂ)) • ((F : A) + 1)
    rfl
  change NormedSpace.exp (Complex.I • ((Real.pi * s / 2) • ((F : A) + 1))) = _
  rw [← hphase, ← CFC.complex_exp_eq_normedSpace_exp
    (a := cfc phase (F : A)) (cfc_predicate phase (F : A))]
  exact (cfc_comp' Complex.exp phase (F : A) (by fun_prop) (by fun_prop) hnormal).symm

/-- The interval half-phase evaluates to the genuine operator half-phase
used by the explicit arbitrary-F row normal-form path. -/
theorem oddFredholmIntervalCFC_halfPhase (F : selfAdjoint A) (hF : ‖(F : A)‖ ≤ 1) :
    oddFredholmIntervalCFC F hF oddFredholmIntervalHalfPhase =
      (selfAdjoint.expUnitary ((Real.pi * 1 / 2) • (F + 1)) : A) := by
  rw [oddFredholmRowHalfPhase_eq_cfc]
  apply oddFredholmIntervalCFC_eq_cfc F hF _ _ (by fun_prop)
  intro r
  change NormedSpace.exp (Complex.I •
    ((Real.pi * oddFredholmIntervalParameter r) • (1 : ℂ))) = _
  rw [← Complex.exp_eq_exp_ℂ]
  congr 1
  rw [RCLike.real_smul_eq_coe_mul, smul_eq_mul, mul_one]
  change Complex.I * (((Real.pi * (((r : ℝ) + 1) / 2)) : ℝ) : ℂ) =
    Complex.I * (((Real.pi * 1 / 2) : ℝ) : ℂ) * (((r : ℝ) : ℂ) + 1)
  push_cast
  ring

/-- Actual circle CFC of the exponential is interval CFC after pullback
along the concrete scalar phase exp(iπ(r+1)). -/
theorem oddFredholmCircleCFC_exponential (F : selfAdjoint A) (hF : ‖(F : A)‖ ≤ 1)
    (f : C(Circle, ℂ)) :
    oddKTheoryCircleCFC (oddFredholmExponential F) f =
      oddFredholmIntervalCFC F hF (f.comp oddFredholmIntervalCircle) := by
  let ψ : C(Circle, ℂ) →⋆ₐ[ℂ] A :=
    (oddFredholmIntervalCFC F hF).comp
      (ContinuousMap.compStarAlgHom' ℂ ℂ oddFredholmIntervalCircle)
  have hcoordinate :
      ψ ((ContinuousMap.id ℂ).restrict (Metric.sphere (0 : ℂ) 1)) =
        (oddFredholmExponential F : A) := by
    change oddFredholmIntervalCFC F hF
      (((ContinuousMap.id ℂ).restrict (Metric.sphere (0 : ℂ) 1)).comp
        oddFredholmIntervalCircle) = (oddFredholmExponential F : A)
    rw [oddFredholmExponential_eq_cfc]
    apply oddFredholmIntervalCFC_eq_cfc F hF _ _ (by fun_prop)
    intro r
    change (Circle.exp (2 * Real.pi * oddFredholmIntervalParameter r) : ℂ) = _
    rw [Circle.coe_exp]
    congr 1
    change (((2 * Real.pi * (((r : ℝ) + 1) / 2)) : ℝ) : ℂ) * Complex.I =
      Complex.I * (Real.pi : ℂ) * (((r : ℝ) : ℂ) + 1)
    push_cast
    ring
  have hh : oddKTheoryCircleCFC (oddFredholmExponential F) = ψ :=
    ContinuousMap.UniqueHom.eq_of_continuous_of_map_id (Metric.sphere (0 : ℂ) 1)
      (oddKTheoryCircleCFC (oddFredholmExponential F)) ψ
      (continuous_oddKTheoryCircleCFC _) (map_continuous ψ)
      (by erw [oddKTheoryCircleCFC_coordinate, hcoordinate])
  exact DFunLike.congr_fun hh f

end BC4lean.KKTheory
