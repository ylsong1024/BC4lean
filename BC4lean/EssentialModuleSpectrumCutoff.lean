import BC4lean.ModuleCompactEssentialPositivity
import BC4lean.ModuleCompactCFCIntertwining
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Tactic.NoncommRing

/-! # Essential low-spectrum cutoffs for actual module operators

Let `Q` be an actual selfadjoint endomorphism and `X` an actual localizing
map. If `[Q,X]` is compact and `X (Q - δ) X*` has a positive lift modulo
compacts, continuous real functions vanishing at and above `δ' < δ`
give compact `X f(Q)` and `f(Q) X`. The proof uses order heredity of the
actual compact ideal, continuous functional calculus, and the rectangular
compact-square criterion. It makes no global spectral-gap or quotient
invertibility assumption.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

local instance standardEssentialModuleSpectrumCutoffLocalInstance01 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance standardEssentialModuleSpectrumCutoffLocalInstance02 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _

/-- The genuine continuous-function induction for rectangular CFC
intertwining specializes to compact CFC commutators. -/
theorem cfc_commutator_isModuleCompact
    (Q X : AdjointableMap B E E) (hQ : IsSelfAdjoint Q)
    (hcomm : IsModuleCompact (Q * X - X * Q)) (f : ℝ → ℝ) (hf : Continuous f) :
    IsModuleCompact (cfc f Q * X - X * cfc f Q) :=
  cfc_intertwining_isModuleCompact Q Q hQ hQ X hcomm f hf

/-- The scalar cutoff support condition makes the actual CFC weighted
low-spectrum defect positive, even without global positivity of `Q`. -/
theorem cfc_lowSpectrum_weight_nonneg
    (Q : AdjointableMap B E E) (δ' : ℝ) (f : ℝ → ℝ)
    (hsupport : ∀ s : ℝ, δ' ≤ s → f s = 0) :
    0 ≤ cfc (fun s => (δ' - s) * (f s * f s)) Q := by
  apply cfc_nonneg
  intro s _
  by_cases hs : s ≤ δ'
  · exact mul_nonneg (sub_nonneg.mpr hs) (mul_self_nonneg (f s))
  · rw [hsupport s (le_of_lt (lt_of_not_ge hs))]
    simp

/-- Exact CFC arithmetic identifies the sum of the compressed scalar
lower-bound defect and the positive cutoff weight with a negative square. -/
theorem cfc_lowSpectrum_weight_identity
    (Q : AdjointableMap B E E) (hQ : IsSelfAdjoint Q)
    (δ δ' : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    cfc f Q * (Q - algebraMap ℝ (AdjointableMap B E E) δ) * cfc f Q +
        cfc (fun s => (δ' - s) * (f s * f s)) Q =
      -((δ - δ') • (cfc f Q * cfc f Q)) := by
  have hw : cfc (fun s => f s * (s - δ) * f s) Q =
      cfc f Q * (Q - algebraMap ℝ (AdjointableMap B E E) δ) * cfc f Q := by
    rw [cfc_mul (fun s => f s * (s - δ)) f Q
      (hf.mul (continuous_id.sub continuous_const)).continuousOn hf.continuousOn,
      cfc_mul f (fun s => s - δ) Q hf.continuousOn
        (continuous_id.sub continuous_const).continuousOn,
      cfc_sub (fun s : ℝ => s) (fun _ => δ) Q continuous_id.continuousOn
        continuous_const.continuousOn,
      cfc_id' ℝ Q hQ, cfc_const δ Q hQ]
  calc
    _ = cfc (fun s => f s * (s - δ) * f s) Q +
        cfc (fun s => (δ' - s) * (f s * f s)) Q := by rw [hw]
    _ = cfc (fun s => f s * (s - δ) * f s + (δ' - s) * (f s * f s)) Q := by
      rw [cfc_add Q (fun s => f s * (s - δ) * f s)
        (fun s => (δ' - s) * (f s * f s))
        (((hf.mul (continuous_id.sub continuous_const)).mul hf).continuousOn)
        (((continuous_const.sub continuous_id).mul (hf.mul hf)).continuousOn)]
    _ = cfc (fun s => -((δ - δ') * (f s * f s))) Q := by
      congr 1
      funext s
      ring
    _ = -((δ - δ') • (cfc f Q * cfc f Q)) := by
      rw [cfc_neg (fun s => (δ - δ') * (f s * f s)) Q,
        cfc_const_mul (δ - δ') (fun s => f s * f s) Q (hf.mul hf).continuousOn,
        cfc_mul f f Q hf.continuousOn hf.continuousOn]

/-- A localized essential lower bound annihilates every actual continuous
low-spectrum cutoff modulo the compact module ideal, on both sides. -/
theorem lowSpectrum_cfc_localization_isModuleCompact
    (Q X : AdjointableMap B E E) (hQ : IsSelfAdjoint Q)
    (δ δ' : ℝ) (hgap : δ' < δ)
    (hcomm : IsModuleCompact (Q * X - X * Q))
    (hlower : IsPositiveModuloModuleCompact
      (X * (Q - algebraMap ℝ (AdjointableMap B E E) δ) * star X))
    (f : ℝ → ℝ) (hf : Continuous f)
    (hsupport : ∀ s : ℝ, δ' ≤ s → f s = 0) :
    IsModuleCompact (X * cfc f Q) ∧ IsModuleCompact (cfc f Q * X) := by
  let h := cfc f Q
  let R := Q - algebraMap ℝ (AdjointableMap B E E) δ
  let D := cfc (fun s => (δ' - s) * (f s * f s)) Q
  let W := X * h
  have hSA : IsSelfAdjoint h := IsSelfAdjoint.cfc
  have hch : IsModuleCompact (h * X - X * h) :=
    cfc_commutator_isModuleCompact Q X hQ hcomm f hf
  have hD : 0 ≤ D := cfc_lowSpectrum_weight_nonneg Q δ' f hsupport
  have hweighted : h * R * h + D = -((δ - δ') • (h * h)) :=
    cfc_lowSpectrum_weight_identity Q hQ δ δ' f hf
  have hleft : IsPositiveModuloModuleCompact ((h * X) * R * star (h * X)) := by
    simpa only [star_mul, hSA.star_eq, mul_assoc] using hlower.star_left_conjugate h
  have hright : IsPositiveModuloModuleCompact (W * R * star W) :=
    hleft.of_sub_compact
      (moduleCompact_star_right_conjugate_sub (h * X) (X * h) R
        (by simpa only [neg_sub] using hch.neg))
  have hsum : IsPositiveModuloModuleCompact (W * R * star W + X * D * star X) :=
    hright.add (isPositiveModuloModuleCompact_of_nonneg (star_right_conjugate_nonneg hD X))
  have hexpand : W * R * star W + X * D * star X =
      -((δ - δ') • (W * star W)) := by
    calc
      _ = X * (h * R * h + D) * star X := by
        dsimp only [W]
        rw [star_mul, hSA.star_eq]
        noncomm_ring
      _ = X * (-((δ - δ') • (h * h))) * star X := by rw [hweighted]
      _ = -((δ - δ') • (W * star W)) := by
        dsimp only [W]
        simp only [star_mul, hSA.star_eq, mul_neg, neg_mul,
          mul_smul_comm, smul_mul_assoc, mul_assoc]
  rw [hexpand] at hsum
  have hc : 0 < δ - δ' := sub_pos.mpr hgap
  have hscaled : IsModuleCompact ((δ - δ') • (W * star W)) :=
    isModuleCompact_of_nonneg_of_neg_positiveModuloModuleCompact
      (smul_nonneg hc.le (mul_star_self_nonneg W)) hsum
  have hsquare : IsModuleCompact (W * star W) := by
    have h := hscaled.real_smul (δ - δ')⁻¹
    simpa only [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] using h
  have hWadjoint : IsModuleCompact W.adjoint := by
    apply IsModuleCompact.of_adjoint_comp_self
    rw [AdjointableMap.adjoint_adjoint]
    exact hsquare
  have hW : IsModuleCompact W := by
    simpa only [AdjointableMap.adjoint_adjoint] using hWadjoint.adjoint
  refine ⟨hW, ?_⟩
  have heq : h * X = (h * X - X * h) + W := by
    dsimp only [W]
    abel
  rw [heq]
  exact hch.add hW

/-- The cutoff is compact after right multiplication by a single localizer. -/
theorem cfc_mul_isModuleCompact_of_essential_lowerBound
    (Q X : AdjointableMap B E E) (hQ : IsSelfAdjoint Q)
    (δ δ' : ℝ) (hgap : δ' < δ)
    (hcomm : IsModuleCompact (Q * X - X * Q))
    (hlower : IsPositiveModuloModuleCompact
      (X * (Q - algebraMap ℝ (AdjointableMap B E E) δ) * star X))
    (f : ℝ → ℝ) (hf : Continuous f)
    (hsupport : ∀ s : ℝ, δ' ≤ s → f s = 0) :
    IsModuleCompact (cfc f Q * X) :=
  (lowSpectrum_cfc_localization_isModuleCompact Q X hQ δ δ' hgap hcomm hlower
    f hf hsupport).2

/-- The cutoff is also compact after left multiplication by the localizer. -/
theorem mul_cfc_isModuleCompact_of_essential_lowerBound
    (Q X : AdjointableMap B E E) (hQ : IsSelfAdjoint Q)
    (δ δ' : ℝ) (hgap : δ' < δ)
    (hcomm : IsModuleCompact (Q * X - X * Q))
    (hlower : IsPositiveModuloModuleCompact
      (X * (Q - algebraMap ℝ (AdjointableMap B E E) δ) * star X))
    (f : ℝ → ℝ) (hf : Continuous f)
    (hsupport : ∀ s : ℝ, δ' ≤ s → f s = 0) :
    IsModuleCompact (X * cfc f Q) :=
  (lowSpectrum_cfc_localization_isModuleCompact Q X hQ δ δ' hgap hcomm hlower
    f hf hsupport).1

end BC4lean.KKTheory
