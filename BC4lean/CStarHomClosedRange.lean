import BC4lean.CStarHomCutoffScalar
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.NoncommRing

/-! # Closed range and bounded lifting for actual complex C⋆-homomorphisms

The range of an actual complex nonunital C⋆-homomorphism is closed. This is
proved from a concrete continuous-functional-calculus clipping operation.
Clipping preserves the image while bounding the source norm by any positive
bound for the image norm. Thus the actual Banach quotient by the closed
linear kernel embeds isometrically in the target, with image exactly the
homomorphism range. No C⋆-algebra structure or order on an unconstructed
algebraic quotient is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped ContinuousFunctionalCalculus CStarAlgebra

variable {A D : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra D]

/-- The usual bounded complex-linear map underlying a C⋆-homomorphism. -/
def nonUnitalCStarHomCLM (φ : A →⋆ₙₐ[ℂ] D) : A →L[ℂ] D :=
  ({ toFun := φ
     map_add' := φ.map_add
     map_smul' := φ.map_smul } : A →ₗ[ℂ] D).mkContinuous 1 (fun a => by
    change ‖φ a‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le φ a)

@[simp] theorem nonUnitalCStarHomCLM_apply (φ : A →⋆ₙₐ[ℂ] D) (a : A) :
    nonUnitalCStarHomCLM φ a = φ a := rfl

/-- The exact star-square identity for nonunital CFC clipping. Every scalar
function entering the calculation vanishes at zero. -/
theorem cstarHomClipping_star_mul_self (a : A) (h : ℝ → ℝ)
    (hc : Continuous h) (h0 : h 0 = 0) :
    star (a - a * cfcₙ h (star a * a)) *
        (a - a * cfcₙ h (star a * a)) =
      cfcₙ (fun t : ℝ => t * (1 - h t) ^ 2) (star a * a) := by
  let p : A := star a * a
  let b : A := cfcₙ h p
  have hp : IsSelfAdjoint p := .star_mul_self a
  have hb : star b = b := (IsSelfAdjoint.cfcₙ (f := h) (a := p)).star_eq
  have hi : cfcₙ (fun t : ℝ => t) p = p := cfcₙ_id' ℝ p hp
  have hexpand : cfcₙ (fun t : ℝ => t * (1 - h t) ^ 2) p =
      p - p * b - b * p + b * p * b := by
    have heq : (fun t : ℝ => t * (1 - h t) ^ 2) =
        (fun t : ℝ => t - t * h t - h t * t + (h t * t) * h t) := by
      funext t
      ring
    rw [heq]
    rw [cfcₙ_add (fun t => t - t * h t - h t * t)
      (fun t => (h t * t) * h t) p (by fun_prop) (by simp [h0])
        (by fun_prop) (by simp [h0])]
    rw [cfcₙ_sub (fun t => t - t * h t) (fun t => h t * t) p
      (by fun_prop) (by simp [h0]) (by fun_prop) (by simp [h0])]
    rw [cfcₙ_sub (fun t => t) (fun t => t * h t) p
      continuousOn_id rfl (by fun_prop) (by simp [h0])]
    rw [cfcₙ_mul (fun t => t) h p continuousOn_id rfl hc.continuousOn h0]
    rw [cfcₙ_mul (fun t => h t * t) h p (by fun_prop) (by simp [h0])
      hc.continuousOn h0]
    rw [cfcₙ_mul h (fun t => t) p hc.continuousOn h0 continuousOn_id rfl]
    rw [hi]
  rw [hexpand]
  change star (a - a * b) * (a - a * b) = _
  rw [star_sub, star_mul, hb]
  dsimp only [p]
  noncomm_ring

/-- An actual element obtained by clipping the singular values at `r`. -/
def cstarHomTrim (r : ℝ) (a : A) : A :=
  a - a * cfcₙ (cstarHomCutoff r) (star a * a)

/-- CFC clipping has the stated source norm bound, independently of the
homomorphism subsequently used to identify its image. -/
theorem norm_cstarHomTrim_le (r : ℝ) (hr : 0 < r) (a : A) :
    ‖cstarHomTrim r a‖ ≤ r := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hsq : ‖cstarHomTrim r a‖ ^ 2 ≤ r ^ 2 := by
    rw [pow_two, ← CStarRing.norm_star_mul_self]
    change ‖star (a - a * cfcₙ (cstarHomCutoff r) (star a * a)) *
      (a - a * cfcₙ (cstarHomCutoff r) (star a * a))‖ ≤ _
    rw [cstarHomClipping_star_mul_self a (cstarHomCutoff r)
      (continuous_cstarHomCutoff hr) (cstarHomCutoff_zero hr)]
    apply norm_cfcₙ_le
    intro t ht
    have ht0 : 0 ≤ t :=
      quasispectrum_nonneg_of_nonneg (star a * a) (star_mul_self_nonneg a) t ht
    rw [Real.norm_eq_abs, abs_of_nonneg
      (cstarHomCutoff_clipped_square_nonneg hr ht0)]
    exact cstarHomCutoff_clipped_square_le hr ht0
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hr.le (by decide : (2 : ℕ) ≠ 0)).mp hsq

/-- Clipping below no point of the image spectrum preserves the actual
image under a C⋆-homomorphism. -/
theorem cstarHomTrim_map (φ : A →⋆ₙₐ[ℂ] D) (a : A)
    (r : ℝ) (hr : 0 < r) (hφa : ‖φ a‖ ≤ r) :
    φ (cstarHomTrim r a) = φ a := by
  have hp : IsSelfAdjoint (star a * a) := .star_mul_self a
  have hpD : IsSelfAdjoint (star (φ a) * φ a) := .star_mul_self (φ a)
  have hfc : φ (cfcₙ (cstarHomCutoff r) (star a * a)) = 0 := by
    rw [φ.map_cfcₙ (cstarHomCutoff r) (star a * a)
      (continuous_cstarHomCutoff hr).continuousOn (cstarHomCutoff_zero hr)
      (nonUnitalCStarHomCLM φ).continuous hp (hp.map φ)]
    simp only [map_mul, map_star]
    trans cfcₙ (0 : ℝ → ℝ) (star (φ a) * φ a)
    · apply cfcₙ_congr
      intro t ht
      have htbound : ‖t‖ ≤ ‖star (φ a) * φ a‖ := by
        simpa only [cfcₙ_id' ℝ _ hpD] using
          norm_apply_le_norm_cfcₙ (fun s : ℝ => s) (star (φ a) * φ a) ht
      have htle : t ≤ r ^ 2 := by
        calc
          t ≤ ‖t‖ := le_abs_self t
          _ ≤ ‖star (φ a) * φ a‖ := htbound
          _ = ‖φ a‖ ^ 2 := by rw [CStarRing.norm_star_mul_self, pow_two]
          _ ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hφa 2
      exact cstarHomCutoff_eq_zero_of_le hr htle
    · exact cfcₙ_zero ℝ _
  simp only [cstarHomTrim, map_sub, map_mul, hfc, mul_zero, sub_zero]

/-- An actual lift of the same image, with norm at most any positive
upper bound for the image norm. -/
theorem nonUnitalCStarHom_exists_norm_le_lift (φ : A →⋆ₙₐ[ℂ] D)
    (a : A) (r : ℝ) (hr : 0 < r) (hφa : ‖φ a‖ ≤ r) :
    ∃ b : A, φ b = φ a ∧ ‖b‖ ≤ r :=
  ⟨cstarHomTrim r a, cstarHomTrim_map φ a r hr hφa,
    norm_cstarHomTrim_le r hr a⟩

/-- Every element in the actual range has a lift attaining its target norm.
The zero-image case uses the actual zero vector. -/
theorem nonUnitalCStarHom_exists_norm_eq_lift (φ : A →⋆ₙₐ[ℂ] D) (a : A) :
    ∃ b : A, φ b = φ a ∧ ‖b‖ = ‖φ a‖ := by
  by_cases hz : ‖φ a‖ = 0
  · refine ⟨0, ?_, ?_⟩
    · rw [map_zero, norm_eq_zero.mp hz]
    · simp only [norm_zero, hz]
  · have hr : 0 < ‖φ a‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    obtain ⟨b, hb, hnorm⟩ :=
      nonUnitalCStarHom_exists_norm_le_lift φ a ‖φ a‖ hr le_rfl
    refine ⟨b, hb, le_antisymm hnorm ?_⟩
    rw [← hb]
    exact NonUnitalStarAlgHom.norm_apply_le φ b

/-- Surjective actual C⋆-homomorphisms have norm-preserving lifts, with no
additional bounded-lifting hypothesis. -/
theorem nonUnitalCStarHom_exists_norm_eq_lift_of_surjective
    (φ : A →⋆ₙₐ[ℂ] D) (hφ : Function.Surjective φ) (d : D) :
    ∃ a : A, φ a = d ∧ ‖a‖ = ‖d‖ := by
  obtain ⟨a, rfl⟩ := hφ d
  exact nonUnitalCStarHom_exists_norm_eq_lift φ a

/-- The actual continuous linear kernel is closed. -/
instance nonUnitalCStarHom_kernel_closed (φ : A →⋆ₙₐ[ℂ] D) :
    IsClosed ((nonUnitalCStarHomCLM φ).ker : Set A) :=
  (nonUnitalCStarHomCLM φ).isClosed_ker

/-- The quotient norm is exactly the target norm, by contractivity in one
direction and actual CFC bounded lifts in the other. -/
theorem nonUnitalCStarHom_quotient_norm_mk (φ : A →⋆ₙₐ[ℂ] D) (a : A) :
    ‖(Submodule.Quotient.mk a : A ⧸ (nonUnitalCStarHomCLM φ).ker)‖ = ‖φ a‖ := by
  let N := (nonUnitalCStarHomCLM φ).ker
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨b, hb, hnorm⟩ := nonUnitalCStarHom_exists_norm_le_lift φ a
      (‖φ a‖ + ε) (by positivity) (by linarith)
    have hclass : (Submodule.Quotient.mk b : A ⧸ N) = Submodule.Quotient.mk a := by
      apply (Submodule.Quotient.eq N).mpr
      change φ (b - a) = 0
      rw [map_sub, hb, sub_self]
    calc
      _ = ‖(Submodule.Quotient.mk b : A ⧸ N)‖ := congrArg norm hclass.symm
      _ ≤ ‖b‖ := Submodule.Quotient.norm_mk_le N b
      _ ≤ ‖φ a‖ + ε := hnorm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨b, hb, hnorm⟩ := Submodule.Quotient.norm_mk_lt
      (Submodule.Quotient.mk a : A ⧸ N) hε
    have himage : φ b = φ a := by
      have hz : φ (b - a) = 0 := (Submodule.Quotient.eq N).mp hb
      simpa only [map_sub, sub_eq_zero] using hz
    calc
      _ = ‖φ b‖ := congrArg norm himage.symm
      _ ≤ ‖b‖ := NonUnitalStarAlgHom.norm_apply_le φ b
      _ ≤ ‖(Submodule.Quotient.mk a : A ⧸ N)‖ + ε := hnorm.le

/-- The genuine complete Banach quotient embeds isometrically in the target.
Its range will be identified with the original homomorphism range below. -/
def nonUnitalCStarHomQuotientIsometry (φ : A →⋆ₙₐ[ℂ] D) :
    (A ⧸ (nonUnitalCStarHomCLM φ).ker) →ₗᵢ[ℂ] D where
  __ := ((nonUnitalCStarHomCLM φ).ker).liftQ
    (nonUnitalCStarHomCLM φ).toLinearMap le_rfl
  norm_map' x := by
    obtain ⟨a, rfl⟩ := ((nonUnitalCStarHomCLM φ).ker).mkQ_surjective x
    exact (nonUnitalCStarHom_quotient_norm_mk φ a).symm

@[simp] theorem nonUnitalCStarHomQuotientIsometry_mk (φ : A →⋆ₙₐ[ℂ] D) (a : A) :
    nonUnitalCStarHomQuotientIsometry φ (Submodule.Quotient.mk a) = φ a := rfl

theorem nonUnitalCStarHomQuotientIsometry_range (φ : A →⋆ₙₐ[ℂ] D) :
    Set.range (nonUnitalCStarHomQuotientIsometry φ) = Set.range φ := by
  ext d
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := ((nonUnitalCStarHomCLM φ).ker).mkQ_surjective x
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨Submodule.Quotient.mk a, rfl⟩

/-- Every actual complex C⋆-homomorphism has closed range. The proof uses
the complete, normed, closed-kernel Banach quotient constructed above. -/
theorem nonUnitalCStarHom_isClosed_range (φ : A →⋆ₙₐ[ℂ] D) :
    IsClosed (Set.range φ) := by
  rw [← nonUnitalCStarHomQuotientIsometry_range φ]
  exact (nonUnitalCStarHomQuotientIsometry φ).isometry.isClosedEmbedding.isClosed_range

end BC4lean.KKTheory
