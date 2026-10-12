import BC4lean.HilbertModuleJuliaSqrt
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-! # Contractive normalization of an actual module operator

For the positive adjoint square a=T*T, the continuous weight
f(s)=1/√max(1,s) gives Tk with norm at most one. The bound is proved
by the actual rectangular C*-identity and the continuous functional calculus.
No compact defect or Fredholm hypothesis is required for this construction.
-/

noncomputable section
namespace BC4lean.KKTheory

def fredholmNormWeight (s : ℝ) : ℝ := (Real.sqrt (max 1 s))⁻¹
def fredholmNormRemainder (s : ℝ) : ℝ :=
  (Real.sqrt (max 1 s) * (Real.sqrt (max 1 s) + 1))⁻¹

private theorem fredholmNormRoot_pos (s : ℝ) : 0 < Real.sqrt (max 1 s) :=
  Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

theorem continuous_fredholmNormWeight : Continuous fredholmNormWeight :=
  (Real.continuous_sqrt.comp (continuous_const.max continuous_id)).inv₀
    (fun s => ne_of_gt (fredholmNormRoot_pos s))

theorem continuous_fredholmNormRemainder : Continuous fredholmNormRemainder := by
  have hc : Continuous (fun s : ℝ => Real.sqrt (max 1 s)) :=
    Real.continuous_sqrt.comp (continuous_const.max continuous_id)
  exact (hc.mul (hc.add continuous_const)).inv₀ (fun s => by
    change Real.sqrt (max 1 s) * (Real.sqrt (max 1 s) + 1) ≠ 0
    exact ne_of_gt (mul_pos (fredholmNormRoot_pos s) (by linarith [fredholmNormRoot_pos s])))

/-- The continuous factorization has no division by s−1 at its zero. -/
theorem fredholmNormWeight_sub_one (s : ℝ) :
    fredholmNormWeight s - 1 = -(max (s - 1) 0) * fredholmNormRemainder s := by
  have ht : 0 < Real.sqrt (max 1 s) := fredholmNormRoot_pos s
  have ht1 : 0 < Real.sqrt (max 1 s) + 1 := by linarith
  have hsq : Real.sqrt (max 1 s) ^ 2 = max 1 s :=
    Real.sq_sqrt (le_trans zero_le_one (le_max_left _ _))
  have hp : max (s - 1) 0 = max 1 s - 1 := by
    rcases le_total s 1 with hs | hs
    · rw [max_eq_right (sub_nonpos.mpr hs), max_eq_left hs]
      ring
    · rw [max_eq_left (sub_nonneg.mpr hs), max_eq_right hs]
  unfold fredholmNormWeight fredholmNormRemainder
  rw [hp]
  field_simp [ne_of_gt ht, ne_of_gt ht1]
  nlinarith

theorem fredholmNormWeight_square_eq (s : ℝ) :
    fredholmNormWeight s * s * fredholmNormWeight s = s / max 1 s := by
  have ht : Real.sqrt (max 1 s) ≠ 0 := ne_of_gt (fredholmNormRoot_pos s)
  have hm : max 1 s ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  have hsq : Real.sqrt (max 1 s) ^ 2 = max 1 s :=
    Real.sq_sqrt (le_trans zero_le_one (le_max_left _ _))
  unfold fredholmNormWeight
  field_simp [ht, hm]
  rw [hsq]
  ring

theorem fredholmNormWeight_square_bounds {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ fredholmNormWeight s * s * fredholmNormWeight s ∧
      fredholmNormWeight s * s * fredholmNormWeight s ≤ 1 := by
  rw [fredholmNormWeight_square_eq]
  have hm : 0 < max 1 s := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  exact ⟨div_nonneg hs hm.le, (div_le_one hm).mpr (le_max_right _ _)⟩

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

local instance standardGlobalModuleContractiveNormalizationLocalInstance01 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance standardGlobalModuleContractiveNormalizationLocalInstance02 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _
local instance standardGlobalModuleContractiveNormalizationLocalInstance03 : PartialOrder (AdjointableMap B F F) := CStarAlgebra.spectralOrder _
local instance standardGlobalModuleContractiveNormalizationLocalInstance04 : StarOrderedRing (AdjointableMap B F F) := CStarAlgebra.spectralOrderedRing _

def globalFredholmNormalizer (T : AdjointableMap B E F) : AdjointableMap B E E :=
  cfc fredholmNormWeight (T.adjoint.comp T)

def globalFredholmNormalization (T : AdjointableMap B E F) : AdjointableMap B E F :=
  T.comp (globalFredholmNormalizer T)

omit [CompleteSpace F] in
@[simp] theorem globalFredholmNormalizer_adjoint (T : AdjointableMap B E F) :
    (globalFredholmNormalizer T).adjoint = globalFredholmNormalizer T :=
  (cfc_predicate fredholmNormWeight (T.adjoint.comp T)).star_eq

theorem globalFredholmNormalization_adjoint_square (T : AdjointableMap B E F) :
    (globalFredholmNormalization T).adjoint.comp (globalFredholmNormalization T) =
      cfc (fun s => fredholmNormWeight s * s * fredholmNormWeight s) (T.adjoint.comp T) := by
  have ha := (rectangular_adjoint_squares_nonneg T).2.isSelfAdjoint
  have hc : cfc (fun s => fredholmNormWeight s * s * fredholmNormWeight s) (T.adjoint.comp T) =
      globalFredholmNormalizer T * (T.adjoint.comp T) * globalFredholmNormalizer T := by
    rw [cfc_mul (fun s => fredholmNormWeight s * s) fredholmNormWeight _
      (continuous_fredholmNormWeight.mul continuous_id).continuousOn continuous_fredholmNormWeight.continuousOn,
      cfc_mul fredholmNormWeight (fun s : ℝ => s) _
        continuous_fredholmNormWeight.continuousOn continuous_id.continuousOn, cfc_id' ℝ _ ha]
    rfl
  rw [hc]
  ext x
  simp only [globalFredholmNormalization, AdjointableMap.adjoint_comp,
    globalFredholmNormalizer_adjoint, AdjointableMap.comp_apply, AdjointableMap.mul_apply]

/-- This Fredholm normalization is actually contractive in the module operator norm. -/
theorem norm_globalFredholmNormalization_le (T : AdjointableMap B E F) :
    ‖globalFredholmNormalization T‖ ≤ 1 := by
  have hc : ‖(globalFredholmNormalization T).adjoint.comp (globalFredholmNormalization T)‖ ≤ 1 := by
    rw [globalFredholmNormalization_adjoint_square]
    apply norm_cfc_le zero_le_one
    intro s hs
    have hb := fredholmNormWeight_square_bounds
      (spectrum_nonneg_of_nonneg (rectangular_adjoint_squares_nonneg T).2 hs)
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2
  change ‖((globalFredholmNormalization T).adjoint.comp (globalFredholmNormalization T)).toCLM‖ ≤ 1 at hc
  rw [AdjointableMap.norm_toCLM_adjoint_comp_self] at hc
  change ‖globalFredholmNormalization T‖ ^ 2 ≤ 1 at hc
  nlinarith [norm_nonneg (globalFredholmNormalization T)]

end BC4lean.KKTheory
