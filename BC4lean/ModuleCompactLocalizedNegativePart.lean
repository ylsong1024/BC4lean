import BC4lean.EssentialModuleSpectrumCutoff
import Mathlib.Analysis.SpecificLimits.Basic

/-! # A localized essentially positive operator has compact negative part

The compression X Q X* is assumed positive only modulo the actual compact
ideal, and [Q,X] is compact. Negative cutoffs separated from zero are compact
by the genuine hereditary-order cutoff theorem. Their uniform CFC norm limit
is the negative part of Q. This proves both localizations compact, without
a positive Calkin lift, global positivity or a spectral gap at zero.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped Topology

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

local instance standardModuleCompactLocalizedNegativePartLocalInstance01 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance standardModuleCompactLocalizedNegativePartLocalInstance02 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _

def localizedNegativeCutoff (ε s : ℝ) : ℝ := max (-s - ε) 0

theorem localizedNegativeCutoff_continuous (ε : ℝ) : Continuous (localizedNegativeCutoff ε) :=
  (continuous_id.neg.sub continuous_const).max continuous_const

theorem localizedNegativeCutoff_support (ε s : ℝ) (hs : -ε ≤ s) :
    localizedNegativeCutoff ε s = 0 :=
  max_eq_right (by linarith)

theorem localizedNegativeCutoff_error (ε s : ℝ) (hε : 0 ≤ ε) :
    ‖localizedNegativeCutoff ε s - max (-s) 0‖ ≤ ε := by
  rw [Real.norm_eq_abs]
  by_cases hs : 0 ≤ s
  · rw [localizedNegativeCutoff, max_eq_right (by linarith), max_eq_right (by linarith), sub_self, abs_zero]
    exact hε
  · have hn : 0 ≤ -s := by linarith
    rw [max_eq_left hn]
    by_cases hsmall : -s - ε ≤ 0
    · rw [localizedNegativeCutoff, max_eq_right hsmall, zero_sub,
        neg_neg, abs_of_nonpos (le_of_not_ge hs)]
      linarith
    · rw [localizedNegativeCutoff, max_eq_left (le_of_lt (lt_of_not_ge hsmall))]
      have heq : -s - ε - -s = -ε := by ring
      rw [heq, abs_neg, abs_of_nonneg hε]

theorem localizedNegativeCutoff_cfc_tendsto
    (Q : AdjointableMap B E E) :
    Tendsto (fun n : ℕ => cfc (localizedNegativeCutoff ((n : ℝ) + 1)⁻¹) Q)
      atTop (𝓝 (cfc (fun s : ℝ => max (-s) 0) Q)) := by
  have hn : Continuous (fun s : ℝ => max (-s) 0) := continuous_id.neg.max continuous_const
  have hbound (n : ℕ) :
      ‖cfc (localizedNegativeCutoff ((n : ℝ) + 1)⁻¹) Q - cfc (fun s : ℝ => max (-s) 0) Q‖ ≤
        ((n : ℝ) + 1)⁻¹ := by
    rw [← cfc_sub (localizedNegativeCutoff ((n : ℝ) + 1)⁻¹)
      (fun s : ℝ => max (-s) 0) Q
      (localizedNegativeCutoff_continuous _).continuousOn hn.continuousOn]
    apply norm_cfc_le (by positivity)
    intro s _
    exact localizedNegativeCutoff_error _ s (by positivity)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) hbound
    (by simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))

/-- Both actual compact localizations of the real-CFC negative part. -/
theorem cfc_negativePart_localization_isModuleCompact
    (Q X : AdjointableMap B E E) (hQ : IsSelfAdjoint Q)
    (hcomm : IsModuleCompact (Q * X - X * Q))
    (hpositive : IsPositiveModuloModuleCompact (X * Q * star X)) :
    IsModuleCompact (X * cfc (fun s : ℝ => max (-s) 0) Q) ∧
      IsModuleCompact (cfc (fun s : ℝ => max (-s) 0) Q * X) := by
  have hcompact (n : ℕ) :
      IsModuleCompact (X * cfc (localizedNegativeCutoff ((n : ℝ) + 1)⁻¹) Q) ∧
        IsModuleCompact (cfc (localizedNegativeCutoff ((n : ℝ) + 1)⁻¹) Q * X) := by
    apply lowSpectrum_cfc_localization_isModuleCompact Q X hQ 0
      (-((n : ℝ) + 1)⁻¹) (neg_lt_zero.mpr (inv_pos.mpr (by positivity))) hcomm
    · simpa only [map_zero, sub_zero] using hpositive
    · exact localizedNegativeCutoff_continuous _
    · exact localizedNegativeCutoff_support _
  have ht := localizedNegativeCutoff_cfc_tendsto Q
  constructor
  · apply moduleCompact_isClosed.mem_of_tendsto (tendsto_const_nhds.mul ht)
    exact Eventually.of_forall fun n => (hcompact n).1
  · apply moduleCompact_isClosed.mem_of_tendsto (ht.mul tendsto_const_nhds)
    exact Eventually.of_forall fun n => (hcompact n).2

theorem negativePart_localization_isModuleCompact
    (Q X : AdjointableMap B E E) (hQ : IsSelfAdjoint Q)
    (hcomm : IsModuleCompact (Q * X - X * Q))
    (hpositive : IsPositiveModuloModuleCompact (X * Q * star X)) :
    IsModuleCompact (X * Q⁻) ∧ IsModuleCompact (Q⁻ * X) := by
  have heq : cfc (fun s : ℝ => max (-s) 0) Q = Q⁻ := by
    rw [CFC.negPart_def]
    simp only [_root_.negPart_def]
    exact (cfcₙ_eq_cfc (a := Q) (f := fun s : ℝ => max (-s) 0)
      (hf := (continuous_id.neg.max continuous_const).continuousOn) (hf0 := by simp)).symm
  simpa only [heq] using cfc_negativePart_localization_isModuleCompact Q X hQ hcomm hpositive

/-- This is the actual residual used by Skandalis's common triple-operator partition. -/
theorem sub_posPart_localization_isModuleCompact
    (Q X : AdjointableMap B E E) (hQ : IsSelfAdjoint Q)
    (hcomm : IsModuleCompact (Q * X - X * Q))
    (hpositive : IsPositiveModuloModuleCompact (X * Q * star X)) :
    IsModuleCompact (X * (Q - Q⁺)) ∧ IsModuleCompact ((Q - Q⁺) * X) := by
  have hneg := negativePart_localization_isModuleCompact Q X hQ hcomm hpositive
  have heq : Q - Q⁺ = -Q⁻ := by
    have h := CFC.posPart_sub_negPart Q hQ
    calc
      Q - Q⁺ = (Q⁺ - Q⁻) - Q⁺ := congrArg (fun R => R - Q⁺) h.symm
      _ = -Q⁻ := by abel
  rw [heq, mul_neg, neg_mul]
  exact ⟨hneg.1.neg, hneg.2.neg⟩

end BC4lean.KKTheory
