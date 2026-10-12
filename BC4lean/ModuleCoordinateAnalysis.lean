import BC4lean.CountableModuleSequence
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! # Actual coisometries from coefficient-convergent operator coordinates

This helper constructs the analysis column and its bounded adjoint row for
an actual operator family whose coefficient partial sums converge to the
module inner product. That explicit convergence hypothesis is discharged by
the spectral band construction and by tensoring a proved Parseval frame.
No formal sequence space or adjoint is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped InnerProductSpace Topology

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

/-- An actual operator family with the full coefficient-norm Parseval identity. -/
structure HasParsevalOperatorCoordinates (X : ℕ → AdjointableMap B E F) : Prop where
  partial_inner_tendsto (u v : E) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, ⟪X n u, X n v⟫_(Bᵐᵒᵖ)) atTop (𝓝 ⟪u, v⟫_(Bᵐᵒᵖ))

namespace HasParsevalOperatorCoordinates
variable {X : ℕ → AdjointableMap B E F} (hX : HasParsevalOperatorCoordinates X)

def analysisSum (_hX : HasParsevalOperatorCoordinates X) (u : E) : CountableHilbertModuleSum B F :=
  countableModuleSequenceSum (fun n => X n u)

omit [CompleteSpace E] in
@[simp] theorem evaluation_analysisSum (n : ℕ) (u : E) :
    countableModuleEvaluation (B := B) n (hX.analysisSum u) = X n u :=
  countableModuleEvaluation_sequenceSum _ (hX.partial_inner_tendsto u u) n

omit [CompleteSpace E] [CompleteSpace F] in
theorem inner_analysisSum (u v : E) :
    ⟪hX.analysisSum u, hX.analysisSum v⟫_(Bᵐᵒᵖ) = ⟪u, v⟫_(Bᵐᵒᵖ) :=
  countableModuleSequenceSum_inner _ _ (hX.partial_inner_tendsto u u)
    (hX.partial_inner_tendsto v v) (hX.partial_inner_tendsto u v)

omit [CompleteSpace E] [CompleteSpace F] in
theorem norm_analysisSum (u : E) : ‖hX.analysisSum u‖ = ‖u‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ), hX.inner_analysisSum,
    ← CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ)]

def analysisIsometry : E →ₗᵢ[ℂ] CountableHilbertModuleSum B F where
  toLinearMap :=
    { toFun := hX.analysisSum
      map_add' := fun u v => by
        apply countableModule_ext_eval
        intro n
        simp only [map_add, hX.evaluation_analysisSum]
      map_smul' := fun c u => by
        apply countableModule_ext_eval
        intro n
        simp only [map_smul, hX.evaluation_analysisSum, RingHom.id_apply] }
  norm_map' := hX.norm_analysisSum

def finiteRow (_hX : HasParsevalOperatorCoordinates X) : CountableModuleVectors F →ₗ[ℂ] E :=
  Finsupp.lsum ℂ (fun n => (X n).adjoint.toCLM.toLinearMap)

omit [CompleteSpace E] in
theorem finiteRow_inner (v : CountableModuleVectors F) (u : E) :
    ⟪hX.finiteRow v, u⟫_(Bᵐᵒᵖ) = ⟪countableModuleMk (B := B) v, hX.analysisSum u⟫_(Bᵐᵒᵖ) := by
  rw [finiteRow, Finsupp.lsum_apply, Finsupp.sum, CStarModule.inner_sum_left,
    countableModuleMk_inner_right]
  exact Finset.sum_congr rfl (fun n _ => by
    rw [hX.evaluation_analysisSum]
    exact (X n).adjoint.adjoint_identity _ _)

omit [CompleteSpace E] in
theorem finiteRow_norm_le (v : CountableModuleVectors F) :
    ‖hX.finiteRow v‖ ≤ ‖countableModuleMk (B := B) v‖ := by
  let u := hX.finiteRow v
  have hsq : ‖u‖ ^ 2 ≤ ‖countableModuleMk (B := B) v‖ * ‖u‖ := by
    rw [CStarModule.norm_sq_eq (Bᵐᵒᵖ), hX.finiteRow_inner]
    simpa only [hX.norm_analysisSum] using CStarModule.norm_inner_le (CountableHilbertModuleSum B F)
      (x := countableModuleMk (B := B) v) (y := hX.analysisSum u)
  by_cases hu : ‖u‖ = 0
  · change ‖u‖ ≤ _
    rw [hu]
    exact norm_nonneg (countableModuleMk (B := B) v)
  · exact le_of_mul_le_mul_right (by simpa only [pow_two] using hsq)
      (lt_of_le_of_ne (norm_nonneg u) (Ne.symm hu))

def rowQuotientLinear : CountableHilbertModulePreSum B F →ₗ[ℂ] E :=
  (PositiveModuleForm.nullRadical (B := B) (E := CountableModuleVectors F)).liftQ hX.finiteRow
    (fun v hv => by
      rw [countableModuleFinite_nullRadical_eq_bot, Submodule.mem_bot] at hv
      simp [hv])

def rowQuotientCLM : CountableHilbertModulePreSum B F →L[ℂ] E :=
  hX.rowQuotientLinear.mkContinuous 1 (fun q => by
    obtain ⟨v, rfl⟩ := positiveModuleQuotientMk_surjective q
    change ‖hX.finiteRow v‖ ≤ 1 * ‖positiveModuleQuotientMk (B := B) v‖
    have h := hX.finiteRow_norm_le v
    simpa only [countableModuleMk_apply, UniformSpace.Completion.norm_coe, one_mul] using h)

def rowCLM : CountableHilbertModuleSum B F →L[ℂ] E := hX.rowQuotientCLM.fromCompletion

omit [CompleteSpace F] in
@[simp] theorem rowCLM_mk [CompleteSpace F] (v : CountableModuleVectors F) :
    hX.rowCLM (countableModuleMk (B := B) v) = hX.finiteRow v := by
  rw [rowCLM, countableModuleMk_apply, ContinuousLinearMap.fromCompletion_apply_coe]
  rfl

/-- The actual bounded adjointable synthesis, with its actual completed column. -/
def synthesis : AdjointableMap B (CountableHilbertModuleSum B F) E where
  toCLM := hX.rowCLM
  adjointCLM := hX.analysisIsometry.toContinuousLinearMap
  adjoint_identity v u := by
    change ⟪hX.rowCLM v, u⟫_(Bᵐᵒᵖ) = ⟪v, hX.analysisSum u⟫_(Bᵐᵒᵖ)
    refine (countableModuleMk_denseRange (B := B) (E := F)).induction_on v ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro w
      rw [hX.rowCLM_mk]
      exact hX.finiteRow_inner w u

@[simp] theorem synthesis_adjoint_apply (u : E) : hX.synthesis.adjoint u = hX.analysisSum u := rfl

@[simp] theorem synthesis_inclusion (n : ℕ) (u : F) :
    hX.synthesis (countableModuleInclusion (B := B) n u) = (X n).adjoint u := by
  rw [countableModuleInclusion_apply]
  change hX.rowCLM (countableModuleMk (B := B) (Finsupp.single n u)) = _
  rw [hX.rowCLM_mk]
  simp only [finiteRow, Finsupp.lsum_apply, Finsupp.sum_single_index, map_zero]
  rfl

@[simp] theorem evaluation_synthesis_adjoint (n : ℕ) (u : E) :
    countableModuleEvaluation (B := B) n (hX.synthesis.adjoint u) = X n u :=
  hX.evaluation_analysisSum n u

/-- The actually constructed Parseval synthesis is contractive because
its proved adjoint preserves the actual module norm. -/
theorem norm_synthesis_le_one : ‖hX.synthesis‖ ≤ 1 := by
  change ‖hX.synthesis.toCLM‖ ≤ 1
  rw [← AdjointableMap.norm_adjoint_toCLM hX.synthesis]
  change ‖hX.analysisIsometry.toContinuousLinearMap‖ ≤ 1
  apply hX.analysisIsometry.toContinuousLinearMap.opNorm_le_bound zero_le_one
  intro u
  change ‖hX.analysisSum u‖ ≤ 1 * ‖u‖
  simpa only [one_mul, hX.norm_analysisSum] using le_rfl (a := ‖u‖)

/-- The synthesis coisometry identity is a proved equality of actual operators. -/
theorem synthesis_comp_adjoint : hX.synthesis.comp hX.synthesis.adjoint = AdjointableMap.id := by
  ext u
  apply module_inner_ext_left (B := B)
  intro v
  change ⟪hX.synthesis (hX.synthesis.adjoint u), v⟫_(Bᵐᵒᵖ) = ⟪u, v⟫_(Bᵐᵒᵖ)
  rw [hX.synthesis.adjoint_identity]
  change ⟪hX.analysisSum u, hX.analysisSum v⟫_(Bᵐᵒᵖ) = ⟪u, v⟫_(Bᵐᵒᵖ)
  exact hX.inner_analysisSum u v

end HasParsevalOperatorCoordinates
end BC4lean.KKTheory
