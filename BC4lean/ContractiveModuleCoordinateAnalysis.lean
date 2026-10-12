import BC4lean.CountableModuleSequence
import BC4lean.HilbertModuleJuliaSqrt
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! # Actual contractive adjointable columns from convergent coordinates

A finite coefficient-square bound and Cauchy convergence in the genuine
countable-module norm construct an actual contractive column. Its adjoint
row is proved by finite coefficient pairings and extended from the dense
finite-coordinate submodule. The positive source square is therefore an
actual positive contraction. These are generic analytic hypotheses; a
technical-theorem band construction must discharge them for its operators.
-/

noncomputable section
namespace BC4lean.KKTheory

open Filter
open scoped InnerProductSpace Topology

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

/-- The precise finite bound and actual norm-convergence conditions for
constructing a contractive adjointable operator column. -/
structure HasContractiveOperatorCoordinates (X : ℕ → AdjointableMap B E F) : Prop where
  finite_inner_le (N : ℕ) (u : E) :
    (∑ n ∈ Finset.range N, ⟪X n u, X n u⟫_(Bᵐᵒᵖ)) ≤ ⟪u, u⟫_(Bᵐᵒᵖ)
  truncation_cauchy (u : E) :
    CauchySeq (countableModuleTruncation (B := B) (fun n => X n u))

omit [CompleteSpace E] [CompleteSpace F] in
/-- The genuine band tail inequality implies Cauchy convergence of the
actual module-coordinate truncations from strong convergence of its controls. -/
theorem moduleCoordinateTruncation_cauchy_of_strong_order_tails
    (X : ℕ → AdjointableMap B E F) (e : ℕ → AdjointableMap B E E)
    (he : ∀ u : E, Tendsto (fun N => e N u) atTop (𝓝 u))
    (htail : ∀ (u : E) (N M : ℕ), N ≤ M →
      (∑ n ∈ Finset.range M, ⟪X n u, X n u⟫_(Bᵐᵒᵖ)) -
        (∑ n ∈ Finset.range N, ⟪X n u, X n u⟫_(Bᵐᵒᵖ)) ≤
          ⟪u, (e M - e N) u⟫_(Bᵐᵒᵖ)) (u : E) :
    CauchySeq (countableModuleTruncation (B := B) (fun n => X n u)) := by
  have hbound (N M : ℕ) (hNM : N ≤ M) :
      dist (countableModuleTruncation (B := B) (fun n => X n u) M)
        (countableModuleTruncation (B := B) (fun n => X n u) N) ^ 2 ≤
          ‖u‖ * dist (e M u) (e N u) := by
    have hpos : 0 ≤ (∑ n ∈ Finset.range M, ⟪X n u, X n u⟫_(Bᵐᵒᵖ)) -
        ∑ n ∈ Finset.range N, ⟪X n u, X n u⟫_(Bᵐᵒᵖ) := by
      rw [← Finset.sum_sdiff_eq_sub (Finset.range_mono hNM)]
      exact Finset.sum_nonneg (fun n _ => CStarModule.inner_self_nonneg)
    rw [dist_eq_norm, countableModuleTruncation_difference_norm_sq _ hNM]
    have h := (CStarAlgebra.norm_le_norm_of_nonneg_of_le hpos (htail u N M hNM)).trans
      (CStarModule.norm_inner_le E (x := u) (y := (e M - e N) u))
    simpa only [AdjointableMap.coe_sub_apply, dist_eq_norm] using h
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hδ : 0 < ε ^ 2 / (‖u‖ + 1) := by positivity
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (he u).cauchySeq _ hδ
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hsmall := hN m hm n hn
  have hmul : ‖u‖ * dist (e m u) (e n u) < ε ^ 2 := by
    have h := (lt_div_iff₀ (by positivity : 0 < ‖u‖ + 1)).mp hsmall
    nlinarith [(dist_nonneg : 0 ≤ dist (e m u) (e n u))]
  have hsq : dist (countableModuleTruncation (B := B) (fun n => X n u) m)
      (countableModuleTruncation (B := B) (fun n => X n u) n) ^ 2 < ε ^ 2 := by
    rcases le_total n m with hnm | hmn
    · exact (hbound n m hnm).trans_lt hmul
    · rw [dist_comm]
      have hmul' : ‖u‖ * dist (e n u) (e m u) < ε ^ 2 := by
        simpa only [dist_comm] using hmul
      exact (hbound m n hmn).trans_lt hmul'
  nlinarith [(dist_nonneg : 0 ≤ dist
    (countableModuleTruncation (B := B) (fun n => X n u) m)
    (countableModuleTruncation (B := B) (fun n => X n u) n))]

namespace HasContractiveOperatorCoordinates

variable {X : ℕ → AdjointableMap B E F} (hX : HasContractiveOperatorCoordinates X)

/-- The column vector is the limit in the already constructed actual countable sum. -/
def analysisSum (_hX : HasContractiveOperatorCoordinates X) (u : E) :
    CountableHilbertModuleSum B F := countableModuleSequenceSum (fun n => X n u)

omit [CompleteSpace E] [CompleteSpace F] in
theorem truncation_tendsto (u : E) :
    Tendsto (countableModuleTruncation (B := B) (fun n => X n u)) atTop
      (𝓝 (hX.analysisSum u)) :=
  (hX.truncation_cauchy u).tendsto_limUnder

omit [CompleteSpace E] in
@[simp] theorem evaluation_analysisSum (n : ℕ) (u : E) :
    countableModuleEvaluation (B := B) n (hX.analysisSum u) = X n u := by
  have ht := (countableModuleEvaluation (B := B) (E := F) n).toCLM.continuous.tendsto
    (hX.analysisSum u) |>.comp (hX.truncation_tendsto u)
  have hc : Tendsto (fun N => countableModuleEvaluation (B := B) n
      (countableModuleTruncation (B := B) (fun k => X k u) N)) atTop (𝓝 (X n u)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (n + 1)] with N hN
    simp only [countableModuleTruncation, countableModuleEvaluation_mk,
      countableModuleFiniteSection_apply, Finset.mem_range, if_pos (by omega : n < N)]
  exact tendsto_nhds_unique ht hc

omit [CompleteSpace E] [CompleteSpace F] in
/-- Every coefficient partial sum converges to the actual column inner product. -/
theorem partial_inner_tendsto (u v : E) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, ⟪X n u, X n v⟫_(Bᵐᵒᵖ)) atTop
      (𝓝 ⟪hX.analysisSum u, hX.analysisSum v⟫_(Bᵐᵒᵖ)) := by
  have h := (CStarModule.continuous_inner (A := Bᵐᵒᵖ)
    (E := CountableHilbertModuleSum B F)).tendsto (hX.analysisSum u, hX.analysisSum v) |>.comp
    ((hX.truncation_tendsto u).prodMk_nhds (hX.truncation_tendsto v))
  simpa only [Function.comp_def, countableModuleTruncation_inner] using h

omit [CompleteSpace E] [CompleteSpace F] in
include hX in
theorem norm_truncation_le (N : ℕ) (u : E) :
    ‖countableModuleTruncation (B := B) (fun n => X n u) N‖ ≤ ‖u‖ := by
  have h := CStarAlgebra.norm_le_norm_of_nonneg_of_le
    (Finset.sum_nonneg (fun n _ => CStarModule.inner_self_nonneg)) (hX.finite_inner_le N u)
  rw [← countableModuleTruncation_inner,
    ← CStarModule.norm_sq_eq (Bᵐᵒᵖ) (x := u),
    ← CStarModule.norm_sq_eq (Bᵐᵒᵖ)
      (x := countableModuleTruncation (B := B) (fun n => X n u) N)] at h
  nlinarith [norm_nonneg (countableModuleTruncation (B := B) (fun n => X n u) N), norm_nonneg u]

omit [CompleteSpace E] [CompleteSpace F] in
theorem norm_analysisSum_le (u : E) : ‖hX.analysisSum u‖ ≤ ‖u‖ :=
  le_of_tendsto' (hX.truncation_tendsto u).norm (fun N => hX.norm_truncation_le N u)

def analysisLinearMap : E →ₗ[ℂ] CountableHilbertModuleSum B F where
  toFun := hX.analysisSum
  map_add' u v := by
    apply countableModule_ext_eval
    intro n
    simp only [map_add, hX.evaluation_analysisSum]
  map_smul' c u := by
    apply countableModule_ext_eval
    intro n
    simp only [map_smul, hX.evaluation_analysisSum, RingHom.id_apply]

/-- The actual bounded column before packaging its proved adjoint. -/
def analysisCLM : E →L[ℂ] CountableHilbertModuleSum B F :=
  hX.analysisLinearMap.mkContinuous 1 (fun u => by
    change ‖hX.analysisSum u‖ ≤ 1 * ‖u‖
    simpa only [one_mul] using hX.norm_analysisSum_le u)

def finiteRow (_hX : HasContractiveOperatorCoordinates X) : CountableModuleVectors F →ₗ[ℂ] E :=
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
    exact (CStarModule.norm_inner_le (CountableHilbertModuleSum B F)
      (x := countableModuleMk (B := B) v) (y := hX.analysisSum u)).trans
      (mul_le_mul_of_nonneg_left (hX.norm_analysisSum_le u) (norm_nonneg _))
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

/-- The actual adjointable row, with its proved contractive column as adjoint. -/
def synthesis : AdjointableMap B (CountableHilbertModuleSum B F) E where
  toCLM := hX.rowCLM
  adjointCLM := hX.analysisCLM
  adjoint_identity v u := by
    change ⟪hX.rowCLM v, u⟫_(Bᵐᵒᵖ) = ⟪v, hX.analysisSum u⟫_(Bᵐᵒᵖ)
    refine (countableModuleMk_denseRange (B := B) (E := F)).induction_on v ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro w
      rw [hX.rowCLM_mk]
      exact hX.finiteRow_inner w u

/-- The constructed actual adjointable column. -/
def column : AdjointableMap B E (CountableHilbertModuleSum B F) := hX.synthesis.adjoint

@[simp] theorem synthesis_inclusion (n : ℕ) (u : F) :
    hX.synthesis (countableModuleInclusion (B := B) n u) = (X n).adjoint u := by
  rw [countableModuleInclusion_apply]
  change hX.rowCLM (countableModuleMk (B := B) (Finsupp.single n u)) = _
  rw [hX.rowCLM_mk]
  simp only [finiteRow, Finsupp.lsum_apply, Finsupp.sum_single_index, map_zero]
  rfl

@[simp] theorem column_apply (u : E) : hX.column u = hX.analysisSum u := rfl

@[simp] theorem evaluation_column (n : ℕ) (u : E) :
    countableModuleEvaluation (B := B) n (hX.column u) = X n u := hX.evaluation_analysisSum n u

theorem norm_column_le_one : ‖hX.column‖ ≤ 1 := by
  rw [AdjointableMap.norm_def]
  apply hX.analysisCLM.opNorm_le_bound zero_le_one
  intro u
  change ‖hX.analysisSum u‖ ≤ 1 * ‖u‖
  simpa only [one_mul] using hX.norm_analysisSum_le u

/-- The genuine source adjoint square supplied to the technical theorem. -/
def positiveSquare : AdjointableMap B E E := hX.column.adjoint.comp hX.column

local instance : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _

theorem positiveSquare_nonneg : 0 ≤ hX.positiveSquare :=
  (rectangular_adjoint_squares_nonneg hX.column).2

theorem positiveSquare_le_one : hX.positiveSquare ≤ 1 :=
  sub_nonneg.mp (one_sub_adjoint_comp_self_nonneg hX.column hX.norm_column_le_one)

theorem norm_positiveSquare_le_one : ‖hX.positiveSquare‖ ≤ 1 := by
  change ‖hX.column.adjoint.comp hX.column‖ ≤ 1
  rw [AdjointableMap.norm_def, AdjointableMap.norm_toCLM_adjoint_comp_self]
  change ‖hX.column‖ ^ 2 ≤ 1
  nlinarith [hX.norm_column_le_one, norm_nonneg hX.column]

/-- The finite source square acts by the actual finite synthesis of the
column truncation. -/
theorem finite_square_apply_eq_synthesis_truncation (N : ℕ) (u : E) :
    (∑ n ∈ Finset.range N, (X n).adjoint.comp (X n)) u =
      hX.synthesis (countableModuleTruncation (B := B) (fun n => X n u) N) := by
  have hsum (N : ℕ) : (∑ n ∈ Finset.range N, (X n).adjoint.comp (X n)) u =
      ∑ n ∈ Finset.range N, (X n).adjoint (X n u) := by
    induction N with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, AdjointableMap.coe_zero_apply]
    | succ N ih =>
      rw [Finset.sum_range_succ, AdjointableMap.coe_add_apply, Finset.sum_range_succ, ih]
      rfl
  rw [hsum]
  change _ = hX.rowCLM (countableModuleMk (B := B)
    (countableModuleFiniteSection (fun n => X n u) (Finset.range N)))
  rw [hX.rowCLM_mk, countableModuleFiniteSection, map_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp only [finiteRow, Finsupp.lsum_apply, Finsupp.sum_single_index, map_zero]
  rfl

/-- Actual finite source squares converge strongly to the constructed
positive contraction; coefficient convergence alone is not used here. -/
theorem finite_square_apply_tendsto (u : E) :
    Tendsto (fun N => (∑ n ∈ Finset.range N, (X n).adjoint.comp (X n)) u)
      atTop (𝓝 (hX.positiveSquare u)) := by
  have h := hX.synthesis.toCLM.continuous.tendsto (hX.analysisSum u) |>.comp
    (hX.truncation_tendsto u)
  change Tendsto (fun N => hX.synthesis
    (countableModuleTruncation (B := B) (fun n => X n u) N)) atTop
      (𝓝 (hX.synthesis (hX.analysisSum u))) at h
  have heq : hX.synthesis (hX.analysisSum u) = hX.positiveSquare u := rfl
  simpa only [← hX.finite_square_apply_eq_synthesis_truncation, heq] using h

/-- The actual positive square's coefficient form is the norm-limit of the
finite coordinate-square forms. -/
theorem partial_inner_tendsto_positiveSquare (u v : E) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, ⟪X n u, X n v⟫_(Bᵐᵒᵖ)) atTop
      (𝓝 ⟪u, hX.positiveSquare v⟫_(Bᵐᵒᵖ)) := by
  have heq : ⟪hX.analysisSum u, hX.analysisSum v⟫_(Bᵐᵒᵖ) =
      ⟪u, hX.positiveSquare v⟫_(Bᵐᵒᵖ) := by
    exact hX.column.adjoint_identity u (hX.column v)
  rw [← heq]
  exact hX.partial_inner_tendsto u v

end HasContractiveOperatorCoordinates
end BC4lean.KKTheory
