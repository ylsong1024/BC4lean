import BC4lean.ModuleParsevalFrame
import BC4lean.ModuleCoordinateAnalysis
import BC4lean.ModuleTensorCompact
import BC4lean.InteriorModuleTensorCountableGeneration

/-! # The actual Parseval creation-row coisometry on the interior tensor

A proved Parseval frame on E gives the actual coordinate maps θξ* from
E ⊗ψ F to F. The partial coefficient forms equal the form of the actual
first-factor frame cutoffs, which converge strongly to the identity on the
constructed tensor. The coefficient-convergent column and its genuine finite
row adjoint are then constructed in the true countable module sum. In
particular the row is a proved coisometry into E ⊗ψ F. No complemented
essential submodule of F is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped InnerProductSpace Topology

variable {B C E F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

private def tensorFrameApplyCLM {D M N : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D]
    [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Dᵐᵒᵖ M] [CStarModule Dᵐᵒᵖ M]
    [NormedAddCommGroup N] [NormedSpace ℂ N] [SMul Dᵐᵒᵖ N] [CStarModule Dᵐᵒᵖ N] (u : M) :
    AdjointableMap D M N →L[ℂ] N :=
  (ContinuousLinearMap.apply ℂ N u).comp AdjointableMap.toCLMContinuousLinearMap

namespace ModuleParsevalFrame
variable {ξ : ℕ → E} (P : ModuleParsevalFrame (B := B) ξ)

omit [CompleteSpace E] in
theorem norm_analysis_le_one : ‖P.analysis‖ ≤ 1 := by
  change ‖P.analysis.toCLM‖ ≤ 1
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [one_mul]
  have hn : ‖P.analysis.toCLM u‖ = ‖u‖ := by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ), P.inner_analysis,
      ← CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ)]
  exact hn.le

/-- The actual finite first-factor frame cutoff. -/
def partialOperator (N : ℕ) : AdjointableMap B E E :=
  (P.analysis.adjoint.comp (standardCountableCutoff N)).comp P.analysis

omit [CompleteSpace E] in
theorem partialOperator_apply (N : ℕ) (u : E) :
    P.partialOperator N u = ∑ n ∈ Finset.range N, ⟪ξ n, u⟫_(Bᵐᵒᵖ) • ξ n := by
  simp only [partialOperator, AdjointableMap.comp_apply, standardCountableCutoff_apply,
    map_sum, P.coordinate, P.adjoint_inclusion]

omit [CompleteSpace E] in
theorem partialOperator_eq_sum (N : ℕ) :
    P.partialOperator N = ∑ n ∈ Finset.range N, moduleRankOne (B := B) (ξ n) (ξ n) := by
  ext u
  have heval := _root_.map_sum (tensorFrameApplyCLM (D := B) (M := E) (N := E) u)
    (fun n => moduleRankOne (B := B) (ξ n) (ξ n)) (Finset.range N)
  simpa only [tensorFrameApplyCLM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    AdjointableMap.toCLMContinuousLinearMap_apply, moduleRankOne_apply, P.partialOperator_apply] using heval.symm

omit [CompleteSpace E] in
theorem norm_partialOperator_le_one (N : ℕ) : ‖P.partialOperator N‖ ≤ 1 := by
  have hadj : ‖P.analysis.adjoint‖ ≤ 1 := by
    change ‖P.analysis.adjoint.toCLM‖ ≤ 1
    rw [AdjointableMap.norm_adjoint_toCLM]
    exact P.norm_analysis_le_one
  calc
    ‖P.partialOperator N‖ ≤ (‖P.analysis.adjoint‖ * ‖standardCountableCutoff (B := B) N‖) *
        ‖P.analysis‖ := by
      exact (AdjointableMap.norm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (AdjointableMap.norm_comp_le _ _) (norm_nonneg _))
    _ ≤ (1 * 1) * 1 := by
      gcongr
      · exact norm_standardCountableCutoff_le N
      · exact P.norm_analysis_le_one
    _ = 1 := by norm_num

omit [CompleteSpace E] in
theorem partialOperator_tendsto (u : E) :
    Tendsto (fun N => P.partialOperator N u) atTop (𝓝 u) := by
  simpa only [P.partialOperator_apply] using P.reconstruction_tendsto u

end ModuleParsevalFrame

private theorem tensorFrame_strongLimit_of_dense
    {D M : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Dᵐᵒᵖ M] [CStarModule Dᵐᵒᵖ M]
    (R : ℕ → AdjointableMap D M M) (hR : ∀ n, ‖R n‖ ≤ 1)
    (s : Set M) (hs : Dense s) (hlim : ∀ u ∈ s, Tendsto (fun n => R n u) atTop (𝓝 u))
    (u : M) : Tendsto (fun n => R n u) atTop (𝓝 u) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨v, hv, huv⟩ := hs.exists_dist_lt u (by positivity : 0 < ε / 3)
  have hevent := Metric.tendsto_nhds.mp (hlim v hv) (ε / 3) (by positivity)
  filter_upwards [hevent] with n hn
  have hdist : dist (R n u) (R n v) ≤ dist u v := by
    rw [dist_eq_norm, ← map_sub]
    exact ((R n).norm_apply_le _).trans (by
      simpa only [AdjointableMap.norm_def, one_mul, dist_eq_norm] using
        mul_le_mul_of_nonneg_right (hR n) (norm_nonneg _))
  calc
    dist (R n u) u ≤ dist (R n u) (R n v) + dist (R n v) v + dist v u :=
      (dist_triangle (R n u) (R n v) u).trans (by
        linarith [dist_triangle (R n v) v u])
    _ ≤ dist u v + dist (R n v) v + dist v u := by gcongr
    _ < ε := by rw [dist_comm v u]; linarith

namespace ModuleParsevalFrame
variable {ξ : ℕ → E} (P : ModuleParsevalFrame (B := B) ξ)
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)

/-- The actual tensor of finite frame cutoffs converges strongly to the identity. -/
theorem tensor_partialOperator_tendsto (u : InteriorModuleTensor (E := E) φ) :
    Tendsto (fun N => interiorModuleTensorOperator φ (P.partialOperator N) u) atTop (𝓝 u) := by
  let s := Submodule.span ℂ (Set.range fun p : E × F => interiorModuleTensorMk φ p.1 p.2)
  apply tensorFrame_strongLimit_of_dense
    (fun N => interiorModuleTensorOperator φ (P.partialOperator N))
    (fun N => (interiorModuleTensorOperator_norm_le φ _).trans (P.norm_partialOperator_le_one N))
    (s : Set _) (interiorModuleTensor_span_dense φ)
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨x, y⟩, rfl⟩ := hv
    simpa only [Function.comp_def, interiorModuleTensorOperator_mk,
      interiorModuleTensorLeftCLM_apply] using
      (interiorModuleTensorLeftCLM φ y).continuous.tendsto x |>.comp (P.partialOperator_tendsto x)
  | zero => simpa only [map_zero] using (tendsto_const_nhds (x := (0 : InteriorModuleTensor (E := E) φ)))
  | add v w _ _ hv hw => simpa only [map_add] using hv.add hw
  | smul c v _ hv => simpa only [map_smul, RingHom.id_apply] using hv.const_smul c

theorem tensor_partialOperator_eq_sum (N : ℕ) :
    interiorModuleTensorOperator φ (P.partialOperator N) =
      ∑ n ∈ Finset.range N, (moduleCreationMap φ (ξ n)).comp (moduleCreationMap φ (ξ n)).adjoint := by
  rw [P.partialOperator_eq_sum]
  change (interiorModuleTensorOperatorHom φ)
      (∑ n ∈ Finset.range N, moduleRankOne (B := B) (ξ n) (ξ n)) = _
  rw [map_sum]
  simp only [interiorModuleTensorOperatorHom_apply, interiorModuleTensorOperator_rankOne]

/-- The creation-adjoint partial coordinate form is exactly the tensor cutoff form. -/
theorem tensor_coordinate_partial_inner (N : ℕ) (u v : InteriorModuleTensor (E := E) φ) :
    (∑ n ∈ Finset.range N,
      ⟪(moduleCreationMap φ (ξ n)).adjoint u,
        (moduleCreationMap φ (ξ n)).adjoint v⟫_(Cᵐᵒᵖ)) =
      ⟪u, interiorModuleTensorOperator φ (P.partialOperator N) v⟫_(Cᵐᵒᵖ) := by
  rw [P.tensor_partialOperator_eq_sum φ]
  have happly := _root_.map_sum (tensorFrameApplyCLM (D := C)
    (M := InteriorModuleTensor (E := E) φ) (N := InteriorModuleTensor (E := E) φ) v)
    (fun n => (moduleCreationMap φ (ξ n)).comp (moduleCreationMap φ (ξ n)).adjoint) (Finset.range N)
  simp only [tensorFrameApplyCLM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    AdjointableMap.toCLMContinuousLinearMap_apply] at happly
  rw [happly, CStarModule.inner_sum_right (A := Cᵐᵒᵖ)
    (E := InteriorModuleTensor (E := E) φ)]
  exact Finset.sum_congr rfl (fun n _ => (moduleCreationMap φ (ξ n)).adjoint.adjoint_identity _ _)

include P in
/-- The actual tensor creation-adjoint family has proved Parseval coefficient convergence. -/
theorem tensorCoordinates :
    HasParsevalOperatorCoordinates (fun n => (moduleCreationMap φ (ξ n)).adjoint) where
  partial_inner_tendsto u v := by
    simpa only [Function.comp_def, CStarModule.innerSL_apply,
      P.tensor_coordinate_partial_inner φ] using
      (CStarModule.innerSL (A := Cᵐᵒᵖ) u).continuous.tendsto v |>.comp
        (P.tensor_partialOperator_tendsto φ v)

/-- The actual row of creation maps into the constructed interior tensor. -/
def tensorSynthesis :
    AdjointableMap C (CountableHilbertModuleSum C F) (InteriorModuleTensor (E := E) φ) :=
  (P.tensorCoordinates φ).synthesis

theorem norm_tensorSynthesis_le_one : ‖P.tensorSynthesis φ‖ ≤ 1 :=
  (P.tensorCoordinates φ).norm_synthesis_le_one

/-- The actual creation row is a proved coisometry, without an essential-range projection assumption. -/
theorem tensorSynthesis_comp_adjoint :
    (P.tensorSynthesis φ).comp (P.tensorSynthesis φ).adjoint = AdjointableMap.id :=
  (P.tensorCoordinates φ).synthesis_comp_adjoint

@[simp] theorem evaluation_tensorSynthesis_adjoint (n : ℕ) (u : InteriorModuleTensor (E := E) φ) :
    countableModuleEvaluation (B := C) n ((P.tensorSynthesis φ).adjoint u) =
      (moduleCreationMap φ (ξ n)).adjoint u :=
  (P.tensorCoordinates φ).evaluation_synthesis_adjoint n u

end ModuleParsevalFrame
end BC4lean.KKTheory
