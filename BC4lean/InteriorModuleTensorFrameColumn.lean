import BC4lean.InteriorModuleTensorFrame
import BC4lean.CountableModuleOperator
import Mathlib.Tactic.NoncommRing

/-! # Operator-norm tails of genuine frame creation columns

For the constructed creation-row coisometry W, the localized column W*θξ
has coordinates ψ(⟨ξₙ,ξ⟩). Its tail square is exactly the represented
coefficient ⟨ξ, ξ-P_Nξ⟩, where the proved frame cutoff P_N converges strongly
to the identity. This proves operator-norm column-tail convergence. It does
not assume real square-norm summability or compactness of θξ.
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

namespace ModuleParsevalFrame
variable {ξ : ℕ → E} (P : ModuleParsevalFrame (B := B) ξ)
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)

@[simp] theorem tensorSynthesis_inclusion (n : ℕ) (y : F) :
    P.tensorSynthesis φ (countableModuleInclusion (B := C) n y) = moduleCreationMap φ (ξ n) y :=
  (P.tensorCoordinates φ).synthesis_inclusion n y

/-- The actual coordinate cutoff compressed by W is the actual tensor frame cutoff. -/
theorem tensorSynthesis_cutoff_comp_adjoint (N : ℕ) :
    ((P.tensorSynthesis φ).comp (countableModuleCutoff (B := C) N)).comp
      (P.tensorSynthesis φ).adjoint = interiorModuleTensorOperator φ (P.partialOperator N) := by
  ext u
  rw [AdjointableMap.comp_apply, AdjointableMap.comp_apply, countableModuleCutoff_apply, map_sum]
  simp only [P.tensorSynthesis_inclusion φ, P.evaluation_tensorSynthesis_adjoint φ]
  rw [P.tensor_partialOperator_eq_sum φ]
  let L := (ContinuousLinearMap.apply ℂ (InteriorModuleTensor (E := E) φ) u).comp
    (AdjointableMap.toCLMContinuousLinearMap (B := C))
  have hsum := _root_.map_sum L
    (fun n => (moduleCreationMap φ (ξ n)).comp (moduleCreationMap φ (ξ n)).adjoint) (Finset.range N)
  simpa only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    AdjointableMap.toCLMContinuousLinearMap_apply, AdjointableMap.comp_apply] using hsum.symm

/-- The actual localized analysis column; no compactness of creation is assumed. -/
def tensorCreationColumn (x : E) : AdjointableMap C F (CountableHilbertModuleSum C F) :=
  (P.tensorSynthesis φ).adjoint.comp (moduleCreationMap φ x)

@[simp] theorem evaluation_tensorCreationColumn (n : ℕ) (x : E) :
    (countableModuleEvaluation (B := C) n).comp (P.tensorCreationColumn φ x) =
      φ (MulOpposite.unop ⟪ξ n, x⟫_(Bᵐᵒᵖ)) := by
  ext y
  rw [AdjointableMap.comp_apply]
  change countableModuleEvaluation (B := C) n
    ((P.tensorSynthesis φ).adjoint (moduleCreationMap φ x y)) = _
  rw [P.evaluation_tensorSynthesis_adjoint φ]
  exact congrArg (fun T : AdjointableMap C F F => T y) (moduleCreationMap_adjoint_comp φ (ξ n) x)

/-- The genuine column-tail square is the represented coefficient frame residual. -/
theorem tensorCreationColumn_tail_square (x : E) (N : ℕ) :
    (P.tensorCreationColumn φ x -
      (countableModuleCutoff (B := C) N).comp (P.tensorCreationColumn φ x)).adjoint.comp
      (P.tensorCreationColumn φ x -
        (countableModuleCutoff (B := C) N).comp (P.tensorCreationColumn φ x)) =
      φ (MulOpposite.unop ⟪x, x - P.partialOperator N x⟫_(Bᵐᵒᵖ)) := by
  let W := P.tensorSynthesis φ
  let A := W.adjoint
  let V := P.tensorCreationColumn φ x
  let Cn := countableModuleCutoff (B := C) (E := F) N
  let D := 1 - Cn
  have hCnstar : Cn.adjoint = Cn := countableModuleCutoff_adjoint (B := C) (E := F) N
  have hDstar : D.adjoint = D := by
    change star (1 - Cn) = 1 - Cn
    rw [star_sub, star_one, AdjointableMap.star_eq_adjoint, hCnstar]
  have hCnsq : Cn * Cn = Cn := countableModuleCutoff_square (B := C) (E := F) N
  have hDsq : D * D = D := by
    change (1 - Cn) * (1 - Cn) = 1 - Cn
    have heq : (1 - Cn) * (1 - Cn) = 1 - Cn - Cn + Cn * Cn := by noncomm_ring
    rw [heq, hCnsq]
    abel
  have htail : V - Cn.comp V = D.comp V := by
    ext y
    simp only [AdjointableMap.coe_sub_apply, AdjointableMap.comp_apply,
      AdjointableMap.one_apply, D]
  have hDsquare : (D.comp V).adjoint.comp (D.comp V) = V.adjoint.comp (D.comp V) := by
    rw [AdjointableMap.adjoint_comp, hDstar]
    ext y
    exact congrArg V.adjoint (congrArg (fun R => R (V y)) hDsq)
  have hcompressed : (W.comp D).comp A = 1 - interiorModuleTensorOperator φ (P.partialOperator N) := by
    ext u
    simp only [AdjointableMap.comp_apply, D, AdjointableMap.coe_sub_apply,
      AdjointableMap.one_apply]
    rw [W.toCLM.map_sub]
    have hWA : W (A u) = u :=
      congrArg (fun R => R u) (P.tensorSynthesis_comp_adjoint φ)
    have hWC : W (Cn (A u)) = interiorModuleTensorOperator φ (P.partialOperator N) u :=
      congrArg (fun R => R u) (P.tensorSynthesis_cutoff_comp_adjoint φ N)
    rw [hWA, hWC]
  have hDcreation : (1 - interiorModuleTensorOperator φ (P.partialOperator N)).comp
      (moduleCreationMap φ x) = moduleCreationMap φ (x - P.partialOperator N x) := by
    ext y
    simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply, AdjointableMap.one_apply]
    have hT := congrArg (fun R => R y) (moduleCreationMap_tensorOperator φ (P.partialOperator N) x)
    simp only [AdjointableMap.comp_apply] at hT
    rw [hT]
    simp only [sub_eq_add_neg, moduleCreationMap_add, moduleCreationMap_neg,
      AdjointableMap.coe_add_apply, AdjointableMap.coe_neg_apply]
  change (V - Cn.comp V).adjoint.comp (V - Cn.comp V) = _
  rw [htail, hDsquare]
  have heq : V.adjoint.comp (D.comp V) =
      (moduleCreationMap φ x).adjoint.comp (((W.comp D).comp A).comp (moduleCreationMap φ x)) := by
    dsimp only [V, tensorCreationColumn, A, W]
    rw [AdjointableMap.adjoint_comp, AdjointableMap.adjoint_adjoint]
    ext y
    rfl
  rw [heq, hcompressed, hDcreation, moduleCreationMap_adjoint_comp]

theorem norm_tensorCreationColumn_tail_le (x : E) (N : ℕ) :
    ‖P.tensorCreationColumn φ x -
      (countableModuleCutoff (B := C) N).comp (P.tensorCreationColumn φ x)‖ ≤
      Real.sqrt (‖x‖ * ‖x - P.partialOperator N x‖) := by
  let T := P.tensorCreationColumn φ x -
    (countableModuleCutoff (B := C) N).comp (P.tensorCreationColumn φ x)
  have hsq : ‖T‖ ^ 2 ≤ ‖x‖ * ‖x - P.partialOperator N x‖ := by
    have hnorm : ‖T.adjoint.comp T‖ = ‖T‖ ^ 2 := by
      simpa only [AdjointableMap.norm_def] using
        (AdjointableMap.norm_toCLM_adjoint_comp_self T)
    rw [← hnorm]
    dsimp only [T]
    rw [P.tensorCreationColumn_tail_square φ x N]
    exact (NonUnitalStarAlgHom.norm_apply_le φ _).trans (by
      simpa only [MulOpposite.norm_unop] using CStarModule.norm_inner_le E
        (x := x) (y := x - P.partialOperator N x))
  calc
    ‖T‖ = Real.sqrt (‖T‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖x‖ * ‖x - P.partialOperator N x‖) := Real.sqrt_le_sqrt hsq

/-- The actual localized column tails tend to zero in operator norm. -/
theorem tensorCreationColumn_norm_tail_tendsto_zero (x : E) :
    Tendsto (fun N => ‖P.tensorCreationColumn φ x -
      (countableModuleCutoff (B := C) N).comp (P.tensorCreationColumn φ x)‖) atTop (𝓝 0) := by
  have hx : Tendsto (fun _ : ℕ => x) atTop (𝓝 x) := tendsto_const_nhds
  have hres : Tendsto (fun N => ‖x - P.partialOperator N x‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hx.sub (P.partialOperator_tendsto x)).norm
  have hprod : Tendsto (fun N => ‖x‖ * ‖x - P.partialOperator N x‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using hres.const_mul ‖x‖
  have hsqrt : Tendsto (fun N => Real.sqrt (‖x‖ * ‖x - P.partialOperator N x‖)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hprod
  exact squeeze_zero (fun _ => norm_nonneg _) (P.norm_tensorCreationColumn_tail_le φ x) hsqrt

end ModuleParsevalFrame
end BC4lean.KKTheory
