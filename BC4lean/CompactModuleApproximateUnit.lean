import BC4lean.CompactModuleOperator
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit

/-! # Genuine strong compact-operator approximate units

The compact algebra acts on the original Hilbert module through its actual
adjointable operators. The diagonal rank-one norm identity and the compact
algebra's two-sided approximate unit prove strong convergence on every vector.
No compact-algebra-valued inner product on the module is introduced.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace Topology
open CStarModule Filter

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

/-- The actual diagonal rank-one map has the square of the vector norm. -/
theorem moduleRankOne_self_norm (x : E) :
    ‖moduleRankOne (B := B) x x‖ = ‖x‖ ^ 2 := by
  apply le_antisymm
  · simpa only [AdjointableMap.norm_def, pow_two] using moduleRankOne_norm_le (B := B) x x
  · by_cases hx : x = 0
    · subst x
      simp
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let a := ⟪x, x⟫_(Bᵐᵒᵖ)
    have ha : IsSelfAdjoint a := (CStarModule.inner_self_nonneg (x := x)).isSelfAdjoint
    have hpair : ⟪x, moduleRankOne (B := B) x x x⟫_(Bᵐᵒᵖ) = a * a := by
      simp only [moduleRankOne_apply, inner_op_smul_right, a]
    have hnorm : ‖x‖ ^ 2 * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 * ‖moduleRankOne (B := B) x x‖ := by
      calc
        ‖x‖ ^ 2 * ‖x‖ ^ 2 = ‖a * a‖ := by
          rw [ha.norm_mul_self]
          change ‖x‖ ^ 2 * ‖x‖ ^ 2 = ‖⟪x, x⟫_(Bᵐᵒᵖ)‖ ^ 2
          rw [← CStarModule.norm_sq_eq (Bᵐᵒᵖ)]
          ring
        _ = ‖⟪x, moduleRankOne (B := B) x x x⟫_(Bᵐᵒᵖ)‖ := by rw [hpair]
        _ ≤ ‖x‖ * ‖moduleRankOne (B := B) x x x‖ := CStarModule.norm_inner_le E
        _ ≤ ‖x‖ * (‖moduleRankOne (B := B) x x‖ * ‖x‖) :=
          mul_le_mul_of_nonneg_left (AdjointableMap.norm_apply_le _ _) (norm_nonneg _)
        _ = _ := by ring
    exact le_of_mul_le_mul_left hnorm (sq_pos_of_pos hxnorm)

variable [CompleteSpace E]

local instance : PartialOrder (CompactModuleOperator B E) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (CompactModuleOperator B E) := CStarAlgebra.spectralOrderedRing _

omit [CompleteSpace E] in
/-- Compression of a diagonal rank one by an actual residual is the
diagonal rank one of the residual vector. -/
theorem moduleRankOne_self_residual (T : AdjointableMap B E E) (x : E) :
    moduleRankOne (B := B) ((1 - T) x) ((1 - T) x) =
      (1 - T) * moduleRankOne x x * star (1 - T) := by
  rw [AdjointableMap.star_eq_adjoint]
  change moduleRankOne ((1 - T) x) ((1 - T) x) =
    ((1 - T).comp (moduleRankOne x x)).comp (1 - T).adjoint
  rw [comp_moduleRankOne, moduleRankOne_comp, AdjointableMap.adjoint_adjoint]

/-- A norm bound on the actual residual and its compact multiplication
error controls the vector's squared strong-action error. -/
theorem compact_approximateUnit_vector_error_sq_le
    (e : CompactModuleOperator B E) (he : ‖e‖ ≤ 1) (x : E) :
    ‖x - (e : AdjointableMap B E E) x‖ ^ 2 ≤
      2 * ‖(e : AdjointableMap B E E) * moduleRankOne x x - moduleRankOne x x‖ := by
  let T : AdjointableMap B E E := e
  have hT : ‖T‖ ≤ 1 := he
  have hI : ‖(1 : AdjointableMap B E E)‖ ≤ 1 := by
    change ‖ContinuousLinearMap.id ℂ E‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  have hR : ‖1 - T‖ ≤ 2 := by
    calc
      ‖1 - T‖ ≤ ‖(1 : AdjointableMap B E E)‖ + ‖T‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add hI hT
      _ = 2 := by norm_num
  have heq : (1 - T) * moduleRankOne (B := B) x x =
      -(T * moduleRankOne x x - moduleRankOne x x) := by
    rw [sub_mul, one_mul]
    abel
  calc
    ‖x - T x‖ ^ 2 = ‖moduleRankOne (B := B) ((1 - T) x) ((1 - T) x)‖ := by
      rw [moduleRankOne_self_norm, AdjointableMap.coe_sub_apply, AdjointableMap.one_apply]
    _ = ‖(1 - T) * moduleRankOne x x * star (1 - T)‖ := by
      rw [moduleRankOne_self_residual]
    _ ≤ ‖(1 - T) * moduleRankOne x x‖ * ‖star (1 - T)‖ := norm_mul_le _ _
    _ = ‖T * moduleRankOne x x - moduleRankOne x x‖ * ‖1 - T‖ := by
      rw [heq, norm_neg, norm_star]
    _ ≤ ‖T * moduleRankOne x x - moduleRankOne x x‖ * 2 :=
      mul_le_mul_of_nonneg_left hR (norm_nonneg _)
    _ = _ := mul_comm _ _

/-- Every actual increasing compact-algebra approximate-unit filter acts
strongly on the original Hilbert module. -/
theorem tendsto_compact_approximateUnit_apply
    {l : Filter (CompactModuleOperator B E)} (hau : l.IsIncreasingApproximateUnit) (x : E) :
    Tendsto (fun e : CompactModuleOperator B E => (e : AdjointableMap B E E) x) l (𝓝 x) := by
  let θ : CompactModuleOperator B E :=
    ⟨moduleRankOne x x, moduleRankOne_mem_moduleCompact x x⟩
  have hlim : Tendsto (fun e : CompactModuleOperator B E => ‖e * θ - θ‖) l (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      ((hau.tendsto_mul_right θ).sub (tendsto_const_nhds (x := θ))).norm
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall : ∀ᶠ e : CompactModuleOperator B E in l, ‖e * θ - θ‖ < ε ^ 2 / 2 :=
    hlim.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hau.eventually_norm, hsmall] with e he herr
  rw [dist_eq_norm, norm_sub_rev]
  have hsq := compact_approximateUnit_vector_error_sq_le e he x
  change ‖(e : AdjointableMap B E E) * moduleRankOne x x - moduleRankOne x x‖ <
    ε ^ 2 / 2 at herr
  nlinarith [norm_nonneg (x - (e : AdjointableMap B E E) x)]

/-- In particular, Mathlib's canonical proper compact approximate-unit
filter converges strongly on every module vector. -/
theorem tendsto_canonical_compact_approximateUnit_apply (x : E) :
    Tendsto (fun e : CompactModuleOperator B E => (e : AdjointableMap B E E) x)
      (CStarAlgebra.approximateUnit (CompactModuleOperator B E)) (𝓝 x) :=
  tendsto_compact_approximateUnit_apply
    (CStarAlgebra.increasingApproximateUnit (CompactModuleOperator B E)) x

/-- An actual positive contractive two-sided compact approximate-unit
sequence supplies an approximate-unit filter with its genuine limit data. -/
theorem compact_sequence_isIncreasingApproximateUnit
    (u : ℕ → CompactModuleOperator B E) (hu0 : ∀ n, 0 ≤ u n) (hu1 : ∀ n, ‖u n‖ ≤ 1)
    (hleft : ∀ a, Tendsto (fun n => a * u n) atTop (𝓝 a))
    (hright : ∀ a, Tendsto (fun n => u n * a) atTop (𝓝 a)) :
    (Filter.map u atTop).IsIncreasingApproximateUnit where
  neBot := inferInstance
  tendsto_mul_left a := by
    rw [Filter.tendsto_map'_iff]
    exact hleft a
  tendsto_mul_right a := by
    rw [Filter.tendsto_map'_iff]
    exact hright a
  eventually_nonneg := by
    change ∀ᶠ n : ℕ in atTop, 0 ≤ u n
    exact Eventually.of_forall hu0
  eventually_norm := by
    change ∀ᶠ n : ℕ in atTop, ‖u n‖ ≤ 1
    exact Eventually.of_forall hu1

/-- The genuine compact approximate-unit sequence therefore acts strongly
on every vector of the original module. -/
theorem tendsto_compact_sequence_apply
    (u : ℕ → CompactModuleOperator B E) (hu0 : ∀ n, 0 ≤ u n) (hu1 : ∀ n, ‖u n‖ ≤ 1)
    (hleft : ∀ a, Tendsto (fun n => a * u n) atTop (𝓝 a))
    (hright : ∀ a, Tendsto (fun n => u n * a) atTop (𝓝 a)) (x : E) :
    Tendsto (fun n => (u n : AdjointableMap B E E) x) atTop (𝓝 x) := by
  have h := tendsto_compact_approximateUnit_apply
    (compact_sequence_isIncreasingApproximateUnit u hu0 hu1 hleft hright) x
  rwa [Filter.tendsto_map'_iff] at h

end BC4lean.KKTheory
