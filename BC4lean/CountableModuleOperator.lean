import BC4lean.CountableModuleSequence
import BC4lean.ModuleOperatorPositivity
import Mathlib.Data.Finsupp.Basic

/-! # Actual diagonals and coordinate cutoffs on countable Hilbert-module sums

The diagonal of a bounded adjointable operator is constructed on the genuine
finite coefficient-form vectors, descends with its actual adjoint, and extends
to the completion. Its norm bound is proved in the coefficient norm. The
coordinate cutoffs are actual selfadjoint projections converging strongly to
the identity; they are not declared compact.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped InnerProductSpace Topology

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

def countableModuleDiagonalLinear (S : AdjointableMap B E E) :
    CountableModuleVectors E →ₗ[ℂ] CountableModuleVectors E :=
  Finsupp.mapRange.linearMap S.toCLM.toLinearMap

omit [StarOrderedRing B] [CompleteSpace E] in
@[simp] theorem countableModuleDiagonalLinear_apply
    (S : AdjointableMap B E E) (u : CountableModuleVectors E) (i : ℕ) :
    countableModuleDiagonalLinear S u i = S (u i) := rfl

omit [StarOrderedRing B] [CompleteSpace E] in
theorem countableModuleDiagonalLinear_support_subset
    (S : AdjointableMap B E E) (u : CountableModuleVectors E) :
    (countableModuleDiagonalLinear S u).support ⊆ u.support :=
  Finsupp.support_mapRange (hf := map_zero S.toCLM)

theorem countableModuleDiagonalLinear_formNorm_le
    (S : AdjointableMap B E E) (u : CountableModuleVectors E) :
    PositiveModuleForm.formNorm (B := B) (countableModuleDiagonalLinear S u) ≤
      ‖S‖ * PositiveModuleForm.formNorm (B := B) u := by
  have hinner : countableModuleFiniteInner (B := B) (countableModuleDiagonalLinear S u)
      (countableModuleDiagonalLinear S u) ≤ (‖S‖ ^ 2 : ℝ) • countableModuleFiniteInner (B := B) u u := by
    rw [countableModuleFiniteInner_eq_sum _ _ u.support (countableModuleDiagonalLinear_support_subset S u),
      countableModuleFiniteInner_eq_sum u u u.support Finset.Subset.rfl, Finset.smul_sum]
    exact Finset.sum_le_sum (fun i _ => S.inner_self_apply_le (u i))
  have hsq : PositiveModuleForm.formNorm (B := B) (countableModuleDiagonalLinear S u) ^ 2 ≤
      (‖S‖ * PositiveModuleForm.formNorm (B := B) u) ^ 2 := by
    rw [PositiveModuleForm.formNorm_sq, countableModuleFinite_inner,
      mul_pow, PositiveModuleForm.formNorm_sq, countableModuleFinite_inner]
    calc
      ‖countableModuleFiniteInner (B := B) (countableModuleDiagonalLinear S u)
          (countableModuleDiagonalLinear S u)‖ ≤
          ‖(‖S‖ ^ 2 : ℝ) • countableModuleFiniteInner (B := B) u u‖ :=
        CStarAlgebra.norm_le_norm_of_nonneg_of_le
          (PositiveModuleForm.inner_self_nonneg (B := B)
            (x := countableModuleDiagonalLinear S u)) hinner
      _ = ‖S‖ ^ 2 * ‖countableModuleFiniteInner (B := B) u u‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (pow_le_pow_iff_left₀ (PositiveModuleForm.formNorm_nonneg _)
    (mul_nonneg (norm_nonneg _) (PositiveModuleForm.formNorm_nonneg _)) (by decide : (2 : ℕ) ≠ 0)).mp hsq

def countableModuleDiagonalQuotient (S : AdjointableMap B E E) :
    AdjointableMap B (CountableHilbertModulePreSum B E) (CountableHilbertModulePreSum B E) where
  toCLM := positiveModuleQuotientLiftCLM (countableModuleDiagonalLinear S)
    (countableModuleDiagonalLinear_formNorm_le S)
  adjointCLM := positiveModuleQuotientLiftCLM (countableModuleDiagonalLinear S.adjoint)
    (countableModuleDiagonalLinear_formNorm_le S.adjoint)
  adjoint_identity u v := by
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective u
    obtain ⟨y, rfl⟩ := positiveModuleQuotientMk_surjective v
    rw [positiveModuleQuotientLiftCLM_mk, positiveModuleQuotientLiftCLM_mk,
      PositiveModuleQuotient.inner_mk, PositiveModuleQuotient.inner_mk]
    change countableModuleFiniteInner (B := B) (countableModuleDiagonalLinear S x) y =
      countableModuleFiniteInner (B := B) x (countableModuleDiagonalLinear S.adjoint y)
    rw [countableModuleFiniteInner_eq_sum _ _ x.support (countableModuleDiagonalLinear_support_subset S x),
      countableModuleFiniteInner_eq_sum _ _ x.support Finset.Subset.rfl]
    exact Finset.sum_congr rfl (fun i _ => S.adjoint_identity (x i) (y i))

/-- The genuine countable diagonal, with its actual completed adjoint. -/
def countableModuleDiagonal (S : AdjointableMap B E E) :
    AdjointableMap B (CountableHilbertModuleSum B E) (CountableHilbertModuleSum B E) :=
  (countableModuleDiagonalQuotient S).completion

@[simp] theorem countableModuleDiagonal_mk
    (S : AdjointableMap B E E) (u : CountableModuleVectors E) :
    countableModuleDiagonal S (countableModuleMk (B := B) u) =
      countableModuleMk (B := B) (countableModuleDiagonalLinear S u) := by
  rw [countableModuleDiagonal, countableModuleMk_apply, AdjointableMap.completion_apply_coe,
    countableModuleMk_apply]
  exact congrArg (fun q : CountableHilbertModulePreSum B E =>
    (q : CountableHilbertModuleSum B E))
      (positiveModuleQuotientLiftCLM_mk _ (countableModuleDiagonalLinear_formNorm_le S) u)

@[simp] theorem countableModuleDiagonal_adjoint (S : AdjointableMap B E E) :
    (countableModuleDiagonal S).adjoint = countableModuleDiagonal S.adjoint := by
  rw [countableModuleDiagonal, AdjointableMap.completion_adjoint]
  rfl

theorem norm_countableModuleDiagonal_le (S : AdjointableMap B E E) :
    ‖countableModuleDiagonal S‖ ≤ ‖S‖ := by
  rw [countableModuleDiagonal, AdjointableMap.norm_completion]
  exact norm_positiveModuleQuotientLiftCLM_le _ (norm_nonneg _)
    (countableModuleDiagonalLinear_formNorm_le S)

@[simp] theorem countableModuleEvaluation_diagonal
    (S : AdjointableMap B E E) (i : ℕ) (u : CountableHilbertModuleSum B E) :
    countableModuleEvaluation (B := B) i (countableModuleDiagonal S u) =
      S (countableModuleEvaluation (B := B) i u) := by
  have he := (countableModuleMk_denseRange (B := B) (E := E)).equalizer
    ((countableModuleEvaluation (B := B) i).toCLM.continuous.comp
      (countableModuleDiagonal S).toCLM.continuous)
    (S.toCLM.continuous.comp (countableModuleEvaluation (B := B) i).toCLM.continuous) (by
      funext v
      change countableModuleEvaluation (B := B) i
        (countableModuleDiagonal S (countableModuleMk (B := B) v)) =
          S (countableModuleEvaluation (B := B) i (countableModuleMk (B := B) v))
      simp only [countableModuleDiagonal_mk, countableModuleEvaluation_mk,
        countableModuleDiagonalLinear_apply])
  exact congrFun he u

@[simp] theorem countableModuleEvaluation_inclusion (i j : ℕ) (x : E) :
    countableModuleEvaluation (B := B) i (countableModuleInclusion (B := B) j x) =
      if j = i then x else 0 := by
  rw [countableModuleInclusion_apply, countableModuleEvaluation_mk]
  exact Finsupp.single_apply

/-- The actual finite coordinate projection. -/
def countableModuleCutoff (N : ℕ) :
    AdjointableMap B (CountableHilbertModuleSum B E) (CountableHilbertModuleSum B E) :=
  ∑ n ∈ Finset.range N,
    (countableModuleInclusion (B := B) n).comp (countableModuleEvaluation (B := B) n)

theorem countableModuleCutoff_apply (N : ℕ) (u : CountableHilbertModuleSum B E) :
    countableModuleCutoff (B := B) N u =
      ∑ n ∈ Finset.range N, countableModuleInclusion (B := B) n (countableModuleEvaluation (B := B) n u) := by
  have hsum (s : Finset ℕ) :
      (∑ n ∈ s, (countableModuleInclusion (B := B) n).comp (countableModuleEvaluation (B := B) n)) u =
        ∑ n ∈ s, countableModuleInclusion (B := B) n (countableModuleEvaluation (B := B) n u) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert n s hn ih =>
      simp only [Finset.sum_insert hn, AdjointableMap.coe_add_apply, ih, AdjointableMap.comp_apply]
  exact hsum (Finset.range N)

@[simp] theorem countableModuleCutoff_mk (N : ℕ) (u : CountableModuleVectors E) :
    countableModuleCutoff (B := B) N (countableModuleMk (B := B) u) =
      countableModuleMk (B := B) (u.filter (fun n => n < N)) := by
  have hsum (s : Finset ℕ) :
      (∑ n ∈ s, (countableModuleInclusion (B := B) n).comp (countableModuleEvaluation (B := B) n))
        (countableModuleMk (B := B) u) =
      ∑ n ∈ s, countableModuleInclusion (B := B) n (u n) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert n s hn ih =>
      simp only [Finset.sum_insert hn, AdjointableMap.coe_add_apply, ih,
        AdjointableMap.comp_apply, countableModuleEvaluation_mk]
  rw [countableModuleCutoff, hsum]
  simp only [countableModuleInclusion_apply, ← map_sum]
  congr 1
  ext i
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply, Finsupp.filter_apply, Finset.mem_range]

@[simp] theorem countableModuleCutoff_adjoint (N : ℕ) :
    (countableModuleCutoff (B := B) (E := E) N).adjoint = countableModuleCutoff N := by
  change star (countableModuleCutoff (B := B) (E := E) N) = countableModuleCutoff N
  simp only [countableModuleCutoff, star_sum, AdjointableMap.star_eq_adjoint,
    AdjointableMap.adjoint_comp, countableModuleEvaluation, AdjointableMap.adjoint_adjoint]

theorem countableModuleCutoff_square (N : ℕ) :
    countableModuleCutoff (B := B) (E := E) N * countableModuleCutoff N = countableModuleCutoff N := by
  have he := (countableModuleMk_denseRange (B := B) (E := E)).equalizer
    (countableModuleCutoff (B := B) (E := E) N * countableModuleCutoff N).toCLM.continuous
    (countableModuleCutoff (B := B) (E := E) N).toCLM.continuous (by
      funext u
      change countableModuleCutoff (B := B) (E := E) N
        (countableModuleCutoff (B := B) (E := E) N (countableModuleMk (B := B) u)) =
          countableModuleCutoff (B := B) (E := E) N (countableModuleMk (B := B) u)
      simp only [countableModuleCutoff_mk]
      congr 1
      ext n
      simp only [Finsupp.filter_apply]
      split_ifs <;> rfl)
  exact AdjointableMap.ext (fun u => congrFun he u)

theorem norm_countableModuleCutoff_le (N : ℕ) :
    ‖countableModuleCutoff (B := B) (E := E) N‖ ≤ 1 :=
  IsStarProjection.norm_le _ (isStarProjection_iff'.mpr
    ⟨countableModuleCutoff_square N, countableModuleCutoff_adjoint N⟩)

/-- The constant diagonal commutes with the actual finite coordinate projections. -/
theorem countableModuleDiagonal_comp_cutoff (S : AdjointableMap B E E) (N : ℕ) :
    (countableModuleDiagonal S).comp (countableModuleCutoff (B := B) N) =
      (countableModuleCutoff (B := B) N).comp (countableModuleDiagonal S) := by
  have he := (countableModuleMk_denseRange (B := B) (E := E)).equalizer
    ((countableModuleDiagonal S).comp (countableModuleCutoff (B := B) N)).toCLM.continuous
    ((countableModuleCutoff (B := B) N).comp (countableModuleDiagonal S)).toCLM.continuous (by
      funext u
      change ((countableModuleDiagonal S).comp (countableModuleCutoff (B := B) N))
        (countableModuleMk (B := B) u) =
          ((countableModuleCutoff (B := B) N).comp (countableModuleDiagonal S))
            (countableModuleMk (B := B) u)
      simp only [AdjointableMap.comp_apply, countableModuleCutoff_mk, countableModuleDiagonal_mk]
      congr 1
      ext i
      simp only [countableModuleDiagonalLinear_apply, Finsupp.filter_apply]
      split_ifs <;> simp only [map_zero])
  exact AdjointableMap.ext (fun u => congrFun he u)

/-- The actual cutoff sequence tends strongly to the identity by finite-vector density. -/
theorem countableModuleCutoff_tendsto (u : CountableHilbertModuleSum B E) :
    Tendsto (fun N => countableModuleCutoff (B := B) N u) atTop (𝓝 u) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨v, hv⟩ := (countableModuleMk_denseRange (B := B) (E := E)).exists_dist_lt u (by
    exact div_pos hε (by norm_num : (0 : ℝ) < 3))
  refine ⟨v.support.sup Nat.succ, ?_⟩
  intro N hN
  have hfix : countableModuleCutoff (B := B) N (countableModuleMk (B := B) v) =
      countableModuleMk (B := B) v := by
    rw [countableModuleCutoff_mk]
    congr 1
    apply (Finsupp.filter_eq_self_iff _ _).mpr
    intro i hi
    exact lt_of_lt_of_le
      (Nat.lt_of_succ_le (Finset.le_sup (f := Nat.succ) (Finsupp.mem_support_iff.mpr hi))) hN
  have hbound : dist (countableModuleCutoff (B := B) N u) (countableModuleMk (B := B) v) ≤
      dist u (countableModuleMk (B := B) v) := by
    calc
      dist (countableModuleCutoff (B := B) N u) (countableModuleMk (B := B) v) =
          ‖countableModuleCutoff (B := B) N (u - countableModuleMk (B := B) v)‖ := by
        rw [dist_eq_norm, map_sub, hfix]
      _ ≤ ‖countableModuleCutoff (B := B) (E := E) N‖ *
          ‖u - countableModuleMk (B := B) v‖ :=
        (countableModuleCutoff (B := B) N).norm_apply_le _
      _ ≤ 1 * ‖u - countableModuleMk (B := B) v‖ :=
        mul_le_mul_of_nonneg_right (norm_countableModuleCutoff_le (B := B) (E := E) N)
          (norm_nonneg (u - countableModuleMk (B := B) v))
      _ = dist u (countableModuleMk (B := B) v) := by rw [one_mul, dist_eq_norm]

  calc
    dist (countableModuleCutoff (B := B) N u) u ≤
        dist (countableModuleCutoff (B := B) N u) (countableModuleMk (B := B) v) +
          dist (countableModuleMk (B := B) v) u := dist_triangle _ _ _
    _ ≤ dist u (countableModuleMk (B := B) v) + dist (countableModuleMk (B := B) v) u :=
      add_le_add hbound le_rfl
    _ < ε := by rw [dist_comm (countableModuleMk (B := B) v) u]; linarith

end BC4lean.KKTheory
