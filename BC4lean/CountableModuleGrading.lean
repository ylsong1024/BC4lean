import BC4lean.CountableModuleOperator
import BC4lean.GradedHilbertModule
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! # Actual signed gradings on countable Hilbert-module sums

The coordinate grading is `y_n ↦ (-1)^p_n J(y_n)`. Its coefficient form
transports by the actual coefficient grading, so it preserves the genuine
finite-vector norm, descends to the null quotient, and extends to its norm
completion. This construction applies to semilinear module gradings.
-/

noncomputable section
namespace BC4lean.KKTheory
open UniformSpace
open scoped InnerProductSpace

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]
  {δB : CStarGrading B}

def signedModuleGradingCLM (J : GradedHilbertModule δB E) (p : ℕ → Bool) (n : ℕ) : E →L[ℂ] E :=
  if p n then -J.grading.toContinuousLinearEquiv.toContinuousLinearMap
  else J.grading.toContinuousLinearEquiv.toContinuousLinearMap

omit [StarOrderedRing B] [CompleteSpace E] in
@[simp] theorem signedModuleGradingCLM_apply (J : GradedHilbertModule δB E)
    (p : ℕ → Bool) (n : ℕ) (u : E) :
    signedModuleGradingCLM J p n u = if p n then -J.grading u else J.grading u := by
  cases hp : p n <;> simp [signedModuleGradingCLM, hp]

def signedCountableGradingLinear (J : GradedHilbertModule δB E) (p : ℕ → Bool) :
    CountableModuleVectors E →ₗ[ℂ] CountableModuleVectors E :=
  Finsupp.lsum ℂ (fun n => (Finsupp.lsingle n).comp (signedModuleGradingCLM J p n).toLinearMap)

omit [StarOrderedRing B] [CompleteSpace E] in
@[simp] theorem signedCountableGradingLinear_apply (J : GradedHilbertModule δB E)
    (p : ℕ → Bool) (u : CountableModuleVectors E) (n : ℕ) :
    signedCountableGradingLinear J p u n = if p n then -J.grading (u n) else J.grading (u n) := by
  classical
  rw [signedCountableGradingLinear, Finsupp.lsum_apply, Finsupp.sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single n]
  · simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Finsupp.single_eq_same]
    change signedModuleGradingCLM J p n (u n) = _
    exact signedModuleGradingCLM_apply J p n (u n)
  · intro m hm hmn
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Finsupp.single_eq_of_ne hmn.symm]
  · intro hn
    rw [Finsupp.notMem_support_iff.mp hn]
    cases p n <;> simp

omit [StarOrderedRing B] [CompleteSpace E] in
theorem signedCountableGradingLinear_support_subset (J : GradedHilbertModule δB E)
    (p : ℕ → Bool) (u : CountableModuleVectors E) :
    (signedCountableGradingLinear J p u).support ⊆ u.support := by
  intro n hn
  contrapose! hn
  rw [Finsupp.notMem_support_iff, signedCountableGradingLinear_apply,
    Finsupp.notMem_support_iff.mp hn]
  cases p n <;> simp

omit [StarOrderedRing B] [CompleteSpace E] in
theorem signedCountableGradingLinear_inner (J : GradedHilbertModule δB E)
    (p : ℕ → Bool) (u v : CountableModuleVectors E) :
    countableModuleFiniteInner (B := B) (signedCountableGradingLinear J p u)
      (signedCountableGradingLinear J p v) =
      opStarAlgEquiv δB.automorphism (countableModuleFiniteInner (B := B) u v) := by
  rw [countableModuleFiniteInner_eq_sum _ _ u.support
    (signedCountableGradingLinear_support_subset J p u),
    countableModuleFiniteInner_eq_sum u v u.support Finset.Subset.rfl, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [signedCountableGradingLinear_apply, signedCountableGradingLinear_apply]
  cases p n <;> simp only [Bool.false_eq_true, if_false, if_true,
    CStarModule.inner_neg_left, CStarModule.inner_neg_right, neg_neg, J.inner_grading]

omit [CompleteSpace E] in
theorem signedCountableGradingLinear_formNorm (J : GradedHilbertModule δB E)
    (p : ℕ → Bool) (u : CountableModuleVectors E) :
    PositiveModuleForm.formNorm (B := B) (signedCountableGradingLinear J p u) =
      PositiveModuleForm.formNorm (B := B) u := by
  rw [PositiveModuleForm.formNorm, countableModuleFinite_inner,
    signedCountableGradingLinear_inner, StarAlgEquiv.norm_map (opStarAlgEquiv δB.automorphism)]
  rfl

omit [StarOrderedRing B] [CompleteSpace E] in
theorem signedCountableGradingLinear_involutive (J : GradedHilbertModule δB E)
    (p : ℕ → Bool) (u : CountableModuleVectors E) :
    signedCountableGradingLinear J p (signedCountableGradingLinear J p u) = u := by
  ext n
  rw [signedCountableGradingLinear_apply, signedCountableGradingLinear_apply]
  cases p n <;> simp only [Bool.false_eq_true, if_false, if_true, map_neg,
    J.grading_sq, neg_neg]

def signedCountableGradingPreCLM (J : GradedHilbertModule δB E) (p : ℕ → Bool) :
    CountableHilbertModulePreSum B E →L[ℂ] CountableHilbertModulePreSum B E :=
  positiveModuleQuotientLiftCLM (signedCountableGradingLinear J p) (K := 1)
    (fun u => by rw [signedCountableGradingLinear_formNorm, one_mul])

omit [CompleteSpace E] in
@[simp] theorem signedCountableGradingPreCLM_mk (J : GradedHilbertModule δB E)
    (p : ℕ → Bool) (u : CountableModuleVectors E) :
    signedCountableGradingPreCLM J p (positiveModuleQuotientMk (B := B) u) =
      positiveModuleQuotientMk (B := B) (signedCountableGradingLinear J p u) :=
  positiveModuleQuotientLiftCLM_mk _ _ u

def signedCountableGradingCLM (J : GradedHilbertModule δB E) (p : ℕ → Bool) :
    CountableHilbertModuleSum B E →L[ℂ] CountableHilbertModuleSum B E :=
  (signedCountableGradingPreCLM J p).completion

omit [CompleteSpace E] in
@[simp] theorem signedCountableGradingCLM_mk (J : GradedHilbertModule δB E)
    (p : ℕ → Bool) (u : CountableModuleVectors E) :
    signedCountableGradingCLM J p (countableModuleMk (B := B) u) =
      countableModuleMk (B := B) (signedCountableGradingLinear J p u) := by
  rw [signedCountableGradingCLM, countableModuleMk_apply,
    ContinuousLinearMap.completion_apply_coe, signedCountableGradingPreCLM_mk]
  rfl

omit [CompleteSpace E] in
theorem signedCountableGradingCLM_inner (J : GradedHilbertModule δB E)
    (p : ℕ → Bool) (u v : CountableHilbertModuleSum B E) :
    ⟪signedCountableGradingCLM J p u, signedCountableGradingCLM J p v⟫_(Bᵐᵒᵖ) =
      opStarAlgEquiv δB.automorphism ⟪u, v⟫_(Bᵐᵒᵖ) := by
  have he := (countableModuleMk_denseRange (B := B) (E := E)).prodMap
    (countableModuleMk_denseRange (B := B) (E := E)) |>.equalizer
    (CStarModule.continuous_inner.comp
      ((signedCountableGradingCLM J p).continuous.comp continuous_fst |>.prodMk
        ((signedCountableGradingCLM J p).continuous.comp continuous_snd)))
    ((StarAlgEquiv.isometry (opStarAlgEquiv δB.automorphism)).continuous.comp CStarModule.continuous_inner)
    (by
      funext w
      change ⟪signedCountableGradingCLM J p (countableModuleMk (B := B) w.1),
        signedCountableGradingCLM J p (countableModuleMk (B := B) w.2)⟫_(Bᵐᵒᵖ) =
        opStarAlgEquiv δB.automorphism
          ⟪countableModuleMk (B := B) w.1, countableModuleMk (B := B) w.2⟫_(Bᵐᵒᵖ)
      simp only [signedCountableGradingCLM_mk, countableModuleMk_inner,
        signedCountableGradingLinear_inner])
  exact congrFun he (u, v)

omit [CompleteSpace E] in
theorem signedCountableGradingCLM_involutive (J : GradedHilbertModule δB E)
    (p : ℕ → Bool) : Function.Involutive (signedCountableGradingCLM J p) := by
  have he := (countableModuleMk_denseRange (B := B) (E := E)).equalizer
    ((signedCountableGradingCLM J p).continuous.comp (signedCountableGradingCLM J p).continuous)
    continuous_id (by
      funext u
      change signedCountableGradingCLM J p
        (signedCountableGradingCLM J p (countableModuleMk (B := B) u)) =
          countableModuleMk (B := B) u
      simp only [signedCountableGradingCLM_mk, signedCountableGradingLinear_involutive])
  exact congrFun he

/-- The actual coefficient-twisted signed grading of the completed sum. -/
def signedCountableModuleGrading (J : GradedHilbertModule δB E) (p : ℕ → Bool) :
    GradedHilbertModule δB (CountableHilbertModuleSum B E) where
  grading :=
    { toLinearEquiv :=
        { toLinearMap := (signedCountableGradingCLM J p).toLinearMap
          invFun := signedCountableGradingCLM J p
          left_inv := signedCountableGradingCLM_involutive J p
          right_inv := signedCountableGradingCLM_involutive J p }
      norm_map' u := by
        change ‖signedCountableGradingCLM J p u‖ = ‖u‖
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ),
          signedCountableGradingCLM_inner, StarAlgEquiv.norm_map (opStarAlgEquiv δB.automorphism)]
        exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) u).symm }
  involutive := signedCountableGradingCLM_involutive J p
  inner_grading := signedCountableGradingCLM_inner J p

@[simp] theorem countableModuleEvaluation_signedGrading (J : GradedHilbertModule δB E)
    (p : ℕ → Bool) (n : ℕ) (u : CountableHilbertModuleSum B E) :
    countableModuleEvaluation (B := B) n ((signedCountableModuleGrading J p).grading u) =
      if p n then -J.grading (countableModuleEvaluation (B := B) n u)
      else J.grading (countableModuleEvaluation (B := B) n u) := by
  have he := (countableModuleMk_denseRange (B := B) (E := E)).equalizer
    ((countableModuleEvaluation (B := B) n).toCLM.continuous.comp
      (signedCountableGradingCLM J p).continuous)
    ((signedModuleGradingCLM J p n).continuous.comp
      (countableModuleEvaluation (B := B) n).toCLM.continuous) (by
      funext v
      change countableModuleEvaluation (B := B) n
          (signedCountableGradingCLM J p (countableModuleMk (B := B) v)) =
        signedModuleGradingCLM J p n
          (countableModuleEvaluation (B := B) n (countableModuleMk (B := B) v))
      simp only [signedCountableGradingCLM_mk, countableModuleEvaluation_mk,
        signedCountableGradingLinear_apply, signedModuleGradingCLM_apply])
  have hu := congrFun he u
  change countableModuleEvaluation (B := B) n (signedCountableGradingCLM J p u) =
    signedModuleGradingCLM J p n (countableModuleEvaluation (B := B) n u) at hu
  change countableModuleEvaluation (B := B) n (signedCountableGradingCLM J p u) = _
  rw [signedModuleGradingCLM_apply] at hu
  exact hu

@[simp] theorem signedCountableModuleGrading_inclusion (J : GradedHilbertModule δB E)
    (p : ℕ → Bool) (n : ℕ) (u : E) :
    (signedCountableModuleGrading J p).grading (countableModuleInclusion (B := B) n u) =
      countableModuleInclusion (B := B) n (if p n then -J.grading u else J.grading u) := by
  apply countableModule_ext_eval
  intro m
  rw [countableModuleEvaluation_signedGrading, countableModuleEvaluation_inclusion,
    countableModuleEvaluation_inclusion]
  by_cases hnm : n = m
  · subst m
    simp only [if_true]
  · simp only [if_neg hnm, map_zero, neg_zero]
    cases p m <;> rfl

/-- Bounded complex-linear maps on the actual countable sum are determined
by their values on coordinate inclusions. -/
theorem countableModule_clm_ext_inclusion {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f g : CountableHilbertModuleSum B E →L[ℂ] F}
    (h : ∀ n u, f (countableModuleInclusion (B := B) n u) =
      g (countableModuleInclusion (B := B) n u)) : f = g := by
  apply ContinuousLinearMap.ext
  intro z
  refine (countableModuleMk_denseRange (B := B) (E := E)).induction_on z
    (isClosed_eq f.continuous g.continuous) ?_
  intro u
  have hu : countableModuleMk (B := B) u =
      ∑ n ∈ u.support, countableModuleInclusion (B := B) n (u n) := by
    simp only [countableModuleInclusion_apply, ← map_sum]
    exact congrArg (countableModuleMk (B := B)) u.sum_single.symm
  rw [hu, map_sum, map_sum]
  exact Finset.sum_congr rfl (fun n _ => h n (u n))

/-- The genuine B-linear coordinate-sign operator; no semilinear module
grading is represented by an adjointable map. -/
def countableModuleSigns (p : ℕ → Bool) :
    AdjointableMap B (CountableHilbertModuleSum B E) (CountableHilbertModuleSum B E) :=
  (signedCountableModuleGrading (GradedHilbertModule.trivial (B := B) (E := E)) p).toAdjointable

@[simp] theorem countableModuleEvaluation_signs (p : ℕ → Bool) (n : ℕ)
    (u : CountableHilbertModuleSum B E) :
    countableModuleEvaluation (B := B) n (countableModuleSigns p u) =
      if p n then -countableModuleEvaluation (B := B) n u else countableModuleEvaluation (B := B) n u :=
  countableModuleEvaluation_signedGrading GradedHilbertModule.trivial p n u

omit [CompleteSpace E] in
theorem norm_countableModuleSigns_le (p : ℕ → Bool) :
    ‖countableModuleSigns (B := B) (E := E) p‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖(signedCountableModuleGrading GradedHilbertModule.trivial p).grading u‖ ≤ _
  rw [LinearIsometryEquiv.norm_map, one_mul]

/-- The actual signed diagonal of an adjointable operator. -/
def countableModuleSignedDiagonal (p : ℕ → Bool) (S : AdjointableMap B E E) :
    AdjointableMap B (CountableHilbertModuleSum B E) (CountableHilbertModuleSum B E) :=
  (countableModuleSigns p).comp (countableModuleDiagonal S)

@[simp] theorem countableModuleEvaluation_signedDiagonal (p : ℕ → Bool)
    (S : AdjointableMap B E E) (n : ℕ) (u : CountableHilbertModuleSum B E) :
    countableModuleEvaluation (B := B) n (countableModuleSignedDiagonal p S u) =
      if p n then -S (countableModuleEvaluation (B := B) n u)
      else S (countableModuleEvaluation (B := B) n u) := by
  rw [countableModuleSignedDiagonal, AdjointableMap.comp_apply,
    countableModuleEvaluation_signs, countableModuleEvaluation_diagonal]

theorem norm_countableModuleSignedDiagonal_le (p : ℕ → Bool) (S : AdjointableMap B E E) :
    ‖countableModuleSignedDiagonal p S‖ ≤ ‖S‖ := by
  calc
    ‖countableModuleSignedDiagonal p S‖ ≤ ‖countableModuleSigns (B := B) (E := E) p‖ *
      ‖countableModuleDiagonal S‖ := AdjointableMap.norm_comp_le _ _
    _ ≤ 1 * ‖S‖ := mul_le_mul (norm_countableModuleSigns_le p)
      (norm_countableModuleDiagonal_le S) (norm_nonneg _) zero_le_one
    _ = ‖S‖ := one_mul _

theorem countableModuleSignedDiagonal_adjoint (p : ℕ → Bool) (S : AdjointableMap B E E) :
    (countableModuleSignedDiagonal p S).adjoint = countableModuleSignedDiagonal p S.adjoint := by
  have hsign : (countableModuleSigns (B := B) (E := E) p).adjoint = countableModuleSigns p := by
    change (signedCountableModuleGrading GradedHilbertModule.trivial p).toAdjointable.adjoint =
      (signedCountableModuleGrading GradedHilbertModule.trivial p).toAdjointable
    exact GradedHilbertModule.toAdjointable_adjoint _
  rw [countableModuleSignedDiagonal, AdjointableMap.adjoint_comp,
    countableModuleDiagonal_adjoint, hsign]
  ext u
  apply countableModule_ext_eval
  intro n
  rw [AdjointableMap.comp_apply, countableModuleEvaluation_diagonal,
    countableModuleEvaluation_signs, countableModuleEvaluation_signedDiagonal]
  cases p n
  · rfl
  · exact map_neg S.adjoint.toCLM _

@[simp] theorem countableModuleEvaluation_cutoff (N n : ℕ)
    (u : CountableHilbertModuleSum B E) :
    countableModuleEvaluation (B := B) n (countableModuleCutoff (B := B) N u) =
      if n < N then countableModuleEvaluation (B := B) n u else 0 := by
  have he := (countableModuleMk_denseRange (B := B) (E := E)).equalizer
    ((countableModuleEvaluation (B := B) n).toCLM.continuous.comp
      (countableModuleCutoff (B := B) N).toCLM.continuous)
    (show Continuous (fun u : CountableHilbertModuleSum B E =>
      if n < N then countableModuleEvaluation (B := B) n u else 0) from by
        split_ifs <;> fun_prop) (by
      funext v
      change countableModuleEvaluation (B := B) n
          (countableModuleCutoff (B := B) N (countableModuleMk (B := B) v)) =
        if n < N then countableModuleEvaluation (B := B) n (countableModuleMk (B := B) v) else 0
      simp only [countableModuleCutoff_mk, countableModuleEvaluation_mk, Finsupp.filter_apply])
  exact congrFun he u

/-- Signed diagonals commute with genuine finite coordinate cutoffs. -/
theorem countableModuleSignedDiagonal_comp_cutoff (p : ℕ → Bool)
    (S : AdjointableMap B E E) (N : ℕ) :
    (countableModuleSignedDiagonal p S).comp (countableModuleCutoff (B := B) N) =
      (countableModuleCutoff (B := B) N).comp (countableModuleSignedDiagonal p S) := by
  ext u
  apply countableModule_ext_eval
  intro n
  rw [AdjointableMap.comp_apply, AdjointableMap.comp_apply,
    countableModuleEvaluation_signedDiagonal, countableModuleEvaluation_cutoff,
    countableModuleEvaluation_cutoff, countableModuleEvaluation_signedDiagonal]
  split_ifs <;> simp only [map_zero, neg_zero]

theorem countableModuleSignedDiagonal_isOdd (J : GradedHilbertModule δB E)
    (p : ℕ → Bool) {S : AdjointableMap B E E} (hS : J.IsOdd J S) :
    (signedCountableModuleGrading J p).IsOdd (signedCountableModuleGrading J p)
      (countableModuleSignedDiagonal p S) := by
  intro u
  apply countableModule_ext_eval
  intro n
  rw [countableModuleEvaluation_signedGrading, countableModuleEvaluation_signedDiagonal,
    map_neg, countableModuleEvaluation_signedDiagonal, countableModuleEvaluation_signedGrading]
  cases p n
  · change J.grading (S (countableModuleEvaluation (B := B) n u)) =
      -S (J.grading (countableModuleEvaluation (B := B) n u))
    exact hS _
  · change -J.grading (-S (countableModuleEvaluation (B := B) n u)) =
      -(-S (-J.grading (countableModuleEvaluation (B := B) n u)))
    rw [map_neg, map_neg, neg_neg, neg_neg]
    exact hS _

end BC4lean.KKTheory
