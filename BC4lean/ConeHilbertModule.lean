import BC4lean.IntervalHilbertModule
import Mathlib.Topology.UniformSpace.Dini

/-! # The zero-endpoint cone Hilbert module

The cone is the actual closed kernel of evaluation at zero on continuous
sections. Its norm is the inherited supremum norm, its action and inner
product are pointwise, and completeness follows from the closed kernel.

Multiplication by the interval coordinate has dense range in the cone. The
regularized inverse sections give decreasing continuous norm errors, so
Dini's theorem proves uniform convergence. A countable generating sequence
for the original module therefore gives the explicit cone generators
`t ↦ t • ξ n`. Constant adjointable maps restrict to the cone.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace Topology
open CStarModule Filter

variable {B E F G : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]

/-- The actual zero-endpoint complex submodule of continuous sections. -/
def coneSectionSubmodule (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    Submodule ℂ C(unitInterval, E) :=
  (continuousSectionEvaluation (E := E) (0 : unitInterval)).ker

@[simp] theorem mem_coneSectionSubmodule (x : C(unitInterval, E)) :
    x ∈ coneSectionSubmodule E ↔ x 0 = 0 := Iff.rfl

theorem coneSectionSubmodule_isClosed :
    IsClosed (coneSectionSubmodule E : Set C(unitInterval, E)) :=
  (continuousSectionEvaluation (E := E) (0 : unitInterval)).isClosed_ker

/-- The cone uses the actual submodule norm inherited from continuous sections. -/
def ConeHilbertModule (B E : Type*) [NonUnitalCStarAlgebra B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] := coneSectionSubmodule E

namespace ConeHilbertModule

instance instNormedAddCommGroup : NormedAddCommGroup (ConeHilbertModule B E) :=
  inferInstanceAs (NormedAddCommGroup (coneSectionSubmodule E))

instance instModule : Module ℂ (ConeHilbertModule B E) :=
  inferInstanceAs (Module ℂ (coneSectionSubmodule E))

instance instNormedSpace : NormedSpace ℂ (ConeHilbertModule B E) :=
  inferInstanceAs (NormedSpace ℂ (coneSectionSubmodule E))

instance instCompleteSpace [CompleteSpace E] : CompleteSpace (ConeHilbertModule B E) :=
  coneSectionSubmodule_isClosed.isComplete.completeSpace_coe

instance instSMul : SMul C(unitInterval, B)ᵐᵒᵖ (ConeHilbertModule B E) where
  smul b x := ⟨b • x.1, by
    change MulOpposite.op (MulOpposite.unop b 0) • x.1 0 = 0
    have hx : x.1 0 = 0 := x.2
    rw [hx]
    exact (moduleActionContinuousLinearMap _).map_zero⟩

omit [StarOrderedRing B] in
@[simp] theorem coe_op_smul (b : C(unitInterval, B)ᵐᵒᵖ) (x : ConeHilbertModule B E) :
    (↑(b • x) : C(unitInterval, E)) = b • (x : C(unitInterval, E)) := rfl

omit [StarOrderedRing B] in
@[simp] theorem op_smul_apply (b : C(unitInterval, B)ᵐᵒᵖ)
    (x : ConeHilbertModule B E) (t : unitInterval) :
    (b • x).1 t = MulOpposite.op (MulOpposite.unop b t) • x.1 t := rfl

instance instCStarModule : CStarModule C(unitInterval, B)ᵐᵒᵖ (ConeHilbertModule B E) where
  inner x y := ⟪(x : C(unitInterval, E)), (y : C(unitInterval, E))⟫_(C(unitInterval, B)ᵐᵒᵖ)
  inner_add_right := CStarModule.inner_add_right
  inner_self_nonneg := CStarModule.inner_self_nonneg
  inner_self := by
    intro x
    rw [CStarModule.inner_self]
    exact ⟨fun hx => Subtype.ext hx, fun hx => congrArg Subtype.val hx⟩
  inner_op_smul_right := CStarModule.inner_op_smul_right
  inner_smul_right_complex := CStarModule.inner_smul_right_complex
  star_inner x y := CStarModule.star_inner x.1 y.1
  norm_eq_sqrt_norm_inner_self x := CStarModule.norm_eq_sqrt_norm_inner_self x.1

@[simp] theorem inner_apply (x y : ConeHilbertModule B E) (t : unitInterval) :
    MulOpposite.unop ⟪x, y⟫_(C(unitInterval, B)ᵐᵒᵖ) t =
      MulOpposite.unop ⟪x.1 t, y.1 t⟫_(Bᵐᵒᵖ) := rfl

omit [PartialOrder B] [StarOrderedRing B] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] in
@[simp] theorem apply_zero (x : ConeHilbertModule B E) : x.1 0 = 0 := x.2

omit [PartialOrder B] [StarOrderedRing B] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] in
@[simp] theorem norm_coe (x : ConeHilbertModule B E) : ‖(x : C(unitInterval, E))‖ = ‖x‖ := rfl

end ConeHilbertModule

/-- Multiplication by the interval coordinate, as an actual bounded map into
the cone. -/
def coneRampMap : C(unitInterval, E) →L[ℂ] ConeHilbertModule B E :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨⟨fun t => (t : ℝ) • x t,
          continuous_subtype_val.smul x.continuous⟩,
          by change (0 : ℝ) • x 0 = 0; exact zero_smul ℝ _⟩
      map_add' := fun x y => by apply Subtype.ext; ext t; exact smul_add _ _ _
      map_smul' := fun c x => by apply Subtype.ext; ext t; exact smul_comm _ _ _ }
    1 (fun x => by
      change ‖(⟨fun t => (t : ℝ) • x t,
        continuous_subtype_val.smul x.continuous⟩ : C(unitInterval, E))‖ ≤ 1 * ‖x‖
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (_root_.norm_nonneg _)).mpr
      intro t
      change ‖(t : ℝ) • x t‖ ≤ ‖x‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.2.1]
      exact (mul_le_mul_of_nonneg_right t.2.2 (_root_.norm_nonneg _)).trans
        (by simpa using x.norm_coe_le_norm t))

omit [PartialOrder B] [StarOrderedRing B] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] in
@[simp] theorem coneRampMap_apply (x : C(unitInterval, E)) (t : unitInterval) :
    (coneRampMap (B := B) x).1 t = (t : ℝ) • x t := rfl

/-- The explicit cone generator associated with a vector. -/
def coneGenerator (x : E) : ConeHilbertModule B E :=
  coneRampMap (ContinuousMap.const unitInterval x)

omit [PartialOrder B] [StarOrderedRing B] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] in
@[simp] theorem coneGenerator_apply (x : E) (t : unitInterval) :
    (coneGenerator (B := B) x).1 t = (t : ℝ) • x := rfl

omit [PartialOrder B] [StarOrderedRing B] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] in
@[simp] theorem coneGenerator_apply_one (x : E) :
    (coneGenerator (B := B) x).1 1 = x := by
  change (1 : ℝ) • x = x
  exact one_smul ℝ x

/-- Actual point evaluation on the closed cone submodule. -/
def coneEvaluation (t : unitInterval) : ConeHilbertModule B E →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := fun x => x.1 t
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun x => by
      change ‖x.1 t‖ ≤ 1 * ‖x.1‖
      rw [one_mul]
      exact x.1.norm_coe_le_norm t)

omit [PartialOrder B] [StarOrderedRing B] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] in
@[simp] theorem coneEvaluation_apply (t : unitInterval) (x : ConeHilbertModule B E) :
    coneEvaluation t x = x.1 t := rfl

omit [PartialOrder B] [StarOrderedRing B] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] in
@[simp] theorem coneEvaluation_zero : coneEvaluation (B := B) (E := E) 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  exact x.2

omit [PartialOrder B] [StarOrderedRing B] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] in
theorem coneEvaluation_one_surjective :
    Function.Surjective (coneEvaluation (B := B) (E := E) 1) :=
  fun x => ⟨coneGenerator (B := B) x, coneGenerator_apply_one (B := B) x⟩

theorem coneEvaluation_inner (t : unitInterval) (x y : ConeHilbertModule B E) :
    ⟪coneEvaluation t x, coneEvaluation t y⟫_(Bᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪x, y⟫_(C(unitInterval, B)ᵐᵒᵖ) t) := rfl

private theorem coneDenominator_pos (n : ℕ) (t : unitInterval) :
    0 < 1 + (t : ℝ) * ((n : ℝ) + 1) := by
  have ht := t.2.1
  positivity

/-- Continuous regularized inverse sections; multiplication by the coordinate
gives the cutoff `t / (t + 1/(n+1))`. -/
def coneRegularizedSection (x : ConeHilbertModule B E) (n : ℕ) : C(unitInterval, E) :=
  ⟨fun t => (((n : ℝ) + 1) / (1 + (t : ℝ) * ((n : ℝ) + 1))) • x.1 t,
    (continuous_const.div (continuous_const.add (continuous_subtype_val.mul continuous_const))
      (fun t => ne_of_gt (coneDenominator_pos n t))).smul x.1.continuous⟩

omit [PartialOrder B] [StarOrderedRing B] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] in
theorem coneRegularizedSection_error (x : ConeHilbertModule B E) (n : ℕ)
    (t : unitInterval) :
    x.1 t - (coneRampMap (B := B) (coneRegularizedSection x n)).1 t =
      (1 / (1 + (t : ℝ) * ((n : ℝ) + 1))) • x.1 t := by
  change x.1 t - (t : ℝ) •
    ((((n : ℝ) + 1) / (1 + (t : ℝ) * ((n : ℝ) + 1))) • x.1 t) = _
  calc
    _ = (1 - (t : ℝ) * (((n : ℝ) + 1) /
        (1 + (t : ℝ) * ((n : ℝ) + 1)))) • x.1 t := by
      rw [sub_smul, one_smul, smul_smul]
    _ = _ := by
      congr 1
      field_simp [ne_of_gt (coneDenominator_pos n t)]
      ring

private def coneErrorNorm (x : ConeHilbertModule B E) (n : ℕ) : C(unitInterval, ℝ) :=
  ⟨fun t => (1 / (1 + (t : ℝ) * ((n : ℝ) + 1))) * ‖x.1 t‖,
    (continuous_const.div (continuous_const.add (continuous_subtype_val.mul continuous_const))
      (fun t => ne_of_gt (coneDenominator_pos n t))).mul x.1.continuous.norm⟩

omit [PartialOrder B] [StarOrderedRing B] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] in
private theorem coneErrorNorm_eq (x : ConeHilbertModule B E) (n : ℕ)
    (t : unitInterval) :
    coneErrorNorm x n t =
      ‖x.1 t - (coneRampMap (B := B) (coneRegularizedSection x n)).1 t‖ := by
  rw [coneRegularizedSection_error, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (by norm_num) (coneDenominator_pos n t).le)]
  rfl

omit [PartialOrder B] [StarOrderedRing B] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] in
private theorem coneErrorNorm_antitone (x : ConeHilbertModule B E) :
    Antitone (coneErrorNorm x) := by
  intro m n hmn t
  apply mul_le_mul_of_nonneg_right _ (_root_.norm_nonneg _)
  apply one_div_le_one_div_of_le (coneDenominator_pos m t)
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ t.2.1
  exact_mod_cast Nat.add_le_add_right hmn 1

omit [PartialOrder B] [StarOrderedRing B] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] in
private theorem coneErrorNorm_tendsto (x : ConeHilbertModule B E) (t : unitInterval) :
    Tendsto (fun n => coneErrorNorm x n t) atTop (𝓝 0) := by
  by_cases ht : (t : ℝ) = 0
  · have ht0 : t = 0 := Subtype.ext ht
    subst t
    simp [coneErrorNorm]
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht)
    have hd : Tendsto (fun n : ℕ => 1 + (t : ℝ) * ((n : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_left _ 1
        ((tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).const_mul_atTop htpos)
    have hi := tendsto_inv_atTop_zero.comp hd
    simpa [coneErrorNorm, one_div] using hi.mul_const ‖x.1 t‖

omit [PartialOrder B] [StarOrderedRing B] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] in
/-- The regularized cutoff sections converge uniformly to the actual cone
section. Dini's theorem is applied to their decreasing continuous norm errors. -/
theorem coneRegularizedSection_tendsto (x : ConeHilbertModule B E) :
    Tendsto (fun n => coneRampMap (B := B) (coneRegularizedSection x n)) atTop (𝓝 x) := by
  have hd : Tendsto (coneErrorNorm x) atTop (𝓝 (0 : C(unitInterval, ℝ))) :=
    ContinuousMap.tendsto_of_antitone_of_pointwise (coneErrorNorm_antitone x)
      (coneErrorNorm_tendsto x)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he : ∀ᶠ n : ℕ in atTop, ‖coneErrorNorm x n‖ < ε := by
    have hd0 : Tendsto (fun n => ‖coneErrorNorm x n‖) atTop (𝓝 0) := by
      simpa only [norm_zero] using hd.norm
    exact hd0.eventually (Iio_mem_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_comm, dist_eq_norm]
  change ‖(x : C(unitInterval, E)) -
    (coneRampMap (B := B) (coneRegularizedSection x n) : C(unitInterval, E))‖ < ε
  apply (ContinuousMap.norm_lt_iff _ hε).mpr
  intro t
  change ‖x.1 t - (coneRampMap (B := B) (coneRegularizedSection x n)).1 t‖ < ε
  rw [← coneErrorNorm_eq]
  exact (le_trans (le_abs_self _) ((coneErrorNorm x n).norm_coe_le_norm t)).trans_lt (hN n hn)

omit [PartialOrder B] [StarOrderedRing B] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] in
theorem coneRampMap_denseRange : DenseRange (coneRampMap (B := B) (E := E)) := by
  intro x
  apply mem_closure_of_tendsto (coneRegularizedSection_tendsto x)
  exact Eventually.of_forall fun n => ⟨coneRegularizedSection x n, rfl⟩

omit [StarOrderedRing B] in
private theorem coneCoefficient_real_smul (a : Bᵐᵒᵖ) (r : ℝ) (x : E) :
    a • (r • x) = r • (a • x) := by
  simpa using module_smul_complex a (r : ℂ) x

omit [StarOrderedRing B] in
theorem coneRampMap_op_smul (a : C(unitInterval, B)ᵐᵒᵖ) (x : C(unitInterval, E)) :
    coneRampMap (B := B) (a • x) = a • coneRampMap x := by
  apply Subtype.ext
  ext t
  exact (coneCoefficient_real_smul _ _ _).symm

omit [StarOrderedRing B] in
private theorem constantSection_generatingSpan_dense (ξ : ℕ → E)
    (hξ : Dense (moduleGeneratingSpan (B := B) ξ : Set E)) :
    Dense (moduleGeneratingSpan (B := C(unitInterval, B))
      (fun n => ContinuousMap.const unitInterval (ξ n)) : Set C(unitInterval, E)) := by
  classical
  let η : ℕ → C(unitInterval, E) := fun n => ContinuousMap.const unitInterval (ξ n)
  have hweight : ∀ (ρ : C(unitInterval, ℝ)) x,
      x ∈ moduleGeneratingSpan (B := B) ξ →
      continuousSectionWeightLinearMap ρ x ∈ moduleGeneratingSpan (B := C(unitInterval, B)) η := by
    intro ρ x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, b, rfl⟩ := hx
      let a : C(unitInterval, B)ᵐᵒᵖ := MulOpposite.op
        ⟨fun t => (ρ t : ℂ) • MulOpposite.unop b, by fun_prop⟩
      have ha : continuousSectionWeightLinearMap ρ (b • ξ n) = a • η n := by
        ext t
        change ρ t • (b • ξ n) = ((ρ t : ℂ) • b) • ξ n
        rw [module_complex_smul]
        exact (algebraMap_smul ℂ (ρ t) (b • ξ n)).symm
      rw [ha]
      exact smul_mem_moduleGeneratingSpan η n a
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro f
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨s, ρ, q, _, _, hq, herr⟩ := exists_finite_partition_approximation f
    (moduleGeneratingSpan (B := B) ξ : Set E) (fun t => hξ (f t)) ε hε
  refine ⟨finitePartitionCombination s ρ q, ?_, ?_⟩
  · exact Submodule.sum_mem _ (fun j _ => hweight (ρ j) (q j) (hq j))
  · simpa only [dist_eq_norm] using herr

omit [StarOrderedRing B] in
/-- The explicit sequence `t ↦ t • ξ n` generates the cone densely whenever
`ξ` generates the original module densely. -/
theorem coneGenerator_generatingSpan_dense (ξ : ℕ → E)
    (hξ : Dense (moduleGeneratingSpan (B := B) ξ : Set E)) :
    Dense (moduleGeneratingSpan (B := C(unitInterval, B))
      (fun n => coneGenerator (B := B) (ξ n)) : Set (ConeHilbertModule B E)) := by
  let η : ℕ → C(unitInterval, E) := fun n => ContinuousMap.const unitInterval (ξ n)
  let ζ : ℕ → ConeHilbertModule B E := fun n => coneGenerator (ξ n)
  have hm : ∀ x ∈ moduleGeneratingSpan (B := C(unitInterval, B)) η,
      coneRampMap (B := B) x ∈ moduleGeneratingSpan (B := C(unitInterval, B)) ζ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, b, rfl⟩ := hx
      rw [coneRampMap_op_smul]
      exact smul_mem_moduleGeneratingSpan ζ n b
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  exact (coneRampMap_denseRange.dense_image coneRampMap.continuous
    (constantSection_generatingSpan_dense ξ hξ)).mono (by
      rintro y ⟨x, hx, rfl⟩
      exact hm x hx)

theorem cone_isCountablyGenerated (hE : IsCountablyGeneratedModule B E) :
    IsCountablyGeneratedModule C(unitInterval, B) (ConeHilbertModule B E) := by
  obtain ⟨ξ, hξ⟩ := hE
  exact ⟨fun n => coneGenerator (ξ n), coneGenerator_generatingSpan_dense ξ hξ⟩

/-- Restriction of a constant adjointable map to the actual cone submodule. -/
def coneOperatorCLM (T : AdjointableMap B E F) :
    ConeHilbertModule B E →L[ℂ] ConeHilbertModule B F :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨⟨fun t => T (x.1 t), T.toCLM.continuous.comp x.1.continuous⟩,
          by
            change T (x.1 0) = 0
            rw [ConeHilbertModule.apply_zero, map_zero]⟩
      map_add' := fun x y => by apply Subtype.ext; ext t; exact T.toCLM.map_add _ _
      map_smul' := fun c x => by apply Subtype.ext; ext t; exact T.toCLM.map_smul _ _ }
    ‖T‖ (fun x => by
      apply (ContinuousMap.norm_le _
        (mul_nonneg (_root_.norm_nonneg _) (_root_.norm_nonneg _))).mpr
      intro t
      exact (AdjointableMap.norm_apply_le T (x.1 t)).trans
        (mul_le_mul_of_nonneg_left (x.1.norm_coe_le_norm t) (_root_.norm_nonneg _)))

def coneOperator (T : AdjointableMap B E F) :
    AdjointableMap C(unitInterval, B) (ConeHilbertModule B E) (ConeHilbertModule B F) where
  toCLM := coneOperatorCLM T
  adjointCLM := coneOperatorCLM T.adjoint
  adjoint_identity x y := by
    apply MulOpposite.unop_injective
    ext t
    exact congrArg MulOpposite.unop (T.adjoint_identity (x.1 t) (y.1 t))

@[simp] theorem coneOperator_apply (T : AdjointableMap B E F)
    (x : ConeHilbertModule B E) (t : unitInterval) :
    (coneOperator T x).1 t = T (x.1 t) := rfl

@[simp] theorem coneOperator_zero : coneOperator (0 : AdjointableMap B E F) = 0 := by
  apply AdjointableMap.ext
  intro x
  apply Subtype.ext
  ext t
  rfl

@[simp] theorem coneOperator_add (S T : AdjointableMap B E F) :
    coneOperator (S + T) = coneOperator S + coneOperator T := by
  apply AdjointableMap.ext
  intro x
  apply Subtype.ext
  ext t
  rfl

@[simp] theorem coneOperator_smul (c : ℂ) (T : AdjointableMap B E F) :
    coneOperator (c • T) = c • coneOperator T := by
  apply AdjointableMap.ext
  intro x
  apply Subtype.ext
  ext t
  rfl

@[simp] theorem coneOperator_comp (S : AdjointableMap B F G) (T : AdjointableMap B E F) :
    coneOperator (S.comp T) = (coneOperator S).comp (coneOperator T) := by
  apply AdjointableMap.ext
  intro x
  apply Subtype.ext
  ext t
  rfl

@[simp] theorem coneOperator_adjoint (T : AdjointableMap B E F) :
    coneOperator T.adjoint = (coneOperator T).adjoint := by
  apply AdjointableMap.ext
  intro x
  apply Subtype.ext
  ext t
  rfl

@[simp] theorem coneOperator_one : coneOperator (1 : AdjointableMap B E E) = 1 := by
  apply AdjointableMap.ext
  intro x
  apply Subtype.ext
  ext t
  rfl

@[simp] theorem coneOperator_mul (S T : AdjointableMap B E E) :
    coneOperator (S * T) = coneOperator S * coneOperator T :=
  coneOperator_comp S T

@[simp] theorem coneOperator_star (T : AdjointableMap B E E) :
    coneOperator (star T) = star (coneOperator T) :=
  coneOperator_adjoint T

/-- The constant-operator restriction is an actual unital complex star
algebra homomorphism, so polynomial and adjoint defects descend exactly. -/
def coneOperatorHom : AdjointableMap B E E →⋆ₐ[ℂ]
    AdjointableMap C(unitInterval, B) (ConeHilbertModule B E) (ConeHilbertModule B E) where
  toFun := coneOperator
  map_zero' := coneOperator_zero
  map_one' := coneOperator_one
  map_add' := coneOperator_add
  map_mul' := coneOperator_mul
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, coneOperator_smul, coneOperator_one]
  map_star' := coneOperator_star

@[simp] theorem coneOperator_sub (S T : AdjointableMap B E E) :
    coneOperator (S - T) = coneOperator S - coneOperator T :=
  coneOperatorHom.map_sub S T

theorem coneOperator_norm_le (T : AdjointableMap B E F) : ‖coneOperator T‖ ≤ ‖T‖ :=
  (coneOperator T).toCLM.opNorm_le_bound (_root_.norm_nonneg _) (fun x =>
    (ContinuousMap.norm_le _
      (mul_nonneg (_root_.norm_nonneg _) (_root_.norm_nonneg _))).mpr (fun t =>
        (AdjointableMap.norm_apply_le T (x.1 t)).trans
          (mul_le_mul_of_nonneg_left (x.1.norm_coe_le_norm t) (_root_.norm_nonneg _))))

/-- A complex linear isometric equivalence acts pointwise on cone sections,
preserving the actual supremum norm. -/
def coneIsometryEquiv (e : E ≃ₗᵢ[ℂ] F) :
    ConeHilbertModule B E ≃ₗᵢ[ℂ] ConeHilbertModule B F where
  toLinearEquiv :=
    { toFun := fun x => ⟨⟨fun t => e (x.1 t), e.continuous.comp x.1.continuous⟩,
        by change e (x.1 0) = 0; rw [ConeHilbertModule.apply_zero, map_zero]⟩
      invFun := fun y => ⟨⟨fun t => e.symm (y.1 t), e.symm.continuous.comp y.1.continuous⟩,
        by change e.symm (y.1 0) = 0; rw [ConeHilbertModule.apply_zero, map_zero]⟩
      left_inv := fun x => by apply Subtype.ext; ext t; exact e.symm_apply_apply _
      right_inv := fun y => by apply Subtype.ext; ext t; exact e.apply_symm_apply _
      map_add' := fun x y => by apply Subtype.ext; ext t; exact e.map_add _ _
      map_smul' := fun c x => by apply Subtype.ext; ext t; exact e.map_smul _ _ }
  norm_map' x := by
    change ‖(⟨fun t => e (x.1 t), e.continuous.comp x.1.continuous⟩ :
      C(unitInterval, F))‖ = ‖x.1‖
    simp only [ContinuousMap.norm_eq_iSup_norm]
    congr 1
    funext t
    exact e.norm_map (x.1 t)

omit [PartialOrder B] [StarOrderedRing B] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] in
@[simp] theorem coneIsometryEquiv_apply (e : E ≃ₗᵢ[ℂ] F)
    (x : ConeHilbertModule B E) (t : unitInterval) :
    (coneIsometryEquiv (B := B) e x).1 t = e (x.1 t) := rfl

end BC4lean.KKTheory
