import BC4lean.CompactModuleOperator
import BC4lean.CountablyGeneratedModule
import BC4lean.ContinuousMapFiniteApproximation
import BC4lean.HilbertModuleEquiv
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Topology.ContinuousMap.StarOrdered
import Mathlib.Topology.Path

/-! # Continuous sections of a Hilbert C⋆-module

For a compact parameter space `X`, `C(X,E)` is a right Hilbert `C(X,B)`-module
with the existing supremum norm and the pointwise coefficient action and
inner product. Its supremum norm is complete whenever `E` is complete. The coefficient algebra carries its pointwise positive order.
Norm-continuous paths of adjointable maps act on sections pointwise.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace
open CStarModule

variable {B E F G X : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [StarOrderedRing B] [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]

/-- The positive square root in a C⋆-algebra gives the continuity structure
needed for the pointwise positive order on continuous coefficient functions. -/
instance (priority := 90) continuousSqrtCStarAlgebra : ContinuousSqrt B where
  sqrt p := CFC.sqrt (p.2 - p.1)
  continuousOn_sqrt := CFC.continuousOn_sqrt.comp
    (continuous_snd.sub continuous_fst).continuousOn
    (fun p hp => sub_nonneg.mpr hp)
  sqrt_nonneg p _ := CFC.sqrt_nonneg _
  sqrt_mul_sqrt p hp := by
    rw [CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr hp)]
    abel

omit [StarOrderedRing B] in
/-- Complex scalars commute with the right coefficient action. -/
theorem module_smul_complex (a : Bᵐᵒᵖ) (c : ℂ) (x : E) :
    a • (c • x) = c • (a • x) := by
  apply module_inner_ext_right (B := B)
  intro y
  simp only [inner_op_smul_right, inner_smul_right_complex, mul_smul_comm]

/-- The coefficient action is jointly continuous, as follows from its
Hilbert-module norm bound rather than an additional continuity assumption. -/
def moduleActionContinuousLinearMap : Bᵐᵒᵖ →L[ℂ] E →L[ℂ] E :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ (fun a x => a • x)
      (fun a b x => module_add_smul a b x)
      (fun c a x => module_complex_smul c a x)
      (fun a x y => module_smul_add a x y)
      (fun c a x => module_smul_complex a c x))
    1 (fun a x => by simpa using module_norm_smul_le a x)

omit [StarOrderedRing B] in
@[simp] theorem moduleActionContinuousLinearMap_apply (a : Bᵐᵒᵖ) (x : E) :
    moduleActionContinuousLinearMap a x = a • x := rfl

omit [StarOrderedRing B] in
theorem continuous_module_action : Continuous (fun p : Bᵐᵒᵖ × E => p.1 • p.2) := by
  change Continuous (fun p : Bᵐᵒᵖ × E => moduleActionContinuousLinearMap p.1 p.2)
  fun_prop

/-- The actual pointwise right action of the continuous coefficient algebra. -/
instance continuousSectionSMul : SMul C(X, B)ᵐᵒᵖ C(X, E) where
  smul b x := ⟨fun t => MulOpposite.op (MulOpposite.unop b t) • x t,
    continuous_module_action.comp
      ((MulOpposite.continuous_op.comp (MulOpposite.unop b).continuous).prodMk x.continuous)⟩

omit [StarOrderedRing B] [CompactSpace X] in
@[simp] theorem continuousSection_smul_apply (b : C(X, B)ᵐᵒᵖ) (x : C(X, E)) (t : X) :
    (b • x) t = MulOpposite.op (MulOpposite.unop b t) • x t := rfl

/-- The pointwise coefficient-valued inner product of continuous sections. -/
def continuousSectionInner (x y : C(X, E)) : C(X, B)ᵐᵒᵖ :=
  MulOpposite.op ⟨fun t => MulOpposite.unop ⟪x t, y t⟫_(Bᵐᵒᵖ),
    MulOpposite.continuous_unop.comp
      (CStarModule.continuous_inner.comp (x.continuous.prodMk y.continuous))⟩

omit [CompactSpace X] in
@[simp] theorem continuousSectionInner_apply (x y : C(X, E)) (t : X) :
    MulOpposite.unop (continuousSectionInner x y) t =
      MulOpposite.unop ⟪x t, y t⟫_(Bᵐᵒᵖ) := rfl

theorem continuousSection_norm_eq_sqrt_inner (x : C(X, E)) :
    ‖x‖ = Real.sqrt ‖continuousSectionInner (B := B) x x‖ := by
  have hu : ‖continuousSectionInner (B := B) x x‖ ≤ ‖x‖ ^ 2 := by
    change ‖MulOpposite.unop (continuousSectionInner (B := B) x x)‖ ≤ ‖x‖ ^ 2
    apply (ContinuousMap.norm_le _ (sq_nonneg _)).mpr
    intro t
    change ‖⟪x t, x t⟫_(Bᵐᵒᵖ)‖ ≤ ‖x‖ ^ 2
    rw [← CStarModule.norm_sq_eq (Bᵐᵒᵖ)]
    exact pow_le_pow_left₀ (_root_.norm_nonneg _) (x.norm_coe_le_norm t) 2
  have hl : ‖x‖ ≤ Real.sqrt ‖continuousSectionInner (B := B) x x‖ := by
    apply (ContinuousMap.norm_le _ (Real.sqrt_nonneg _)).mpr
    intro t
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ)]
    apply Real.sqrt_le_sqrt
    exact (MulOpposite.unop (continuousSectionInner (B := B) x x)).norm_coe_le_norm t
  exact le_antisymm hl ((Real.sqrt_le_sqrt hu).trans_eq (Real.sqrt_sq (_root_.norm_nonneg _)))

/-- Continuous sections form a Hilbert module with their existing supremum
norm. Completeness is inherited from `ContinuousMap` when `E` is complete. -/
instance continuousSectionCStarModule : CStarModule C(X, B)ᵐᵒᵖ C(X, E) where
  inner := continuousSectionInner
  inner_add_right := by
    intro x y z
    apply MulOpposite.unop_injective
    ext t
    exact congrArg MulOpposite.unop (CStarModule.inner_add_right (x := x t) (y := y t) (z := z t))
  inner_self_nonneg := by
    intro x
    change ∀ t, 0 ≤ MulOpposite.unop ⟪x t, x t⟫_(Bᵐᵒᵖ)
    intro t
    exact CStarModule.inner_self_nonneg (A := Bᵐᵒᵖ) (x := x t)
  inner_self := by
    intro x
    constructor
    · intro h
      ext t
      apply (CStarModule.inner_self (A := Bᵐᵒᵖ)).mp
      exact congrArg (fun b : C(X, B)ᵐᵒᵖ => MulOpposite.op (MulOpposite.unop b t)) h
    · intro h
      subst x
      apply MulOpposite.unop_injective
      ext t
      simp [continuousSectionInner]
  inner_op_smul_right := by
    intro b x y
    apply MulOpposite.unop_injective
    ext t
    exact congrArg MulOpposite.unop (CStarModule.inner_op_smul_right
      (a := MulOpposite.op (MulOpposite.unop b t)) (x := x t) (y := y t))
  inner_smul_right_complex := by
    intro c x y
    apply MulOpposite.unop_injective
    ext t
    exact congrArg MulOpposite.unop (CStarModule.inner_smul_right_complex
      (z := c) (x := x t) (y := y t))
  star_inner x y := by
    apply MulOpposite.unop_injective
    ext t
    exact congrArg MulOpposite.unop (CStarModule.star_inner (x t) (y t))
  norm_eq_sqrt_norm_inner_self := continuousSection_norm_eq_sqrt_inner (B := B)

@[simp] theorem continuousSection_inner_apply (x y : C(X, E)) (t : X) :
    MulOpposite.unop ⟪x, y⟫_(C(X, B)ᵐᵒᵖ) t =
      MulOpposite.unop ⟪x t, y t⟫_(Bᵐᵒᵖ) := rfl

/-- Sections over the closed unit interval, with the preceding actual module
and supremum norm instances. -/
abbrev IntervalHilbertModule (B E : Type*) [NonUnitalCStarAlgebra B]
    [TopologicalSpace E] := C(unitInterval, E)

/-- A norm-continuous field of adjointable maps acts continuously on sections. -/
def continuousSectionOperatorApply (T : C(X, AdjointableMap B E F))
    (x : C(X, E)) : C(X, F) :=
  ⟨fun t => T t (x t), by
    have hT := AdjointableMap.toCLMContinuousLinearMap.continuous.comp T.continuous
    exact hT.clm_apply x.continuous⟩

omit [StarOrderedRing B] [CompactSpace X] in
@[simp] theorem continuousSectionOperatorApply_apply
    (T : C(X, AdjointableMap B E F)) (x : C(X, E)) (t : X) :
    continuousSectionOperatorApply T x t = T t (x t) := rfl

omit [StarOrderedRing B] in
/-- The section action is bounded by the supremum of the operator norms. -/
theorem continuousSectionOperatorApply_norm_le
    (T : C(X, AdjointableMap B E F)) (x : C(X, E)) :
    ‖continuousSectionOperatorApply T x‖ ≤ ‖T‖ * ‖x‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (_root_.norm_nonneg _) (_root_.norm_nonneg _))).mpr
  intro t
  exact (AdjointableMap.norm_apply_le (T t) (x t)).trans
    (mul_le_mul (T.norm_coe_le_norm t) (x.norm_coe_le_norm t)
      (_root_.norm_nonneg _) (_root_.norm_nonneg _))

/-- The bounded complex-linear map induced by an operator field. -/
def continuousSectionOperatorCLM (T : C(X, AdjointableMap B E F)) : C(X, E) →L[ℂ] C(X, F) :=
  LinearMap.mkContinuous
    { toFun := continuousSectionOperatorApply T
      map_add' := fun x y => by ext t; exact (T t).toCLM.map_add (x t) (y t)
      map_smul' := fun c x => by ext t; exact (T t).toCLM.map_smul c (x t) }
    ‖T‖ (continuousSectionOperatorApply_norm_le T)

/-- Pointwise adjointability gives genuine adjointability over `C(X,B)`. -/
def continuousSectionOperator (T : C(X, AdjointableMap B E F)) :
    AdjointableMap C(X, B) C(X, E) C(X, F) where
  toCLM := continuousSectionOperatorCLM T
  adjointCLM := continuousSectionOperatorCLM
    ⟨fun t => (T t).adjoint,
      AdjointableMap.adjointContinuousLinearMap.continuous.comp T.continuous⟩
  adjoint_identity x y := by
    apply MulOpposite.unop_injective
    ext t
    exact congrArg MulOpposite.unop ((T t).adjoint_identity (x t) (y t))

@[simp] theorem continuousSectionOperator_apply
    (T : C(X, AdjointableMap B E F)) (x : C(X, E)) (t : X) :
    continuousSectionOperator T x t = T t (x t) := rfl

theorem continuousSectionOperator_norm_le (T : C(X, AdjointableMap B E F)) :
    ‖continuousSectionOperator T‖ ≤ ‖T‖ := by
  exact (continuousSectionOperator T).toCLM.opNorm_le_bound (_root_.norm_nonneg _)
    (continuousSectionOperatorApply_norm_le T)

@[simp] theorem continuousSectionOperator_zero :
    continuousSectionOperator (0 : C(X, AdjointableMap B E F)) = 0 := by ext x t; rfl

@[simp] theorem continuousSectionOperator_add (S T : C(X, AdjointableMap B E F)) :
    continuousSectionOperator (S + T) = continuousSectionOperator S + continuousSectionOperator T := by
  ext x t
  rfl

@[simp] theorem continuousSectionOperator_smul (c : ℂ) (T : C(X, AdjointableMap B E F)) :
    continuousSectionOperator (c • T) = c • continuousSectionOperator T := by ext x t; rfl

@[simp] theorem continuousSectionOperator_sub (S T : C(X, AdjointableMap B E F)) :
    continuousSectionOperator (S - T) = continuousSectionOperator S - continuousSectionOperator T := by
  ext x t
  rfl

/-- The operator-field construction itself is continuous and complex-linear. -/
def continuousSectionOperatorMap :
    C(X, AdjointableMap B E F) →L[ℂ] AdjointableMap C(X, B) C(X, E) C(X, F) :=
  LinearMap.mkContinuous
    { toFun := continuousSectionOperator
      map_add' := continuousSectionOperator_add
      map_smul' := continuousSectionOperator_smul }
    1 (fun T => by simpa using continuousSectionOperator_norm_le T)

/-- Weight a constant section by a continuous real scalar function. -/
def continuousSectionWeightLinearMap (ρ : C(X, ℝ)) : E →ₗ[ℂ] C(X, E) where
  toFun x := ρ • ContinuousMap.const X x
  map_add' x y := by ext t; exact smul_add (ρ t) x y
  map_smul' c x := by ext t; exact smul_comm (ρ t) c x

omit [CompactSpace X] in
@[simp] theorem continuousSectionWeightLinearMap_apply (ρ : C(X, ℝ)) (x : E) (t : X) :
    continuousSectionWeightLinearMap ρ x t = ρ t • x := rfl

/-- A continuously weighted constant rank-one field is an actual rank-one
module operator on the section module. -/
theorem continuousSectionOperator_weighted_rankOne (ρ : C(X, ℝ)) (x : F) (y : E) :
    continuousSectionOperator (ρ • ContinuousMap.const X (moduleRankOne (B := B) x y)) =
      moduleRankOne (continuousSectionWeightLinearMap ρ x) (ContinuousMap.const X y) := by
  ext z t
  change ρ t • (⟪y, z t⟫_(Bᵐᵒᵖ) • x) =
    ⟪y, z t⟫_(Bᵐᵒᵖ) • (ρ t • x)
  rw [← algebraMap_smul ℂ (ρ t) x,
    module_smul_complex, algebraMap_smul]

/-- Weighting a constant finite-rank operator preserves genuine module
finite rank over the continuous coefficient algebra. -/
theorem continuousSectionOperator_weighted_finiteRank (ρ : C(X, ℝ))
    {T : AdjointableMap B E F} (hT : T ∈ moduleFiniteRank B E F) :
    continuousSectionOperator (ρ • ContinuousMap.const X T) ∈
      moduleFiniteRank C(X, B) C(X, E) C(X, F) := by
  let L : AdjointableMap B E F →ₗ[ℂ]
      AdjointableMap C(X, B) C(X, E) C(X, F) :=
    { toFun := fun T => continuousSectionOperator (ρ • ContinuousMap.const X T)
      map_add' := fun S T => by ext z t; exact smul_add (ρ t) (S (z t)) (T (z t))
      map_smul' := fun c T => by ext z t; exact smul_comm (ρ t) c (T (z t)) }
  change L T ∈ _
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨⟨x, y⟩, rfl⟩ := hT
    change continuousSectionOperator (ρ • ContinuousMap.const X (moduleRankOne x y)) ∈ _
    rw [continuousSectionOperator_weighted_rankOne]
    exact Submodule.subset_span ⟨(_, _), rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add S T _ _ hS hT => rw [map_add]; exact Submodule.add_mem _ hS hT
  | smul c T _ hT => rw [map_smul]; exact Submodule.smul_mem _ c hT

/-- Norm-continuous fields of compact module maps give compact section
operators. The proof uses uniform finite partition approximation, not merely
pointwise compactness. -/
theorem continuousSectionOperator_isModuleCompact [T2Space X]
    (T : C(X, AdjointableMap B E F)) (hT : ∀ t, IsModuleCompact (T t)) :
    IsModuleCompact (continuousSectionOperator T) := by
  classical
  apply (mem_moduleCompact_iff_approx _).mpr
  intro ε hε
  obtain ⟨s, ρ, q, _, _, hq, herr⟩ := exists_finite_partition_approximation T
    (moduleFiniteRank B E F : Set (AdjointableMap B E F)) hT ε hε
  refine ⟨continuousSectionOperator (finitePartitionCombination s ρ q), ?_, ?_⟩
  · change continuousSectionOperatorMap (finitePartitionCombination s ρ q) ∈ _
    rw [finitePartitionCombination, map_sum]
    exact Submodule.sum_mem _ (fun j _ => continuousSectionOperator_weighted_finiteRank
      (ρ j) (hq j))
  · rw [← continuousSectionOperator_sub]
    exact (continuousSectionOperator_norm_le _).trans_lt herr

/-- Constant sections of a generating sequence generate densely over the
continuous coefficient algebra, including when the coefficients are nonunital. -/
theorem continuousSection_isCountablyGenerated [T2Space X]
    (hE : IsCountablyGeneratedModule B E) : IsCountablyGeneratedModule C(X, B) C(X, E) := by
  classical
  obtain ⟨ξ, hξ⟩ := hE
  let η : ℕ → C(X, E) := fun n => ContinuousMap.const X (ξ n)
  have hweight : ∀ (ρ : C(X, ℝ)) x, x ∈ moduleGeneratingSpan (B := B) ξ →
      continuousSectionWeightLinearMap ρ x ∈ moduleGeneratingSpan (B := C(X, B)) η := by
    intro ρ x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, b, rfl⟩ := hx
      let a : C(X, B)ᵐᵒᵖ := MulOpposite.op
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
  refine ⟨η, ?_⟩
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

/-- Evaluation is a contractive complex-linear map on the section module. -/
def continuousSectionEvaluation (t : X) : C(X, E) →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := fun x => x t
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun x => by simpa using x.norm_coe_le_norm t)

@[simp] theorem continuousSectionEvaluation_apply (t : X) (x : C(X, E)) :
    continuousSectionEvaluation t x = x t := rfl

theorem continuousSectionEvaluation_surjective (t : X) :
    Function.Surjective (continuousSectionEvaluation (E := E) t) :=
  fun x => ⟨ContinuousMap.const X x, rfl⟩

/-- The canonical fibre is the actual quotient by the null space of the
evaluated inner product; this null space equals the kernel of evaluation. -/
abbrev ContinuousSectionFibre (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (t : X) := C(X, E) ⧸ (continuousSectionEvaluation (E := E) t).ker

instance continuousSectionEvaluation_isClosed_ker (t : X) :
    IsClosed ((continuousSectionEvaluation (E := E) t).ker : Set C(X, E)) :=
  (continuousSectionEvaluation t).isClosed_ker

set_option maxHeartbeats 800000 in
/-- The algebraic evaluation quotient is exactly the original vector space. -/
def continuousSectionFibreLinearEquiv (t : X) : ContinuousSectionFibre E t ≃ₗ[ℂ] E :=
  (continuousSectionEvaluation (E := E) t).toLinearMap.quotKerEquivOfSurjective
    (continuousSectionEvaluation_surjective (E := E) t)

@[simp] theorem continuousSectionFibreLinearEquiv_mk (t : X) (x : C(X, E)) :
    continuousSectionFibreLinearEquiv t (Submodule.Quotient.mk x) = x t :=
  LinearMap.quotKerEquivOfSurjective_apply_mk
    (continuousSectionEvaluation (E := E) t).toLinearMap
    (continuousSectionEvaluation_surjective (E := E) t) x

/-- The existing quotient norm is exactly the norm of the evaluation. This is
proved using its actual infimum norm and the contractive constant-section lift. -/
theorem continuousSectionFibreLinearEquiv_norm (t : X) (q : ContinuousSectionFibre E t) :
    ‖continuousSectionFibreLinearEquiv t q‖ = ‖q‖ := by
  let e := continuousSectionFibreLinearEquiv (E := E) t
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨x, hx, hnorm⟩ := Submodule.Quotient.norm_mk_lt q hε
    have he : e q = x t := by rw [← hx]; exact continuousSectionFibreLinearEquiv_mk t x
    rw [he]
    exact (x.norm_coe_le_norm t).trans hnorm.le
  · have hq : (Submodule.Quotient.mk (ContinuousMap.const X (e q)) : ContinuousSectionFibre E t) = q := by
      apply e.injective
      exact continuousSectionFibreLinearEquiv_mk t _
    calc
      ‖q‖ = ‖(Submodule.Quotient.mk (ContinuousMap.const X (e q)) : ContinuousSectionFibre E t)‖ :=
        congrArg norm hq.symm
      _ ≤ ‖ContinuousMap.const X (e q)‖ := Submodule.Quotient.norm_mk_le _ _
      _ ≤ ‖e q‖ := (ContinuousMap.norm_le _ (_root_.norm_nonneg _)).mpr (fun _ => le_rfl)

/-- Evaluation gives a genuine complex-linear isometric equivalence between
the actual quotient fibre and the original module. -/
def continuousSectionFibreIsometryEquiv (t : X) : ContinuousSectionFibre E t ≃ₗᵢ[ℂ] E where
  toLinearEquiv := continuousSectionFibreLinearEquiv t
  norm_map' := continuousSectionFibreLinearEquiv_norm t

@[simp] theorem continuousSectionFibreIsometryEquiv_mk (t : X) (x : C(X, E)) :
    continuousSectionFibreIsometryEquiv t (Submodule.Quotient.mk x) = x t :=
  continuousSectionFibreLinearEquiv_mk t x

/-- The fibre coefficient action is the actual evaluated `B` action, transported
through the proved quotient isometry. -/
instance continuousSectionFibreSMul (t : X) : SMul Bᵐᵒᵖ (ContinuousSectionFibre E t) where
  smul a q := (continuousSectionFibreIsometryEquiv t).symm
    (a • continuousSectionFibreIsometryEquiv t q)

/-- The quotient fibre has its evaluated coefficient inner product and existing
quotient norm, rather than an assumed Hilbert-module structure. -/
instance continuousSectionFibreCStarModule (t : X) : CStarModule Bᵐᵒᵖ (ContinuousSectionFibre E t) where
  inner x y := ⟪continuousSectionFibreIsometryEquiv t x,
    continuousSectionFibreIsometryEquiv t y⟫_(Bᵐᵒᵖ)
  inner_add_right := by intro x y z; rw [map_add, CStarModule.inner_add_right]
  inner_self_nonneg := CStarModule.inner_self_nonneg
  inner_self := by
    intro x
    rw [CStarModule.inner_self]
    exact (continuousSectionFibreIsometryEquiv t).map_eq_zero_iff
  inner_op_smul_right := by
    intro a x y
    change ⟪_, continuousSectionFibreIsometryEquiv t
      ((continuousSectionFibreIsometryEquiv t).symm (a • continuousSectionFibreIsometryEquiv t y))⟫_(Bᵐᵒᵖ) = _
    rw [LinearIsometryEquiv.apply_symm_apply, CStarModule.inner_op_smul_right]
  inner_smul_right_complex := by intro c x y; rw [map_smul, CStarModule.inner_smul_right_complex]
  star_inner x y := CStarModule.star_inner _ _
  norm_eq_sqrt_norm_inner_self x := by
    rw [← (continuousSectionFibreIsometryEquiv t).norm_map x]
    exact CStarModule.norm_eq_sqrt_norm_inner_self _

/-- The quotient evaluation is a unitary Hilbert-module equivalence. -/
def continuousSectionFibreModuleEquiv (t : X) : HilbertModuleEquiv B (ContinuousSectionFibre E t) E where
  linearIsometryEquiv := continuousSectionFibreIsometryEquiv t
  inner_map _ _ := rfl

/-- Evaluation of section inner products is precisely the quotient-fibre
inner product on representatives. -/
@[simp] theorem continuousSectionFibre_inner_mk (t : X) (x y : C(X, E)) :
    ⟪(Submodule.Quotient.mk x : ContinuousSectionFibre E t), Submodule.Quotient.mk y⟫_(Bᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪x, y⟫_(C(X, B)ᵐᵒᵖ) t) := by
  change ⟪continuousSectionFibreIsometryEquiv t _, continuousSectionFibreIsometryEquiv t _⟫_(Bᵐᵒᵖ) = _
  rw [continuousSectionFibreIsometryEquiv_mk, continuousSectionFibreIsometryEquiv_mk]
  rfl

@[simp] theorem continuousSectionFibre_norm_mk (t : X) (x : C(X, E)) :
    ‖(Submodule.Quotient.mk x : ContinuousSectionFibre E t)‖ = ‖x t‖ := by
  rw [← (continuousSectionFibreIsometryEquiv t).norm_map, continuousSectionFibreIsometryEquiv_mk]

omit [StarOrderedRing B] in
/-- The transported fibre action agrees with evaluation of section coefficients
on representatives; in particular every evaluation-kernel coefficient acts by zero. -/
theorem continuousSectionFibre_smul_mk (t : X) (b : C(X, B)ᵐᵒᵖ) (x : C(X, E)) :
    MulOpposite.op (MulOpposite.unop b t) •
      (Submodule.Quotient.mk x : ContinuousSectionFibre E t) = Submodule.Quotient.mk (b • x) := by
  apply (continuousSectionFibreIsometryEquiv t).injective
  change continuousSectionFibreIsometryEquiv t
    ((continuousSectionFibreIsometryEquiv t).symm _) = _
  rw [LinearIsometryEquiv.apply_symm_apply, continuousSectionFibreIsometryEquiv_mk,
    continuousSectionFibreIsometryEquiv_mk]
  rfl

end BC4lean.KKTheory
