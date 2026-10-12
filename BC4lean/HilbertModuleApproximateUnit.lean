import BC4lean.HilbertModuleCoefficientApproximateUnit
import BC4lean.AdjointableAlgebra
import BC4lean.ProjectionHilbertModule
import BC4lean.HilbertModuleSum

/-! # Nonunital coefficient action and actual coordinate projections

The shared approximate-unit theorem proves strong convergence of the actual
coefficient action from the coefficient inner product, with no essentiality
hypothesis. Here fixed-vector coefficient action is bounded and linear. For
a complete module over `B × B`, the two coordinate actions of the canonical
positive contractive approximate unit have actual limits. The limits are
complementary selfadjoint adjointable projections. No elements `(1,0)` or
`(0,1)` are introduced into a nonunital coefficient algebra.

The coefficient filter is the genuine canonical approximate-unit filter on
`(B × B)ᵐᵒᵖ`. Its coordinate actions are `(e₁,0)` and `(0,e₂)`. Cauchy
convergence follows from a direct comparison with the convergent full action.
-/

noncomputable section
namespace BC4lean.KKTheory

open Filter
open scoped Topology InnerProductSpace

section CoefficientVector

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

/-- The genuine coefficient action on a fixed vector, as a bounded complex
linear map. Its bound is derived from the Hilbert-module inner product. -/
def moduleCoefficientVectorCLM (x : E) : Bᵐᵒᵖ →L[ℂ] E :=
  ({ toFun := fun a => a • x
     map_add' := fun a b => module_add_smul a b x
     map_smul' := fun c a => module_complex_smul c a x } : Bᵐᵒᵖ →ₗ[ℂ] E).mkContinuous
    ‖x‖ (fun a => by
      change ‖a • x‖ ≤ ‖x‖ * ‖a‖
      simpa only [mul_comm] using module_norm_smul_le a x)

@[simp] theorem moduleCoefficientVectorCLM_apply (x : E) (a : Bᵐᵒᵖ) :
    moduleCoefficientVectorCLM x a = a • x := rfl

/-- All vectors lie in the closure of actual coefficient multiples. This
nondegeneracy is a theorem of the Hilbert-module laws, including for nonunital B. -/
theorem moduleCoefficient_span_dense [StarOrderedRing B] :
    Dense ((Submodule.span ℂ (Set.range fun p : Bᵐᵒᵖ × E => p.1 • p.2)) : Set E) := by
  apply (dense_iff_closure_eq).mpr
  apply Set.eq_univ_of_forall
  intro x
  have hx : Tendsto (fun a : Bᵐᵒᵖ => a • x)
      (CStarAlgebra.approximateUnit Bᵐᵒᵖ) (𝓝 x) := tendsto_coefficient_approximateUnit_smul x
  exact isClosed_closure.mem_of_tendsto hx (Eventually.of_forall fun a =>
    subset_closure (Submodule.subset_span ⟨(a, x), rfl⟩))

end CoefficientVector

section ProductCoefficient

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul (B × B)ᵐᵒᵖ E]
  [CStarModule (B × B)ᵐᵒᵖ E] [CompleteSpace E]

/-- Select the first (`true`) or second (`false`) actual coefficient component. -/
def coordinateCoefficient (k : Bool) (a : (B × B)ᵐᵒᵖ) : (B × B)ᵐᵒᵖ :=
  if k then MulOpposite.op ((MulOpposite.unop a).1, 0)
  else MulOpposite.op (0, (MulOpposite.unop a).2)

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem coordinateCoefficient_zero (k : Bool) :
    coordinateCoefficient (B := B) k 0 = 0 := by cases k <;> rfl

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem coordinateCoefficient_add (k : Bool) (a b : (B × B)ᵐᵒᵖ) :
    coordinateCoefficient k (a + b) = coordinateCoefficient k a + coordinateCoefficient k b := by
  cases k <;> apply MulOpposite.unop_injective <;> ext <;> simp [coordinateCoefficient]

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem coordinateCoefficient_smul (k : Bool) (c : ℂ) (a : (B × B)ᵐᵒᵖ) :
    coordinateCoefficient k (c • a) = c • coordinateCoefficient k a := by
  cases k <;> apply MulOpposite.unop_injective <;> ext <;> simp [coordinateCoefficient]

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem coordinateCoefficient_star (k : Bool) (a : (B × B)ᵐᵒᵖ) :
    coordinateCoefficient k (star a) = star (coordinateCoefficient k a) := by
  cases k <;> apply MulOpposite.unop_injective <;> ext <;> simp [coordinateCoefficient]

omit [PartialOrder B] [StarOrderedRing B] in
theorem coordinateCoefficient_mul_left (k : Bool) (a b : (B × B)ᵐᵒᵖ) :
    coordinateCoefficient k (a * b) = coordinateCoefficient k a * b := by
  cases k <;> apply MulOpposite.unop_injective <;> ext <;> simp [coordinateCoefficient]

omit [PartialOrder B] [StarOrderedRing B] in
theorem coordinateCoefficient_mul_right (k : Bool) (a b : (B × B)ᵐᵒᵖ) :
    coordinateCoefficient k (a * b) = a * coordinateCoefficient k b := by
  cases k <;> apply MulOpposite.unop_injective <;> ext <;> simp [coordinateCoefficient]

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem coordinateCoefficient_idempotent (k : Bool) (a : (B × B)ᵐᵒᵖ) :
    coordinateCoefficient k (coordinateCoefficient k a) = coordinateCoefficient k a := by
  cases k <;> rfl

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem coordinateCoefficient_complement (k : Bool) (a : (B × B)ᵐᵒᵖ) :
    coordinateCoefficient k (coordinateCoefficient (!k) a) = 0 := by cases k <;> rfl

omit [PartialOrder B] [StarOrderedRing B] in
theorem coordinateCoefficient_add_complement (k : Bool) (a : (B × B)ᵐᵒᵖ) :
    coordinateCoefficient k a + coordinateCoefficient (!k) a = a := by
  cases k <;> apply MulOpposite.unop_injective <;> ext <;> simp [coordinateCoefficient]

omit [PartialOrder B] [StarOrderedRing B] in
theorem coordinateCoefficient_norm_le (k : Bool) (a : (B × B)ᵐᵒᵖ) :
    ‖coordinateCoefficient k a‖ ≤ ‖a‖ := by
  rw [← MulOpposite.norm_unop (coordinateCoefficient k a), ← MulOpposite.norm_unop a]
  cases k <;> simp [coordinateCoefficient, Prod.norm_def]


/-- The coordinate selector is a genuine bounded coefficient-linear map. -/
def coordinateCoefficientCLM (k : Bool) : (B × B)ᵐᵒᵖ →L[ℂ] (B × B)ᵐᵒᵖ :=
  ({ toFun := coordinateCoefficient k
     map_add' := coordinateCoefficient_add k
     map_smul' := coordinateCoefficient_smul k } : (B × B)ᵐᵒᵖ →ₗ[ℂ] (B × B)ᵐᵒᵖ).mkContinuous
    1 (fun a => by
      change ‖coordinateCoefficient k a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using coordinateCoefficient_norm_le k a)

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem coordinateCoefficientCLM_apply (k : Bool) (a : (B × B)ᵐᵒᵖ) :
    coordinateCoefficientCLM k a = coordinateCoefficient k a := rfl

omit [StarOrderedRing B] [CompleteSpace E] in
/-- A coordinate action is bounded by the full action on the same vector.
This is the product coefficient inner norm, not an assumed projection. -/
theorem coordinateCoefficient_smul_norm_le (k : Bool) (a : (B × B)ᵐᵒᵖ) (x : E) :
    ‖coordinateCoefficient k a • x‖ ≤ ‖a • x‖ := by
  have hn (b : (B × B)ᵐᵒᵖ) :
      ‖b • x‖ ^ 2 = ‖star (MulOpposite.unop b) *
        (MulOpposite.unop ⟪x, x⟫_((B × B)ᵐᵒᵖ) * MulOpposite.unop b)‖ := by
    rw [CStarModule.norm_sq_eq ((B × B)ᵐᵒᵖ), CStarModule.inner_op_smul_left,
      CStarModule.inner_op_smul_right]
    rw [← MulOpposite.norm_unop]
    rfl
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by decide : 2 ≠ 0)).mp
  rw [hn, hn]
  cases k <;> simp [coordinateCoefficient, Prod.norm_def]

omit [StarOrderedRing B] [CompleteSpace E] in
theorem coordinateCoefficient_smul_dist_le (k : Bool) (a b : (B × B)ᵐᵒᵖ) (x : E) :
    dist (coordinateCoefficient k a • x) (coordinateCoefficient k b • x) ≤
      dist (a • x) (b • x) := by
  have h := coordinateCoefficient_smul_norm_le k (a - b) x
  change ‖moduleCoefficientVectorCLM x (coordinateCoefficientCLM k (a - b))‖ ≤
    ‖moduleCoefficientVectorCLM x (a - b)‖ at h
  simpa only [map_sub, moduleCoefficientVectorCLM_apply, coordinateCoefficientCLM_apply,
    dist_eq_norm] using h

omit [CompleteSpace E] in
/-- Coordinate actions are Cauchy because their distances are bounded by
those of the actual strongly convergent full approximate-unit action. -/
theorem coordinateCoefficient_smul_cauchy (k : Bool) (x : E) :
    Cauchy (Filter.map (fun a : (B × B)ᵐᵒᵖ => coordinateCoefficient k a • x)
      (CStarAlgebra.approximateUnit (B × B)ᵐᵒᵖ)) := by
  let l := CStarAlgebra.approximateUnit (B × B)ᵐᵒᵖ
  have hfull : Cauchy (Filter.map (fun a : (B × B)ᵐᵒᵖ => a • x) l) :=
    (tendsto_coefficient_approximateUnit_smul x).cauchy_map
  refine Metric.cauchy_iff.mpr ⟨by infer_instance, ?_⟩
  intro ε hε
  obtain ⟨S, hS, hdiam⟩ := (Metric.cauchy_iff.mp hfull).2 ε hε
  let T : Set (B × B)ᵐᵒᵖ := (fun a => a • x) ⁻¹' S
  refine ⟨(fun a : (B × B)ᵐᵒᵖ => coordinateCoefficient k a • x) '' T, ?_, ?_⟩
  · change (fun a : (B × B)ᵐᵒᵖ => coordinateCoefficient k a • x) ⁻¹'
      ((fun a : (B × B)ᵐᵒᵖ => coordinateCoefficient k a • x) '' T) ∈ l
    exact Filter.mem_of_superset hS (fun a ha => ⟨a, ha, rfl⟩)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact (coordinateCoefficient_smul_dist_le k a b x).trans_lt (hdiam _ ha _ hb)

/-- The coordinate action has a genuine limit in the complete module. -/
theorem exists_coordinateCoefficient_smul_limit (k : Bool) (x : E) :
    ∃ y : E, Tendsto (fun a : (B × B)ᵐᵒᵖ => coordinateCoefficient k a • x)
      (CStarAlgebra.approximateUnit (B × B)ᵐᵒᵖ) (𝓝 y) :=
  cauchy_map_iff_exists_tendsto.mp (coordinateCoefficient_smul_cauchy k x)

/-- The actual coordinate limit, selected only after proving existence. -/
def coordinateModuleProjection (k : Bool) (x : E) : E :=
  (exists_coordinateCoefficient_smul_limit (B := B) k x).choose

theorem tendsto_coordinateModuleProjection (k : Bool) (x : E) :
    Tendsto (fun a : (B × B)ᵐᵒᵖ => coordinateCoefficient k a • x)
      (CStarAlgebra.approximateUnit (B × B)ᵐᵒᵖ) (𝓝 (coordinateModuleProjection (B := B) k x)) :=
  (exists_coordinateCoefficient_smul_limit (B := B) k x).choose_spec

theorem coordinateModuleProjection_add (k : Bool) (x y : E) :
    coordinateModuleProjection (B := B) k (x + y) = coordinateModuleProjection (B := B) k x + coordinateModuleProjection (B := B) k y := by
  apply tendsto_nhds_unique (tendsto_coordinateModuleProjection (B := B) k (x + y))
  simpa only [module_smul_add] using
    (tendsto_coordinateModuleProjection (B := B) k x).add (tendsto_coordinateModuleProjection (B := B) k y)

theorem coordinateModuleProjection_smul_complex (k : Bool) (c : ℂ) (x : E) :
    coordinateModuleProjection (B := B) k (c • x) = c • coordinateModuleProjection (B := B) k x := by
  apply tendsto_nhds_unique (tendsto_coordinateModuleProjection (B := B) k (c • x))
  have hc : ∀ a : (B × B)ᵐᵒᵖ, coordinateCoefficient k a • (c • x) = c • (coordinateCoefficient k a • x) := by
    intro a
    apply module_inner_ext_right (B := B × B)
    intro y
    simp only [CStarModule.inner_op_smul_right, CStarModule.inner_smul_right_complex,
      mul_smul_comm]
  simpa only [hc] using (tendsto_coordinateModuleProjection (B := B) k x).const_smul c

theorem coordinateModuleProjection_norm_le (k : Bool) (x : E) :
    ‖coordinateModuleProjection (B := B) k x‖ ≤ ‖x‖ :=
  le_of_tendsto_of_tendsto'
    (tendsto_coordinateModuleProjection (B := B) k x).norm
    (tendsto_coefficient_approximateUnit_smul x).norm
    (fun a => coordinateCoefficient_smul_norm_le k a x)

/-- The limit is complex linear and contractive, hence genuinely bounded. -/
def coordinateModuleProjectionCLM (k : Bool) : E →L[ℂ] E :=
  ({ toFun := coordinateModuleProjection (B := B) k
     map_add' := coordinateModuleProjection_add (B := B) k
     map_smul' := coordinateModuleProjection_smul_complex (B := B) k } : E →ₗ[ℂ] E).mkContinuous
    1 (fun x => by
      change ‖coordinateModuleProjection (B := B) k x‖ ≤ 1 * ‖x‖
      simpa only [one_mul] using coordinateModuleProjection_norm_le (B := B) k x)

@[simp] theorem coordinateModuleProjectionCLM_apply (k : Bool) (x : E) :
    coordinateModuleProjectionCLM (B := B) k x = coordinateModuleProjection (B := B) k x := rfl

/-- The first inner variable retains exactly its coefficient component. -/
theorem coordinateModuleProjection_inner_left (k : Bool) (x y : E) :
    ⟪coordinateModuleProjection (B := B) k x, y⟫_((B × B)ᵐᵒᵖ) =
      coordinateCoefficient k ⟪x, y⟫_((B × B)ᵐᵒᵖ) := by
  have hmodule := (CStarModule.continuous_inner (A := (B × B)ᵐᵒᵖ) (E := E)).tendsto
    (coordinateModuleProjection (B := B) k x, y) |>.comp
      ((tendsto_coordinateModuleProjection (B := B) k x).prodMk_nhds
        (tendsto_const_nhds (x := y)))
  have hcoef := (coordinateCoefficientCLM k).continuous.continuousAt.tendsto.comp
    ((CStarAlgebra.increasingApproximateUnit (B × B)ᵐᵒᵖ).tendsto_mul_left
      ⟪x, y⟫_((B × B)ᵐᵒᵖ))
  have hsame : (fun a : (B × B)ᵐᵒᵖ =>
      ⟪coordinateCoefficient k a • x, y⟫_((B × B)ᵐᵒᵖ)) =ᶠ[
        CStarAlgebra.approximateUnit (B × B)ᵐᵒᵖ]
      (fun a => coordinateCoefficient k (⟪x, y⟫_((B × B)ᵐᵒᵖ) * a)) := by
    filter_upwards [(CStarAlgebra.increasingApproximateUnit (B × B)ᵐᵒᵖ).eventually_star_eq]
      with a ha
    rw [CStarModule.inner_op_smul_left, ← coordinateCoefficient_star, ha,
      coordinateCoefficient_mul_right]
  exact tendsto_nhds_unique hmodule (hcoef.congr' hsame.symm)

/-- Hermitian symmetry supplies the same exact component in the second variable. -/
theorem coordinateModuleProjection_inner_right (k : Bool) (x y : E) :
    ⟪x, coordinateModuleProjection (B := B) k y⟫_((B × B)ᵐᵒᵖ) =
      coordinateCoefficient k ⟪x, y⟫_((B × B)ᵐᵒᵖ) := by
  apply star_injective
  rw [CStarModule.star_inner, coordinateModuleProjection_inner_left,
    ← coordinateCoefficient_star, CStarModule.star_inner]

/-- On an actual coefficient multiple the limit selects its component.
This proves the intended central multiplier action without postulating one. -/
theorem coordinateModuleProjection_coefficient_smul (k : Bool)
    (a : (B × B)ᵐᵒᵖ) (x : E) :
    coordinateModuleProjection (B := B) k (a • x) = coordinateCoefficient k a • x := by
  apply module_inner_ext_left (B := B × B)
  intro y
  rw [coordinateModuleProjection_inner_left, CStarModule.inner_op_smul_left,
    CStarModule.inner_op_smul_left, coordinateCoefficient_mul_right,
    coordinateCoefficient_star]

/-- The coordinate limit is adjointable and is its own adjoint. -/
def coordinateAdjointableProjection (k : Bool) : AdjointableMap (B × B) E E where
  toCLM := coordinateModuleProjectionCLM (B := B) k
  adjointCLM := coordinateModuleProjectionCLM (B := B) k
  adjoint_identity x y := by
    change ⟪coordinateModuleProjection (B := B) k x, y⟫_((B × B)ᵐᵒᵖ) =
      ⟪x, coordinateModuleProjection (B := B) k y⟫_((B × B)ᵐᵒᵖ)
    rw [coordinateModuleProjection_inner_left, coordinateModuleProjection_inner_right]

@[simp] theorem coordinateAdjointableProjection_apply (k : Bool) (x : E) :
    coordinateAdjointableProjection (B := B) k x = coordinateModuleProjection (B := B) k x := rfl

@[simp] theorem coordinateAdjointableProjection_star (k : Bool) :
    star (coordinateAdjointableProjection (B := B) (E := E) k) = coordinateAdjointableProjection (B := B) k := rfl

@[simp] theorem coordinateAdjointableProjection_square (k : Bool) :
    coordinateAdjointableProjection (B := B) (E := E) k * coordinateAdjointableProjection (B := B) k =
      coordinateAdjointableProjection (B := B) k := by
  apply AdjointableMap.ext
  intro x
  change coordinateModuleProjection (B := B) k (coordinateModuleProjection (B := B) k x) =
    coordinateModuleProjection (B := B) k x
  apply module_inner_ext_left (B := B × B)
  intro y
  simp only [coordinateModuleProjection_inner_left, coordinateCoefficient_idempotent]

@[simp] theorem coordinateAdjointableProjection_mul_complement (k : Bool) :
    coordinateAdjointableProjection (B := B) (E := E) k * coordinateAdjointableProjection (B := B) (!k) = 0 := by
  apply AdjointableMap.ext
  intro x
  change coordinateModuleProjection (B := B) k (coordinateModuleProjection (B := B) (!k) x) = 0
  apply module_inner_ext_left (B := B × B)
  intro y
  simp only [coordinateModuleProjection_inner_left, coordinateCoefficient_complement,
    CStarModule.inner_zero_left]

/-- Every vector splits into the two actual coordinate projection ranges. -/
theorem coordinateAdjointableProjection_add_complement (k : Bool) :
    coordinateAdjointableProjection (B := B) (E := E) k + coordinateAdjointableProjection (B := B) (!k) = 1 := by
  apply AdjointableMap.ext
  intro x
  change coordinateModuleProjection (B := B) k x + coordinateModuleProjection (B := B) (!k) x = x
  apply module_inner_ext_left (B := B × B)
  intro y
  simp only [CStarModule.inner_add_left, coordinateModuleProjection_inner_left,
    coordinateCoefficient_add_complement]

theorem coordinateAdjointableProjection_isStarProjection (k : Bool) :
    IsStarProjection (coordinateAdjointableProjection (B := B) (E := E) k) :=
  isStarProjection_iff'.mpr
    ⟨coordinateAdjointableProjection_square k, coordinateAdjointableProjection_star k⟩

/-- The coordinate limits commute with every genuine coefficient-linear
adjointable map, including rectangular maps between complete modules. -/
theorem coordinateModuleProjection_map
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul (B × B)ᵐᵒᵖ F]
    [CStarModule (B × B)ᵐᵒᵖ F] [CompleteSpace F]
    (k : Bool) (T : AdjointableMap (B × B) E F) (x : E) :
    T (coordinateModuleProjection (B := B) k x) = coordinateModuleProjection (B := B) k (T x) := by
  have hleft := (T.toCLM.continuous.tendsto (coordinateModuleProjection (B := B) k x)).comp
    (tendsto_coordinateModuleProjection (B := B) k x)
  have hright := tendsto_coordinateModuleProjection (B := B) k (T x)
  apply tendsto_nhds_unique hleft
  change Tendsto (fun a : (B × B)ᵐᵒᵖ => T (coordinateCoefficient k a • x))
    (CStarAlgebra.approximateUnit (B × B)ᵐᵒᵖ)
    (𝓝 (coordinateModuleProjection (B := B) k (T x)))
  simpa only [T.map_op_smul] using hright

/-- Every complete product-coefficient module splits into the genuine ranges
of the two constructed projections, with their inherited Hilbert norm. -/
def coordinateModuleRangeDecomposition (k : Bool) :
    HilbertModuleEquiv (B × B) E
      (HilbertModuleSum (B × B)
        (ProjectionModule (coordinateAdjointableProjection (B := B) (E := E) k))
        (ProjectionModule (coordinateAdjointableProjection (B := B) (E := E) (!k)))) := by
  let P := coordinateAdjointableProjection (B := B) (E := E) k
  let Q := coordinateAdjointableProjection (B := B) (E := E) (!k)
  have hP (x : E) : P (P x) = P x :=
    congrArg (fun T : AdjointableMap (B × B) E E => T x)
      (coordinateAdjointableProjection_square k)
  have hQ (x : E) : Q (Q x) = Q x :=
    congrArg (fun T : AdjointableMap (B × B) E E => T x)
      (coordinateAdjointableProjection_square (!k))
  let L : E →ₗ[ℂ] HilbertModuleSum (B × B) (ProjectionModule P) (ProjectionModule Q) :=
    { toFun x := sumMk ⟨P x, hP x⟩ ⟨Q x, hQ x⟩
      map_add' x y := by
        apply Prod.ext <;> apply Subtype.ext
        · exact P.toCLM.map_add x y
        · exact Q.toCLM.map_add x y
      map_smul' c x := by
        apply Prod.ext <;> apply Subtype.ext
        · exact P.toCLM.map_smul c x
        · exact Q.toCLM.map_smul c x }
  have hinner (x y : E) : ⟪L x, L y⟫_((B × B)ᵐᵒᵖ) = ⟪x, y⟫_((B × B)ᵐᵒᵖ) := by
    change ⟪coordinateModuleProjection (B := B) k x, coordinateModuleProjection (B := B) k y⟫_((B × B)ᵐᵒᵖ) +
      ⟪coordinateModuleProjection (B := B) (!k) x, coordinateModuleProjection (B := B) (!k) y⟫_((B × B)ᵐᵒᵖ) = _
    rw [coordinateModuleProjection_inner_left, coordinateModuleProjection_inner_left,
      coordinateModuleProjection_inner_right, coordinateModuleProjection_inner_right,
      coordinateCoefficient_idempotent, coordinateCoefficient_idempotent,
      coordinateCoefficient_add_complement]
  refine
    { linearIsometryEquiv :=
        { toFun := L
          invFun := fun y => (y.fst : E) + (y.snd : E)
          left_inv := ?_
          right_inv := ?_
          map_add' := L.map_add
          map_smul' := L.map_smul
          norm_map' := ?_ }
      inner_map := hinner }
  · intro x
    exact congrArg (fun T : AdjointableMap (B × B) E E => T x)
      (coordinateAdjointableProjection_add_complement k)
  · intro y
    have hPQ : P (y.snd : E) = 0 := by
      calc
        P (y.snd : E) = P (Q (y.snd : E)) := congrArg P y.snd.property.symm
        _ = 0 := congrArg (fun T : AdjointableMap (B × B) E E => T (y.snd : E))
          (coordinateAdjointableProjection_mul_complement k)
    have hQP : Q (y.fst : E) = 0 := by
      have h := coordinateAdjointableProjection_mul_complement (B := B) (E := E) (!k)
      simp only [Bool.not_not] at h
      calc
        Q (y.fst : E) = Q (P (y.fst : E)) := congrArg Q y.fst.property.symm
        _ = 0 := congrArg (fun T : AdjointableMap (B × B) E E => T (y.fst : E)) h
    apply Prod.ext <;> apply Subtype.ext
    · change P ((y.fst : E) + (y.snd : E)) = (y.fst : E)
      rw [P.toCLM.map_add, y.fst.property, hPQ, add_zero]
    · change Q ((y.fst : E) + (y.snd : E)) = (y.snd : E)
      rw [Q.toCLM.map_add, hQP, y.snd.property, zero_add]
  · intro x
    change ‖L x‖ = ‖x‖
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := (B × B)ᵐᵒᵖ), hinner,
      ← CStarModule.norm_eq_sqrt_norm_inner_self (A := (B × B)ᵐᵒᵖ)]

@[simp] theorem coordinateModuleRangeDecomposition_fst (k : Bool) (x : E) :
    ((coordinateModuleRangeDecomposition (B := B) k x).fst : E) = coordinateModuleProjection (B := B) k x := rfl

@[simp] theorem coordinateModuleRangeDecomposition_snd (k : Bool) (x : E) :
    ((coordinateModuleRangeDecomposition (B := B) k x).snd : E) = coordinateModuleProjection (B := B) (!k) x := rfl

end ProductCoefficient
end BC4lean.KKTheory
