import BC4lean.CompactModuleOperator
import BC4lean.CountablyGeneratedModule
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.Normed.Operator.Mul

/-! # Operators on the standard right Hilbert module

Left multiplication gives an isometric complex star algebra representation
of a possibly nonunital C⋆-algebra on its standard right module. Its range
is exactly the compact module operators. The forward inclusion uses an
approximate unit, and the reverse inclusion uses closedness of the isometric
range and the explicit rank-one multiplication formula.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace Topology
open Filter

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Left multiplication on the standard right module, in the opposite model. -/
def standardLeftMulCLM (b : B) : Bᵐᵒᵖ →L[ℂ] Bᵐᵒᵖ :=
  (ContinuousLinearMap.mul ℂ Bᵐᵒᵖ).flip (MulOpposite.op b)

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem standardLeftMulCLM_apply (b : B) (x : Bᵐᵒᵖ) :
    standardLeftMulCLM b x = MulOpposite.op (b * MulOpposite.unop x) := rfl

/-- Left multiplication is adjointable, with adjoint left multiplication by `b*`. -/
def standardLeftMulMap (b : B) : AdjointableMap B Bᵐᵒᵖ Bᵐᵒᵖ where
  toCLM := standardLeftMulCLM b
  adjointCLM := standardLeftMulCLM (star b)
  adjoint_identity x y := by
    change MulOpposite.op (star (b * MulOpposite.unop x) * MulOpposite.unop y) =
      MulOpposite.op (star (MulOpposite.unop x) * (star b * MulOpposite.unop y))
    simp only [star_mul, mul_assoc]

/-- The left regular representation on the standard right Hilbert module. -/
def standardLeftMul : B →⋆ₙₐ[ℂ] AdjointableMap B Bᵐᵒᵖ Bᵐᵒᵖ where
  toFun := standardLeftMulMap
  map_zero' := by
    ext x
    change MulOpposite.op (0 * MulOpposite.unop x) = 0
    simp
  map_add' a b := by
    ext x
    change MulOpposite.op ((a + b) * MulOpposite.unop x) =
      MulOpposite.op (a * MulOpposite.unop x) + MulOpposite.op (b * MulOpposite.unop x)
    simp only [add_mul, MulOpposite.op_add]
  map_mul' a b := by
    ext x
    change MulOpposite.op ((a * b) * MulOpposite.unop x) =
      MulOpposite.op (a * (b * MulOpposite.unop x))
    rw [mul_assoc]
  map_smul' c b := by
    ext x
    change MulOpposite.op ((c • b) * MulOpposite.unop x) =
      c • MulOpposite.op (b * MulOpposite.unop x)
    simp only [smul_mul_assoc, MulOpposite.op_smul]
  map_star' b := by ext x; rfl

@[simp] theorem standardLeftMul_apply (b : B) (x : Bᵐᵒᵖ) :
    standardLeftMul b x = MulOpposite.op (b * MulOpposite.unop x) := rfl

@[simp] theorem standardLeftMul_apply_op (b x : B) :
    standardLeftMul b (MulOpposite.op x) = MulOpposite.op (b * x) := rfl

@[simp] theorem standardLeftMul_adjoint (b : B) :
    (standardLeftMul b).adjoint = standardLeftMul (star b) := by ext x; rfl

/-- The operator-norm upper bound for left multiplication. -/
theorem norm_standardLeftMul_le (b : B) : ‖standardLeftMul b‖ ≤ ‖b‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (_root_.norm_nonneg b)
  intro x
  change ‖b * MulOpposite.unop x‖ ≤ ‖b‖ * ‖MulOpposite.unop x‖
  exact norm_mul_le _ _

/-- Left multiplication has the same norm as its coefficient, also without a unit. -/
@[simp] theorem norm_standardLeftMul (b : B) : ‖standardLeftMul b‖ = ‖b‖ := by
  apply le_antisymm (norm_standardLeftMul_le b)
  by_cases hb : ‖b‖ = 0
  · simpa only [hb] using (_root_.norm_nonneg (standardLeftMul b))
  · have h : ‖b‖ * ‖b‖ ≤ ‖standardLeftMul b‖ * ‖b‖ := by
      have hbound := AdjointableMap.norm_apply_le (standardLeftMul b) (MulOpposite.op (star b))
      simpa only [standardLeftMul_apply_op, MulOpposite.norm_op, norm_star,
        CStarRing.norm_self_mul_star, AdjointableMap.norm_def] using hbound
    exact le_of_mul_le_mul_right h
      (lt_of_le_of_ne (_root_.norm_nonneg b) (Ne.symm hb))

/-- The complex-linear form of the standard left representation. -/
def standardLeftMulLinearMap : B →ₗ[ℂ] AdjointableMap B Bᵐᵒᵖ Bᵐᵒᵖ where
  toFun := standardLeftMul
  map_add' := map_add standardLeftMul
  map_smul' := map_smul standardLeftMul

/-- The standard left representation is a linear isometry. -/
def standardLeftMulLinearIsometry : B →ₗᵢ[ℂ] AdjointableMap B Bᵐᵒᵖ Bᵐᵒᵖ :=
  { standardLeftMulLinearMap with norm_map' := norm_standardLeftMul }

theorem standardLeftMul_isometry : Isometry (standardLeftMul (B := B)) :=
  standardLeftMulLinearIsometry.isometry

theorem standardLeftMul_injective : Function.Injective (standardLeftMul (B := B)) :=
  standardLeftMul_isometry.injective

/-- The left representation has closed range because the coefficient algebra is complete. -/
theorem standardLeftMul_range_isClosed :
    IsClosed ((standardLeftMulLinearMap (B := B)).range :
      Set (AdjointableMap B Bᵐᵒᵖ Bᵐᵒᵖ)) := by
  change IsClosed (Set.range (standardLeftMul (B := B)))
  exact standardLeftMul_isometry.isClosedEmbedding.isClosed_range

/-- Every standard-module rank-one map is left multiplication by `x y*`. -/
theorem standard_moduleRankOne_eq_leftMul (x y : Bᵐᵒᵖ) :
    moduleRankOne (B := B) x y =
      standardLeftMul (MulOpposite.unop x * star (MulOpposite.unop y)) := by
  ext z
  apply MulOpposite.unop_injective
  exact standard_moduleRankOne (MulOpposite.unop x) (MulOpposite.unop y) (MulOpposite.unop z)

/-- Every coefficient acts by a compact operator on the standard right module. -/
theorem standardLeftMul_mem_moduleCompact (b : B) :
    standardLeftMul b ∈ moduleCompact B Bᵐᵒᵖ Bᵐᵒᵖ := by
  have hlim : Tendsto (fun u : B => standardLeftMul (b * u))
      (CStarAlgebra.approximateUnit B) (𝓝 (standardLeftMul b)) :=
    standardLeftMul_isometry.continuous.tendsto b |>.comp
      ((CStarAlgebra.increasingApproximateUnit B).tendsto_mul_left b)
  apply moduleCompact_isClosed.mem_of_tendsto hlim
  exact Eventually.of_forall fun u => by
    change standardLeftMul (b * u) ∈ moduleCompact B Bᵐᵒᵖ Bᵐᵒᵖ
    simpa only [standard_moduleRankOne_eq_leftMul, MulOpposite.unop_op, star_star] using
      moduleRankOne_mem_moduleCompact (B := B) (MulOpposite.op b) (MulOpposite.op (star u))

/-- Every compact standard-module operator lies in the left representation's range. -/
theorem moduleCompact_standard_le_range :
    moduleCompact B Bᵐᵒᵖ Bᵐᵒᵖ ≤ (standardLeftMulLinearMap (B := B)).range := by
  apply moduleCompact_le_of_isClosed (B := B) (E := Bᵐᵒᵖ) (F := Bᵐᵒᵖ)
    (standardLeftMulLinearMap (B := B)).range standardLeftMul_range_isClosed
  intro x y
  exact ⟨MulOpposite.unop x * star (MulOpposite.unop y),
    (standard_moduleRankOne_eq_leftMul x y).symm⟩

/-- Compact standard-module operators are exactly the left multiplications. -/
theorem moduleCompact_standard_eq_range :
    moduleCompact B Bᵐᵒᵖ Bᵐᵒᵖ = (standardLeftMulLinearMap (B := B)).range := by
  apply le_antisymm moduleCompact_standard_le_range
  rintro T ⟨b, rfl⟩
  exact standardLeftMul_mem_moduleCompact b

/-- The explicit characterization of compact operators on the standard module. -/
theorem mem_moduleCompact_standard_iff (T : AdjointableMap B Bᵐᵒᵖ Bᵐᵒᵖ) :
    T ∈ moduleCompact B Bᵐᵒᵖ Bᵐᵒᵖ ↔ ∃ b : B, standardLeftMul b = T := by
  rw [moduleCompact_standard_eq_range]
  rfl

/-- Left multiplication with its codomain restricted to compact operators. -/
def standardLeftMulCompactHom : B →⋆ₙₐ[ℂ] CompactModuleOperator B Bᵐᵒᵖ :=
  NonUnitalStarAlgHom.codRestrict standardLeftMul
    (compactModuleOperatorAlgebra (B := B) (E := Bᵐᵒᵖ)) standardLeftMul_mem_moduleCompact

theorem standardLeftMulCompactHom_bijective :
    Function.Bijective (standardLeftMulCompactHom (B := B)) := by
  constructor
  · intro a b h
    apply standardLeftMul_injective
    exact congrArg Subtype.val h
  · intro T
    obtain ⟨b, hb⟩ := (mem_moduleCompact_standard_iff T.val).mp T.property
    exact ⟨b, Subtype.ext hb⟩

/-- The coefficient algebra is isomorphic to the compact operators on its standard module. -/
def standardCompactEquiv : B ≃⋆ₐ[ℂ] CompactModuleOperator B Bᵐᵒᵖ :=
  StarAlgEquiv.ofBijective standardLeftMulCompactHom standardLeftMulCompactHom_bijective

@[simp] theorem standardCompactEquiv_apply_val (b : B) :
    (standardCompactEquiv b).val = standardLeftMul b := rfl

/-- The standard compact-operator identification is isometric. -/
@[simp] theorem norm_standardCompactEquiv (b : B) : ‖standardCompactEquiv b‖ = ‖b‖ :=
  norm_standardLeftMul b

/-- A dense sequence generates the standard module even for nonunital coefficients. -/
theorem standard_moduleGeneratingSpan_dense (ξ : ℕ → Bᵐᵒᵖ) (hξ : DenseRange ξ) :
    Dense (moduleGeneratingSpan (B := B) ξ : Set Bᵐᵒᵖ) := by
  have hrange : Set.range ξ ⊆ closure (moduleGeneratingSpan (B := B) ξ : Set Bᵐᵒᵖ) := by
    rintro _ ⟨n, rfl⟩
    have hlim : Tendsto (fun u : B => MulOpposite.op u • ξ n)
        (CStarAlgebra.approximateUnit B) (𝓝 (ξ n)) := by
      change Tendsto (fun u : B => MulOpposite.op (MulOpposite.unop (ξ n) * u))
        (CStarAlgebra.approximateUnit B) (𝓝 (MulOpposite.op (MulOpposite.unop (ξ n))))
      exact MulOpposite.continuous_op.tendsto _ |>.comp
        ((CStarAlgebra.increasingApproximateUnit B).tendsto_mul_left (MulOpposite.unop (ξ n)))
    apply (Submodule.isClosed_topologicalClosure (moduleGeneratingSpan (B := B) ξ)).mem_of_tendsto hlim
    exact Eventually.of_forall fun u =>
      Submodule.le_topologicalClosure _ (smul_mem_moduleGeneratingSpan ξ n (MulOpposite.op u))
  intro x
  have hx := closure_mono hrange (hξ x)
  simpa only [closure_closure] using hx

/-- A separable C⋆-algebra is countably generated as a right module over itself. -/
theorem standard_module_isCountablyGenerated [TopologicalSpace.SeparableSpace B] :
    IsCountablyGeneratedModule B Bᵐᵒᵖ := by
  refine ⟨fun n => MulOpposite.op (TopologicalSpace.denseSeq B n), ?_⟩
  apply standard_moduleGeneratingSpan_dense
  exact MulOpposite.op_surjective.denseRange.comp
    (TopologicalSpace.denseRange_denseSeq B) MulOpposite.continuous_op

end BC4lean.KKTheory
