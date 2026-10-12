import BC4lean.HilbertModuleApproximateUnit
import BC4lean.CliffordCoefficientGrading

/-! # Genuine coefficient ranges for the product model of Cl₁

The actual coordinate projections are constructed from coefficient
approximate-unit limits in `HilbertModuleApproximateUnit`. Their ranges are
right Hilbert B-modules by selecting the supported coordinate of the
B × B-valued inner product. The inherited norm is proved to be exactly that
Hilbert-module norm. Operators restrict continuously, and actual module
compactness transfers by the proved rank-one compression formula and norm
closure. No coefficient units, central projections, tensor identification or
compactness equivalence are assumed.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped Topology InnerProductSpace

variable {B : Type*} [NonUnitalCStarAlgebra B]

/-- Embed B into the first (`true`) or second (`false`) actual coefficient ideal. -/
def cliffordCoordinateEmbedding (k : Bool) (b : Bᵐᵒᵖ) : (B × B)ᵐᵒᵖ :=
  if k then MulOpposite.op (MulOpposite.unop b, 0)
  else MulOpposite.op (0, MulOpposite.unop b)

/-- Select the B-valued coordinate supported by a projection range. -/
def cliffordCoordinateExtraction (k : Bool) (a : (B × B)ᵐᵒᵖ) : Bᵐᵒᵖ :=
  MulOpposite.op (if k then (MulOpposite.unop a).1 else (MulOpposite.unop a).2)

@[simp] theorem cliffordCoordinateEmbedding_zero (k : Bool) :
    cliffordCoordinateEmbedding (B := B) k 0 = 0 := by cases k <;> rfl

@[simp] theorem cliffordCoordinateExtraction_zero (k : Bool) :
    cliffordCoordinateExtraction (B := B) k 0 = 0 := by cases k <;> rfl

@[simp] theorem cliffordCoordinateExtraction_add (k : Bool) (a b : (B × B)ᵐᵒᵖ) :
    cliffordCoordinateExtraction k (a + b) = cliffordCoordinateExtraction k a +
      cliffordCoordinateExtraction k b := by
  cases k <;> rfl

@[simp] theorem cliffordCoordinateExtraction_smul (k : Bool) (c : ℂ) (a : (B × B)ᵐᵒᵖ) :
    cliffordCoordinateExtraction k (c • a) = c • cliffordCoordinateExtraction k a := by
  cases k <;> rfl

@[simp] theorem cliffordCoordinateExtraction_star (k : Bool) (a : (B × B)ᵐᵒᵖ) :
    cliffordCoordinateExtraction k (star a) = star (cliffordCoordinateExtraction k a) := by
  cases k <;> rfl

@[simp] theorem cliffordCoordinateExtraction_mul (k : Bool) (a b : (B × B)ᵐᵒᵖ) :
    cliffordCoordinateExtraction k (a * b) = cliffordCoordinateExtraction k a *
      cliffordCoordinateExtraction k b := by cases k <;> rfl

@[simp] theorem cliffordCoordinateEmbedding_mul (k : Bool) (a b : Bᵐᵒᵖ) :
    cliffordCoordinateEmbedding k (a * b) = cliffordCoordinateEmbedding k a *
      cliffordCoordinateEmbedding k b := by
  cases k <;> apply MulOpposite.unop_injective <;> ext <;> simp [cliffordCoordinateEmbedding]

@[simp] theorem cliffordCoordinateExtraction_embedding (k : Bool) (b : Bᵐᵒᵖ) :
    cliffordCoordinateExtraction k (cliffordCoordinateEmbedding k b) = b := by cases k <;> rfl

@[simp] theorem cliffordCoordinateEmbedding_extraction (k : Bool) (a : (B × B)ᵐᵒᵖ) :
    cliffordCoordinateEmbedding k (cliffordCoordinateExtraction k a) = coordinateCoefficient k a := by
  cases k <;> rfl

theorem cliffordCoordinateEmbedding_injective (k : Bool) :
    Function.Injective (cliffordCoordinateEmbedding (B := B) k) := by
  intro a b h
  simpa only [cliffordCoordinateExtraction_embedding] using
    congrArg (cliffordCoordinateExtraction k) h

@[simp] theorem cliffordCoordinateEmbedding_norm (k : Bool) (b : Bᵐᵒᵖ) :
    ‖cliffordCoordinateEmbedding k b‖ = ‖b‖ := by
  cases k <;> simp [cliffordCoordinateEmbedding, Prod.norm_def, MulOpposite.norm_op, MulOpposite.norm_unop]

variable [PartialOrder B] [StarOrderedRing B]

section Ranges

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul (B × B)ᵐᵒᵖ E]
  [CStarModule (B × B)ᵐᵒᵖ E] [CompleteSpace E]

/-- An actual coordinate projection range, with the ambient norm unchanged. -/
abbrev CliffordCoefficientRange (B E : Type*) [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul (B × B)ᵐᵒᵖ E]
    [CStarModule (B × B)ᵐᵒᵖ E] [CompleteSpace E] (k : Bool) :=
  ProjectionModule (coordinateAdjointableProjection (B := B) (E := E) k)

@[simp] theorem cliffordCoefficientRange_projection (k : Bool)
    (x : CliffordCoefficientRange B E k) : coordinateModuleProjection (B := B) k (x : E) = (x : E) :=
  x.property

/-- The original inner product of range vectors is supported in the selected ideal. -/
theorem cliffordCoefficientRange_inner_supported (k : Bool)
    (x y : CliffordCoefficientRange B E k) :
    coordinateCoefficient k ⟪(x : E), (y : E)⟫_((B × B)ᵐᵒᵖ) =
      ⟪(x : E), (y : E)⟫_((B × B)ᵐᵒᵖ) := by
  rw [← coordinateModuleProjection_inner_left, cliffordCoefficientRange_projection]

instance cliffordCoefficientRangeSMul (k : Bool) : SMul Bᵐᵒᵖ (CliffordCoefficientRange B E k) where
  smul b x := ⟨cliffordCoordinateEmbedding k b • (x : E), by
    change coordinateAdjointableProjection (B := B) k
      (cliffordCoordinateEmbedding k b • (x : E)) = cliffordCoordinateEmbedding k b • (x : E)
    rw [AdjointableMap.map_op_smul, x.property]⟩

@[simp] theorem cliffordCoefficientRange_coe_smul (k : Bool) (b : Bᵐᵒᵖ)
    (x : CliffordCoefficientRange B E k) :
    ((b • x : CliffordCoefficientRange B E k) : E) = cliffordCoordinateEmbedding k b • (x : E) := rfl

instance cliffordCoefficientRangeInner (k : Bool) : Inner Bᵐᵒᵖ (CliffordCoefficientRange B E k) where
  inner x y := cliffordCoordinateExtraction k ⟪(x : E), (y : E)⟫_((B × B)ᵐᵒᵖ)

@[simp] theorem cliffordCoefficientRange_inner (k : Bool)
    (x y : CliffordCoefficientRange B E k) :
    ⟪x, y⟫_(Bᵐᵒᵖ) = cliffordCoordinateExtraction k ⟪(x : E), (y : E)⟫_((B × B)ᵐᵒᵖ) := rfl

/-- The selected inner product embeds back to the original one exactly. -/
theorem cliffordCoefficientRange_embed_inner (k : Bool)
    (x y : CliffordCoefficientRange B E k) :
    cliffordCoordinateEmbedding k ⟪x, y⟫_(Bᵐᵒᵖ) = ⟪(x : E), (y : E)⟫_((B × B)ᵐᵒᵖ) := by
  rw [cliffordCoefficientRange_inner, cliffordCoordinateEmbedding_extraction,
    cliffordCoefficientRange_inner_supported]

/-- Every genuine Hilbert-module law over B follows from the inherited
product-coefficient inner product and its proved support. -/
instance cliffordCoefficientRangeCStarModule (k : Bool) :
    CStarModule Bᵐᵒᵖ (CliffordCoefficientRange B E k) where
  inner := cliffordCoefficientRangeInner k |>.inner
  inner_add_right := by
    intro x y z
    change cliffordCoordinateExtraction k ⟪(x : E), (y : E) + (z : E)⟫_((B × B)ᵐᵒᵖ) =
      cliffordCoordinateExtraction k ⟪(x : E), (y : E)⟫_((B × B)ᵐᵒᵖ) +
        cliffordCoordinateExtraction k ⟪(x : E), (z : E)⟫_((B × B)ᵐᵒᵖ)
    rw [CStarModule.inner_add_right, cliffordCoordinateExtraction_add]
  inner_self_nonneg := by
    intro x
    have h : (0 : (B × B)ᵐᵒᵖ) ≤ ⟪(x : E), (x : E)⟫_((B × B)ᵐᵒᵖ) :=
      CStarModule.inner_self_nonneg
    cases k
    · exact h.2
    · exact h.1
  inner_self := by
    intro x
    constructor
    · intro h
      have hzero : ⟪(x : E), (x : E)⟫_((B × B)ᵐᵒᵖ) = 0 := by
        rw [← cliffordCoefficientRange_embed_inner, h, cliffordCoordinateEmbedding_zero]
      apply Subtype.ext
      exact (CStarModule.inner_self (A := (B × B)ᵐᵒᵖ)).mp hzero
    · intro h
      rw [h]
      change cliffordCoordinateExtraction k ⟪(0 : E), 0⟫_((B × B)ᵐᵒᵖ) = 0
      rw [CStarModule.inner_zero_left, cliffordCoordinateExtraction_zero]
  inner_op_smul_right := by
    intro b x y
    change cliffordCoordinateExtraction k
      ⟪(x : E), cliffordCoordinateEmbedding k b • (y : E)⟫_((B × B)ᵐᵒᵖ) =
        b * cliffordCoordinateExtraction k ⟪(x : E), (y : E)⟫_((B × B)ᵐᵒᵖ)
    rw [CStarModule.inner_op_smul_right, cliffordCoordinateExtraction_mul,
      cliffordCoordinateExtraction_embedding]
  inner_smul_right_complex := by
    intro c x y
    change cliffordCoordinateExtraction k ⟪(x : E), c • (y : E)⟫_((B × B)ᵐᵒᵖ) =
      c • cliffordCoordinateExtraction k ⟪(x : E), (y : E)⟫_((B × B)ᵐᵒᵖ)
    rw [CStarModule.inner_smul_right_complex, cliffordCoordinateExtraction_smul]
  star_inner x y := by
    change star (cliffordCoordinateExtraction k ⟪(x : E), (y : E)⟫_((B × B)ᵐᵒᵖ)) =
      cliffordCoordinateExtraction k ⟪(y : E), (x : E)⟫_((B × B)ᵐᵒᵖ)
    rw [← cliffordCoordinateExtraction_star, CStarModule.star_inner]
  norm_eq_sqrt_norm_inner_self x := by
    change ‖(x : E)‖ = Real.sqrt ‖⟪x, x⟫_(Bᵐᵒᵖ)‖
    rw [← cliffordCoordinateEmbedding_norm k, cliffordCoefficientRange_embed_inner]
    exact CStarModule.norm_eq_sqrt_norm_inner_self (A := (B × B)ᵐᵒᵖ) (x : E)

/-- Completeness is inherited from the proved closed ambient range. -/
theorem cliffordCoefficientRange_complete (k : Bool) : CompleteSpace (CliffordCoefficientRange B E k) :=
  inferInstance

/-- Product-coefficient action on a range reduces to the selected B action. -/
theorem cliffordCoefficientRange_product_smul (k : Bool) (a : (B × B)ᵐᵒᵖ)
    (x : CliffordCoefficientRange B E k) :
    (a • x : ProjectionModule (coordinateAdjointableProjection (B := B) (E := E) k)) =
      cliffordCoordinateExtraction k a • x := by
  apply Subtype.ext
  change a • (x : E) = cliffordCoordinateEmbedding k (cliffordCoordinateExtraction k a) • (x : E)
  rw [cliffordCoordinateEmbedding_extraction]
  have h := (coordinateAdjointableProjection (B := B) (E := E) k).map_op_smul a (x : E)
  rw [x.property] at h
  exact h.symm.trans (coordinateModuleProjection_coefficient_smul k a (x : E))

/-- Countable generation survives the genuine coefficient reduction. -/
theorem cliffordCoefficientRange_countablyGenerated (k : Bool)
    (hE : IsCountablyGeneratedModule (B × B) E) :
    IsCountablyGeneratedModule B (CliffordCoefficientRange B E k) := by
  obtain ⟨ξ, hξ⟩ := projectionModule_isCountablyGenerated
    (coordinateAdjointableProjection (B := B) (E := E) k)
    (coordinateAdjointableProjection_isStarProjection k) hE
  refine ⟨ξ, hξ.mono ?_⟩
  apply Submodule.span_le.mpr
  rintro _ ⟨n, a, rfl⟩
  rw [cliffordCoefficientRange_product_smul]
  exact smul_mem_moduleGeneratingSpan ξ n (cliffordCoordinateExtraction k a)

/-- The ambient coordinate projection, correctly corestricted to its range. -/
def cliffordCoefficientRangeProject (k : Bool) (x : E) : CliffordCoefficientRange B E k :=
  ⟨coordinateModuleProjection (B := B) k x, by
    exact congrArg (fun T : AdjointableMap (B × B) E E => T x)
      (coordinateAdjointableProjection_square (B := B) (E := E) k)⟩

@[simp] theorem cliffordCoefficientRangeProject_coe (k : Bool) (x : E) :
    (cliffordCoefficientRangeProject (B := B) k x : E) = coordinateModuleProjection (B := B) k x := rfl

variable {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul (B × B)ᵐᵒᵖ F]
  [CStarModule (B × B)ᵐᵒᵖ F] [CompleteSpace F]

/-- A genuine product-coefficient operator preserves the coordinate ranges. -/
def cliffordRangeRestrictionCLM (k : Bool) (T : AdjointableMap (B × B) E F) :
    CliffordCoefficientRange B E k →L[ℂ] CliffordCoefficientRange B F k :=
  (T.toCLM.comp (projectionFixedSubmodule
    (coordinateAdjointableProjection (B := B) (E := E) k)).subtypeL).codRestrict
    (projectionFixedSubmodule (coordinateAdjointableProjection (B := B) (E := F) k)) (fun x => by
      change coordinateModuleProjection (B := B) k (T (x : E)) = T (x : E)
      have hx : coordinateModuleProjection (B := B) k (x : E) = (x : E) := x.property
      rw [← coordinateModuleProjection_map, hx])

@[simp] theorem cliffordRangeRestrictionCLM_coe (k : Bool) (T : AdjointableMap (B × B) E F)
    (x : CliffordCoefficientRange B E k) : (cliffordRangeRestrictionCLM k T x : F) = T (x : E) := rfl

/-- Restriction is genuinely B-adjointable; its adjoint is the actual
restriction of the original adjoint. -/
def cliffordRangeRestriction (k : Bool) (T : AdjointableMap (B × B) E F) :
    AdjointableMap B (CliffordCoefficientRange B E k) (CliffordCoefficientRange B F k) where
  toCLM := cliffordRangeRestrictionCLM k T
  adjointCLM := cliffordRangeRestrictionCLM k T.adjoint
  adjoint_identity x y := congrArg (cliffordCoordinateExtraction k)
    (T.adjoint_identity (x : E) (y : F))

@[simp] theorem cliffordRangeRestriction_coe (k : Bool) (T : AdjointableMap (B × B) E F)
    (x : CliffordCoefficientRange B E k) : (cliffordRangeRestriction k T x : F) = T (x : E) := rfl

@[simp] theorem cliffordRangeRestriction_adjoint (k : Bool) (T : AdjointableMap (B × B) E F) :
    (cliffordRangeRestriction k T).adjoint = cliffordRangeRestriction k T.adjoint := rfl

@[simp] theorem cliffordRangeRestriction_zero (k : Bool) :
    cliffordRangeRestriction k (0 : AdjointableMap (B × B) E F) = 0 := by ext x; rfl

@[simp] theorem cliffordRangeRestriction_add (k : Bool) (S T : AdjointableMap (B × B) E F) :
    cliffordRangeRestriction k (S + T) = cliffordRangeRestriction k S + cliffordRangeRestriction k T := by
  apply AdjointableMap.ext
  intro x
  apply Subtype.ext
  rfl

@[simp] theorem cliffordRangeRestriction_smul (k : Bool) (c : ℂ) (T : AdjointableMap (B × B) E F) :
    cliffordRangeRestriction k (c • T) = c • cliffordRangeRestriction k T := by
  apply AdjointableMap.ext
  intro x
  apply Subtype.ext
  rfl

@[simp] theorem cliffordRangeRestriction_sub (k : Bool) (S T : AdjointableMap (B × B) E F) :
    cliffordRangeRestriction k (S - T) = cliffordRangeRestriction k S - cliffordRangeRestriction k T := by
  apply AdjointableMap.ext
  intro x
  apply Subtype.ext
  rfl

@[simp] theorem cliffordRangeRestriction_star (k : Bool) (T : AdjointableMap (B × B) E E) :
    cliffordRangeRestriction k (star T) = star (cliffordRangeRestriction k T) := rfl

@[simp] theorem cliffordRangeRestriction_comp
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul (B × B)ᵐᵒᵖ G]
    [CStarModule (B × B)ᵐᵒᵖ G] [CompleteSpace G] (k : Bool)
    (S : AdjointableMap (B × B) F G) (T : AdjointableMap (B × B) E F) :
    cliffordRangeRestriction k (S.comp T) = (cliffordRangeRestriction k S).comp
      (cliffordRangeRestriction k T) := by
  apply AdjointableMap.ext
  intro x
  apply Subtype.ext
  rfl

@[simp] theorem cliffordRangeRestriction_one (k : Bool) :
    cliffordRangeRestriction k (1 : AdjointableMap (B × B) E E) = 1 := by
  apply AdjointableMap.ext
  intro x
  apply Subtype.ext
  rfl

@[simp] theorem cliffordRangeRestriction_mul (k : Bool) (S T : AdjointableMap (B × B) E E) :
    cliffordRangeRestriction k (S * T) = cliffordRangeRestriction k S * cliffordRangeRestriction k T :=
  cliffordRangeRestriction_comp k S T

/-- The inherited range norm gives a contractive restriction map. -/
theorem cliffordRangeRestriction_norm_le (k : Bool) (T : AdjointableMap (B × B) E F) :
    ‖cliffordRangeRestriction k T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  exact T.toCLM.le_opNorm (x : E)

/-- Rectangular restriction is a genuine norm-continuous complex linear map. -/
def cliffordRangeRestrictionMap (k : Bool) : AdjointableMap (B × B) E F →L[ℂ]
    AdjointableMap B (CliffordCoefficientRange B E k) (CliffordCoefficientRange B F k) :=
  ({ toFun := cliffordRangeRestriction k
     map_add' := cliffordRangeRestriction_add k
     map_smul' := cliffordRangeRestriction_smul k } : AdjointableMap (B × B) E F →ₗ[ℂ]
       AdjointableMap B (CliffordCoefficientRange B E k) (CliffordCoefficientRange B F k)).mkContinuous
    1 (fun T => by
      change ‖cliffordRangeRestriction k T‖ ≤ 1 * ‖T‖
      simpa only [one_mul] using cliffordRangeRestriction_norm_le k T)

@[simp] theorem cliffordRangeRestrictionMap_apply (k : Bool) (T : AdjointableMap (B × B) E F) :
    cliffordRangeRestrictionMap k T = cliffordRangeRestriction k T := rfl

/-- A rank-one operator compresses to the actual B-valued rank-one operator
of the two genuine coordinate projections. -/
theorem cliffordRangeRestriction_rankOne (k : Bool) (x : F) (y : E) :
    cliffordRangeRestriction k (moduleRankOne (B := B × B) x y) =
      moduleRankOne (B := B) (cliffordCoefficientRangeProject k x)
        (cliffordCoefficientRangeProject k y) := by
  apply AdjointableMap.ext
  intro z
  apply Subtype.ext
  change ⟪y, (z : E)⟫_((B × B)ᵐᵒᵖ) • x =
    cliffordCoordinateEmbedding k
      (cliffordCoordinateExtraction k
        ⟪coordinateModuleProjection (B := B) k y, (z : E)⟫_((B × B)ᵐᵒᵖ)) • coordinateModuleProjection (B := B) k x
  have hz : coordinateCoefficient k ⟪y, (z : E)⟫_((B × B)ᵐᵒᵖ) =
      ⟪y, (z : E)⟫_((B × B)ᵐᵒᵖ) := by
    rw [← coordinateModuleProjection_inner_right, cliffordCoefficientRange_projection]
  rw [coordinateModuleProjection_inner_left, cliffordCoordinateEmbedding_extraction,
    coordinateCoefficient_idempotent, hz]
  have hP := (coordinateAdjointableProjection (B := B) (E := F) k).map_op_smul
    ⟪y, (z : E)⟫_((B × B)ᵐᵒᵖ) x
  change coordinateModuleProjection (B := B) k (⟪y, (z : E)⟫_((B × B)ᵐᵒᵖ) • x) =
    ⟪y, (z : E)⟫_((B × B)ᵐᵒᵖ) • coordinateModuleProjection (B := B) k x at hP
  rw [coordinateModuleProjection_coefficient_smul, hz] at hP
  exact hP

/-- Actual module compactness transfers by a continuous restriction map,
the proved rank-one formula and the closed rank-one-span definition. -/
theorem cliffordRangeRestriction_isModuleCompact (k : Bool)
    {T : AdjointableMap (B × B) E F} (hT : IsModuleCompact T) :
    IsModuleCompact (cliffordRangeRestriction k T) := by
  let S := (moduleCompact B (CliffordCoefficientRange B E k) (CliffordCoefficientRange B F k)).comap
    (cliffordRangeRestrictionMap (B := B) (E := E) (F := F) k).toLinearMap
  have hS : IsClosed (S : Set (AdjointableMap (B × B) E F)) :=
    moduleCompact_isClosed.preimage (cliffordRangeRestrictionMap k).continuous
  apply moduleCompact_le_of_isClosed S hS ?_ hT
  intro x y
  change cliffordRangeRestriction k (moduleRankOne (B := B × B) x y) ∈
    moduleCompact B (CliffordCoefficientRange B E k) (CliffordCoefficientRange B F k)
  rw [cliffordRangeRestriction_rankOne]
  exact moduleRankOne_mem_moduleCompact _ _

/-- Restriction of endomorphisms is a genuine unital complex star homomorphism. -/
def cliffordRangeRestrictionHom (k : Bool) : AdjointableMap (B × B) E E →⋆ₐ[ℂ]
    AdjointableMap B (CliffordCoefficientRange B E k) (CliffordCoefficientRange B E k) where
  toFun := cliffordRangeRestriction k
  map_zero' := cliffordRangeRestriction_zero k
  map_add' := cliffordRangeRestriction_add k
  map_one' := cliffordRangeRestriction_one k
  map_mul' S T := cliffordRangeRestriction_comp k S T
  commutes' c := by
    apply AdjointableMap.ext
    intro x
    apply Subtype.ext
    rfl
  map_star' T := (cliffordRangeRestriction_adjoint k T).symm

end Ranges

omit [PartialOrder B] [StarOrderedRing B] in
theorem cliffordCoordinateExtraction_action {Γ : Type*} [Group Γ]
    (β : CStarAlgebraAction Γ B) (g : Γ) (k : Bool) (a : (B × B)ᵐᵒᵖ) :
    cliffordCoordinateExtraction k
        (opStarAlgEquiv ((cliffordCoefficientAction β).automorphism g) a) =
      opStarAlgEquiv (β.automorphism g) (cliffordCoordinateExtraction k a) := by
  cases k <;> rfl

omit [PartialOrder B] [StarOrderedRing B] in
theorem coordinateCoefficient_action {Γ : Type*} [Group Γ]
    (β : CStarAlgebraAction Γ B) (g : Γ) (k : Bool) (a : (B × B)ᵐᵒᵖ) :
    opStarAlgEquiv ((cliffordCoefficientAction β).automorphism g)
        (coordinateCoefficient k a) =
      coordinateCoefficient k
        (opStarAlgEquiv ((cliffordCoefficientAction β).automorphism g) a) := by
  cases k <;> apply MulOpposite.unop_injective <;> ext <;>
    simp [coordinateCoefficient, opStarAlgEquiv, cliffordCoefficientAction]

omit [PartialOrder B] [StarOrderedRing B] in
theorem cliffordCoordinateExtraction_grading (k : Bool) (a : (B × B)ᵐᵒᵖ) :
    cliffordCoordinateExtraction (!k)
        (opStarAlgEquiv cliffordCoefficientGrading.automorphism a) =
      cliffordCoordinateExtraction k a := by cases k <;> rfl

omit [PartialOrder B] [StarOrderedRing B] in
theorem coordinateCoefficient_grading (k : Bool) (a : (B × B)ᵐᵒᵖ) :
    opStarAlgEquiv cliffordCoefficientGrading.automorphism (coordinateCoefficient k a) =
      coordinateCoefficient (!k) (opStarAlgEquiv cliffordCoefficientGrading.automorphism a) := by
  cases k <;> rfl

section GradingAndAction

variable {Γ E : Type*} [Group Γ]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul (B × B)ᵐᵒᵖ E]
  [CStarModule (B × B)ᵐᵒᵖ E] [CompleteSpace E]

/-- The actual module grading exchanges the two constructed coordinate ranges. -/
theorem coordinateModuleProjection_grading
    (γ : GradedHilbertModule (cliffordCoefficientGrading : CStarGrading (B × B)) E)
    (k : Bool) (x : E) :
    γ.grading (coordinateModuleProjection (B := B) k x) = coordinateModuleProjection (B := B) (!k) (γ.grading x) := by
  apply module_inner_ext_left (B := B × B)
  intro y
  rw [γ.inner_grading_left, coordinateModuleProjection_inner_left,
    coordinateCoefficient_grading, coordinateModuleProjection_inner_left,
    γ.inner_grading_left]

/-- The actual diagonal coefficient action preserves each constructed range. -/
theorem coordinateModuleProjection_action {β : CStarAlgebraAction Γ B}
    (U : EquivariantHilbertModule (cliffordCoefficientAction β) E)
    (g : Γ) (k : Bool) (x : E) :
    U.action g (coordinateModuleProjection (B := B) k x) = coordinateModuleProjection (B := B) k (U.action g x) := by
  apply module_inner_ext_left (B := B × B)
  intro y
  rw [U.inner_action_left, coordinateModuleProjection_inner_left,
    coordinateCoefficient_action, coordinateModuleProjection_inner_left,
    U.inner_action_left]

/-- Restrict the genuine module action to an actual coefficient range. -/
def cliffordRangeActionIsometry {β : CStarAlgebraAction Γ B}
    (U : EquivariantHilbertModule (cliffordCoefficientAction β) E)
    (k : Bool) (g : Γ) : CliffordCoefficientRange B E k ≃ₗᵢ[ℂ] CliffordCoefficientRange B E k where
  toFun x := ⟨U.action g (x : E), by
    change coordinateModuleProjection (B := B) k (U.action g (x : E)) = U.action g (x : E)
    rw [← coordinateModuleProjection_action, cliffordCoefficientRange_projection]⟩
  invFun x := ⟨U.action g⁻¹ (x : E), by
    change coordinateModuleProjection (B := B) k (U.action g⁻¹ (x : E)) = U.action g⁻¹ (x : E)
    rw [← coordinateModuleProjection_action, cliffordCoefficientRange_projection]⟩
  left_inv x := by apply Subtype.ext; exact U.inv_apply_apply g _
  right_inv x := by apply Subtype.ext; exact U.apply_inv_apply g _
  map_add' x y := by apply Subtype.ext; exact (U.action g).map_add _ _
  map_smul' c x := by apply Subtype.ext; exact (U.action g).map_smul _ _
  norm_map' x := (U.action g).norm_map (x : E)

@[simp] theorem cliffordRangeActionIsometry_coe {β : CStarAlgebraAction Γ B}
    (U : EquivariantHilbertModule (cliffordCoefficientAction β) E)
    (k : Bool) (g : Γ) (x : CliffordCoefficientRange B E k) :
    (cliffordRangeActionIsometry U k g x : E) = U.action g (x : E) := rfl

/-- The restricted action obeys the genuine B-valued inner-product law. -/
def cliffordRangeAction {β : CStarAlgebraAction Γ B}
    (U : EquivariantHilbertModule (cliffordCoefficientAction β) E)
    (k : Bool) : EquivariantHilbertModule β (CliffordCoefficientRange B E k) where
  action :=
    { toFun := cliffordRangeActionIsometry U k
      map_one' := by
        apply LinearIsometryEquiv.ext
        intro x
        apply Subtype.ext
        exact U.one_apply _
      map_mul' g h := by
        apply LinearIsometryEquiv.ext
        intro x
        apply Subtype.ext
        exact U.mul_apply g h _ }
  inner_action g x y := by
    change cliffordCoordinateExtraction k ⟪U.action g (x : E), U.action g (y : E)⟫_((B × B)ᵐᵒᵖ) = _
    rw [U.inner_action, cliffordCoordinateExtraction_action]
    rfl

@[simp] theorem cliffordRangeAction_coe {β : CStarAlgebraAction Γ B}
    (U : EquivariantHilbertModule (cliffordCoefficientAction β) E)
    (k : Bool) (g : Γ) (x : CliffordCoefficientRange B E k) :
    ((cliffordRangeAction U k).action g x : E) = U.action g (x : E) := rfl

/-- Restriction intertwines the actual conjugation actions on operators. -/
theorem cliffordRangeRestriction_conjugate {β : CStarAlgebraAction Γ B}
    (U : EquivariantHilbertModule (cliffordCoefficientAction β) E)
    (k : Bool) (g : Γ) (T : AdjointableMap (B × B) E E) :
    cliffordRangeRestriction k (U.conjugateOperator g T) =
      (cliffordRangeAction U k).conjugateOperator g (cliffordRangeRestriction k T) := by
  apply AdjointableMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- The module grading is a genuine B-unitary equivalence between the ranges. -/
def cliffordRangeGradingEquiv
    (γ : GradedHilbertModule (cliffordCoefficientGrading : CStarGrading (B × B)) E)
    (k : Bool) : HilbertModuleEquiv B (CliffordCoefficientRange B E k)
      (CliffordCoefficientRange B E (!k)) where
  linearIsometryEquiv :=
    { toFun x := ⟨γ.grading (x : E), by
        change coordinateModuleProjection (B := B) (!k) (γ.grading (x : E)) = γ.grading (x : E)
        rw [← coordinateModuleProjection_grading, cliffordCoefficientRange_projection]⟩
      invFun x := ⟨γ.grading (x : E), by
        change coordinateModuleProjection (B := B) k (γ.grading (x : E)) = γ.grading (x : E)
        have h := coordinateModuleProjection_grading γ (!k) (x : E)
        simp only [Bool.not_not, cliffordCoefficientRange_projection] at h
        exact h.symm⟩
      left_inv x := by apply Subtype.ext; exact γ.grading_sq _
      right_inv x := by apply Subtype.ext; exact γ.grading_sq _
      map_add' x y := by apply Subtype.ext; exact γ.grading.map_add _ _
      map_smul' c x := by apply Subtype.ext; exact γ.grading.map_smul _ _
      norm_map' x := γ.grading.norm_map (x : E) }
  inner_map x y := by
    change cliffordCoordinateExtraction (!k) ⟪γ.grading (x : E), γ.grading (y : E)⟫_((B × B)ᵐᵒᵖ) = _
    rw [γ.inner_grading, cliffordCoordinateExtraction_grading]
    rfl

@[simp] theorem cliffordRangeGradingEquiv_coe
    (γ : GradedHilbertModule (cliffordCoefficientGrading : CStarGrading (B × B)) E)
    (k : Bool) (x : CliffordCoefficientRange B E k) :
    (cliffordRangeGradingEquiv γ k x : E) = γ.grading (x : E) := rfl

/-- An odd operator has the required minus sign between the two ranges. -/
theorem cliffordRangeGradingEquiv_odd
    (γ : GradedHilbertModule (cliffordCoefficientGrading : CStarGrading (B × B)) E)
    (k : Bool) {T : AdjointableMap (B × B) E E} (hT : γ.IsOdd γ T)
    (x : CliffordCoefficientRange B E k) :
    cliffordRangeGradingEquiv γ k (cliffordRangeRestriction k T x) =
      -(cliffordRangeRestriction (!k) T (cliffordRangeGradingEquiv γ k x)) := by
  apply Subtype.ext
  exact hT (x : E)

end GradingAndAction

section OddExtraction

variable {Γ A E : Type*} [Group Γ] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul (B × B)ᵐᵒᵖ E]
  [CStarModule (B × B)ᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

/-- Select an actual coordinate range of the Clifford-graded cycle. The
standard odd convention uses `k = true`, the +1 range of ε = (1,-1). -/
def cliffordExtractOddCycle (k : Bool)
    (c : GradedKasparovCycle α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading E) :
    OddKasparovCycle α β (CliffordCoefficientRange B E k) where
  countablyGenerated := cliffordCoefficientRange_countablyGenerated k c.countablyGenerated
  groupAction := cliffordRangeAction c.groupAction k
  representation := (cliffordRangeRestrictionHom k).toNonUnitalStarAlgHom.comp c.representation
  representation_equivariant g a := by
    change (cliffordRangeAction c.groupAction k).conjugateOperator g
      (cliffordRangeRestriction k (c.representation a)) =
        cliffordRangeRestriction k (c.representation (α.automorphism g a))
    rw [← cliffordRangeRestriction_conjugate, c.representation_equivariant]
  operator := cliffordRangeRestriction k c.operator
  selfadjoint_mod_compact a := by
    change IsModuleCompact ((cliffordRangeRestriction k c.operator -
      star (cliffordRangeRestriction k c.operator)) * cliffordRangeRestriction k (c.representation a))
    simpa only [cliffordRangeRestriction_mul, cliffordRangeRestriction_sub,
      cliffordRangeRestriction_star] using
      cliffordRangeRestriction_isModuleCompact k (c.selfadjoint_mod_compact a)
  square_mod_compact a := by
    change IsModuleCompact ((cliffordRangeRestriction k c.operator *
      cliffordRangeRestriction k c.operator - 1) * cliffordRangeRestriction k (c.representation a))
    simpa only [cliffordRangeRestriction_mul, cliffordRangeRestriction_sub,
      cliffordRangeRestriction_one] using
      cliffordRangeRestriction_isModuleCompact k (c.square_mod_compact a)
  commutator_compact a := by
    change IsModuleCompact (cliffordRangeRestriction k c.operator *
      cliffordRangeRestriction k (c.representation a) -
        cliffordRangeRestriction k (c.representation a) * cliffordRangeRestriction k c.operator)
    simpa only [cliffordRangeRestriction_mul, cliffordRangeRestriction_sub,
      CStarGrading.trivial_apply] using
      cliffordRangeRestriction_isModuleCompact k (c.commutator_compact a)
  equivariance_mod_compact g a := by
    change IsModuleCompact (((cliffordRangeAction c.groupAction k).conjugateOperator g
      (cliffordRangeRestriction k c.operator) - cliffordRangeRestriction k c.operator) *
        cliffordRangeRestriction k (c.representation a))
    simpa only [cliffordRangeRestriction_mul, cliffordRangeRestriction_sub,
      cliffordRangeRestriction_conjugate] using
      cliffordRangeRestriction_isModuleCompact k (c.equivariance_mod_compact g a)

/-- Exact degeneracy survives actual coefficient restriction. -/
theorem cliffordExtractOddCycle_isDegenerate (k : Bool)
    (c : GradedKasparovCycle α (cliffordCoefficientAction β)
      CStarGrading.trivial cliffordCoefficientGrading E) (hc : c.IsDegenerate) :
    (cliffordExtractOddCycle k c).IsDegenerate := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    have h := congrArg (cliffordRangeRestrictionHom (B := B) (E := E) k) (hc.1 a)
    change ((cliffordRangeRestriction k c.operator - star (cliffordRangeRestriction k c.operator)) *
      cliffordRangeRestriction k (c.representation a)) = 0
    change cliffordRangeRestriction k ((c.operator - star c.operator) * c.representation a) = 0 at h
    simpa only [cliffordRangeRestriction_mul, cliffordRangeRestriction_sub,
      cliffordRangeRestriction_star] using h
  · intro a
    have h := congrArg (cliffordRangeRestrictionHom (B := B) (E := E) k) (hc.2.1 a)
    change ((cliffordRangeRestriction k c.operator * cliffordRangeRestriction k c.operator - 1) *
      cliffordRangeRestriction k (c.representation a)) = 0
    change cliffordRangeRestriction k ((c.operator * c.operator - 1) * c.representation a) = 0 at h
    simpa only [cliffordRangeRestriction_mul, cliffordRangeRestriction_sub,
      cliffordRangeRestriction_one] using h
  · intro a
    have h := congrArg (cliffordRangeRestrictionHom (B := B) (E := E) k) (hc.2.2.1 a)
    change (cliffordRangeRestriction k c.operator * cliffordRangeRestriction k (c.representation a) -
      cliffordRangeRestriction k (c.representation a) * cliffordRangeRestriction k c.operator) = 0
    change cliffordRangeRestriction k
      (c.operator * c.representation a - c.representation (CStarGrading.trivial.automorphism a) * c.operator) = 0 at h
    simpa only [cliffordRangeRestriction_mul, cliffordRangeRestriction_sub,
      CStarGrading.trivial_apply] using h
  · intro g a
    have h := congrArg (cliffordRangeRestrictionHom (B := B) (E := E) k) (hc.2.2.2 g a)
    change (((cliffordRangeAction c.groupAction k).conjugateOperator g
      (cliffordRangeRestriction k c.operator) - cliffordRangeRestriction k c.operator) *
        cliffordRangeRestriction k (c.representation a)) = 0
    change cliffordRangeRestriction k
      ((c.groupAction.conjugateOperator g c.operator - c.operator) * c.representation a) = 0 at h
    simpa only [cliffordRangeRestriction_mul, cliffordRangeRestriction_sub,
      cliffordRangeRestriction_conjugate] using h

end OddExtraction
end BC4lean.KKTheory
