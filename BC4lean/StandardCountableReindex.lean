import BC4lean.StandardCountableCutoff
import BC4lean.HilbertModuleSum
import BC4lean.HilbertModuleEquiv
import Mathlib.Logic.Equiv.Nat

/-! # Coordinate embeddings and self-absorption of the genuine standard module

An injection of the countable coordinates induces an actual adjointable
isometry on H_B. Its adjoint restricts coefficient coordinates. Both maps are
constructed first on finite coefficient vectors, with bounds in the actual
coefficient-form norm, and then extended through the radical quotient and its
completion. Splitting the coordinates by ℕ ⊕ ℕ ≃ ℕ therefore gives the genuine
module unitary H_B ⊕ H_B ≅ H_B, including for nonunital B.

This is coordinate self-absorption. It does not assert the distinct stabilization
theorem E ⊕ H_B ≅ H_B for arbitrary countably generated E.
-/

noncomputable section
namespace BC4lean.KKTheory
open UniformSpace
open scoped InnerProductSpace

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Inject the actual finite coefficient coordinates. -/
def standardCountableEmbeddingLinear (f : ℕ ↪ ℕ) :
    StandardCountableVectors B →ₗ[ℂ] StandardCountableVectors B :=
  Finsupp.lmapDomain Bᵐᵒᵖ ℂ f

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem standardCountableEmbeddingLinear_apply (f : ℕ ↪ ℕ)
    (x : StandardCountableVectors B) :
    standardCountableEmbeddingLinear f x = x.embDomain f :=
  (Finsupp.embDomain_eq_mapDomain f x).symm

/-- Restrict the actual finite coefficient coordinates along an injection. -/
def standardCountableRestrictionLinear (f : ℕ ↪ ℕ) :
    StandardCountableVectors B →ₗ[ℂ] StandardCountableVectors B :=
  Finsupp.lcomapDomain f f.injective

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem standardCountableRestrictionLinear_apply (f : ℕ ↪ ℕ)
    (x : StandardCountableVectors B) (n : ℕ) :
    standardCountableRestrictionLinear f x n = x (f n) := rfl

/-- The finite coordinate maps satisfy the genuine coefficient adjoint identity. -/
theorem standardCountableFiniteEmbedding_inner (f : ℕ ↪ ℕ)
    (x y : StandardCountableVectors B) :
    standardCountableFiniteInner (standardCountableEmbeddingLinear f x) y =
      standardCountableFiniteInner x (standardCountableRestrictionLinear f y) := by
  simp only [standardCountableEmbeddingLinear_apply, standardCountableFiniteInner,
    Finsupp.sum_embDomain, standardCountableRestrictionLinear_apply]

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem standardCountableRestriction_embedding (f : ℕ ↪ ℕ)
    (x : StandardCountableVectors B) :
    standardCountableRestrictionLinear f (standardCountableEmbeddingLinear f x) = x := by
  ext n
  simp only [standardCountableRestrictionLinear_apply, standardCountableEmbeddingLinear_apply,
    Finsupp.embDomain_apply_self]

theorem standardCountableFiniteEmbedding_inner_map (f : ℕ ↪ ℕ)
    (x y : StandardCountableVectors B) :
    standardCountableFiniteInner (standardCountableEmbeddingLinear f x)
      (standardCountableEmbeddingLinear f y) = standardCountableFiniteInner x y := by
  rw [standardCountableFiniteEmbedding_inner, standardCountableRestriction_embedding]

/-- Coordinate injection is isometric for the actual finite-vector form norm. -/
theorem standardCountableEmbedding_formNorm (f : ℕ ↪ ℕ) (x : StandardCountableVectors B) :
    PositiveModuleForm.formNorm (B := B) (standardCountableEmbeddingLinear f x) =
      PositiveModuleForm.formNorm (B := B) x := by
  simp only [PositiveModuleForm.formNorm, standardCountableFinite_inner,
    standardCountableFiniteEmbedding_inner_map]

/-- Restriction is contractive by the genuine form Cauchy--Schwarz inequality. -/
theorem standardCountableRestriction_formNorm_le (f : ℕ ↪ ℕ) (x : StandardCountableVectors B) :
    PositiveModuleForm.formNorm (B := B) (standardCountableRestrictionLinear f x) ≤
      1 * PositiveModuleForm.formNorm (B := B) x := by
  rw [one_mul]
  let y := standardCountableRestrictionLinear f x
  have hsq : (PositiveModuleForm.formNorm (B := B) y) ^ 2 ≤
      PositiveModuleForm.formNorm (B := B) y * PositiveModuleForm.formNorm (B := B) x := by
    rw [PositiveModuleForm.formNorm_sq]
    change ‖standardCountableFiniteInner y y‖ ≤ _
    rw [← standardCountableFiniteEmbedding_inner f y x]
    simpa only [standardCountableFinite_inner, standardCountableEmbedding_formNorm]
      using PositiveModuleForm.norm_inner_le (B := B) (standardCountableEmbeddingLinear f y) x
  by_contra h
  have hlt : PositiveModuleForm.formNorm (B := B) x < PositiveModuleForm.formNorm (B := B) y :=
    lt_of_not_ge h
  have hy : 0 < PositiveModuleForm.formNorm (B := B) y :=
    lt_of_le_of_lt (PositiveModuleForm.formNorm_nonneg x) hlt
  have hm := mul_lt_mul_of_pos_left hlt hy
  rw [← pow_two] at hm
  exact not_lt_of_ge hsq hm

/-- Coordinate inclusion and restriction on the normed finite-vector quotient. -/
def standardCountableQuotientEmbedding (f : ℕ ↪ ℕ) :
    AdjointableMap B (StandardCountablePreModule B) (StandardCountablePreModule B) where
  toCLM := positiveModuleQuotientLiftCLM (standardCountableEmbeddingLinear f) (K := 1)
    (fun x => by rw [standardCountableEmbedding_formNorm]; simp only [one_mul, le_refl])
  adjointCLM := positiveModuleQuotientLiftCLM (standardCountableRestrictionLinear f)
    (standardCountableRestriction_formNorm_le f)
  adjoint_identity q r := by
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
    obtain ⟨y, rfl⟩ := positiveModuleQuotientMk_surjective r
    rw [positiveModuleQuotientLiftCLM_mk, positiveModuleQuotientLiftCLM_mk,
      PositiveModuleQuotient.inner_mk, PositiveModuleQuotient.inner_mk]
    exact standardCountableFiniteEmbedding_inner f x y

/-- The actual completed coordinate embedding, with the proved restriction adjoint. -/
def standardCountableEmbedding (f : ℕ ↪ ℕ) :
    AdjointableMap B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B) :=
  (standardCountableQuotientEmbedding f).completion

@[simp] theorem standardCountableEmbedding_mk (f : ℕ ↪ ℕ) (x : StandardCountableVectors B) :
    standardCountableEmbedding f (standardCountableMk x) =
      standardCountableMk (standardCountableEmbeddingLinear f x) := by
  rw [standardCountableMk_apply, standardCountableEmbedding, AdjointableMap.completion_apply_coe,
    standardCountableMk_apply]
  rfl

@[simp] theorem standardCountableEmbedding_adjoint_mk (f : ℕ ↪ ℕ) (x : StandardCountableVectors B) :
    (standardCountableEmbedding f).adjoint (standardCountableMk x) =
      standardCountableMk (standardCountableRestrictionLinear f x) := by
  rw [standardCountableMk_apply, standardCountableEmbedding, AdjointableMap.completion_adjoint,
    AdjointableMap.completion_apply_coe, standardCountableMk_apply]
  rfl

@[simp] theorem standardCountableEmbedding_adjoint_comp_self (f : ℕ ↪ ℕ) :
    (standardCountableEmbedding (B := B) f).adjoint.comp (standardCountableEmbedding f) =
      AdjointableMap.id := by
  apply standardCountable_adjointable_ext_mk
  intro x
  simp only [AdjointableMap.comp_apply, standardCountableEmbedding_mk,
    standardCountableEmbedding_adjoint_mk, standardCountableRestriction_embedding,
    AdjointableMap.id_apply]

/-- The completed coordinate map preserves the actual coefficient-valued inner product. -/
theorem standardCountableEmbedding_inner (f : ℕ ↪ ℕ) (x y : StandardCountableHilbertModule B) :
    ⟪standardCountableEmbedding f x, standardCountableEmbedding f y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) := by
  rw [(standardCountableEmbedding (B := B) f).adjoint_identity]
  change ⟪x, (standardCountableEmbedding f).adjoint (standardCountableEmbedding f y)⟫_(Bᵐᵒᵖ) = _
  have h := congrArg (fun T : AdjointableMap B (StandardCountableHilbertModule B)
    (StandardCountableHilbertModule B) => T y) (standardCountableEmbedding_adjoint_comp_self f)
  simpa only [AdjointableMap.comp_apply, AdjointableMap.id_apply] using congrArg
    (fun z : StandardCountableHilbertModule B => ⟪x, z⟫_(Bᵐᵒᵖ)) h

@[simp] theorem standardCountableEmbedding_norm (f : ℕ ↪ ℕ) (x : StandardCountableHilbertModule B) :
    ‖standardCountableEmbedding f x‖ = ‖x‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) (standardCountableEmbedding f x),
    standardCountableEmbedding_inner]
  exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm

theorem norm_standardCountableEmbedding_le (f : ℕ ↪ ℕ) :
    ‖standardCountableEmbedding (B := B) f‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖standardCountableEmbedding (B := B) f x‖ ≤ 1 * ‖x‖
  rw [standardCountableEmbedding_norm, one_mul]

/-- Evaluation in an injected coordinate recovers the actual original coefficient. -/
@[simp] theorem standardCountableEvaluation_embedding (f : ℕ ↪ ℕ)
    (x : StandardCountableHilbertModule B) (n : ℕ) :
    standardCountableEvaluation (f n) (standardCountableEmbedding f x) =
      standardCountableEvaluation n x := by
  have h := (standardCountableMk_denseRange (B := B)).equalizer
    ((standardCountableEvaluation (B := B) (f n)).toCLM.continuous.comp
      (standardCountableEmbedding (B := B) f).toCLM.continuous)
    (standardCountableEvaluation (B := B) n).toCLM.continuous (by
      funext y
      simp only [Function.comp_def, standardCountableEmbedding_mk, standardCountableEvaluation_mk,
        standardCountableEmbeddingLinear_apply, Finsupp.embDomain_apply_self])
  exact congrFun h x

private def standardSumLeftEmbedding (e : ℕ ⊕ ℕ ≃ ℕ) : ℕ ↪ ℕ :=
  Function.Embedding.inl.trans e.toEmbedding

private def standardSumRightEmbedding (e : ℕ ⊕ ℕ ≃ ℕ) : ℕ ↪ ℕ :=
  Function.Embedding.inr.trans e.toEmbedding

private theorem standardSumLeft_not_right (e : ℕ ⊕ ℕ ≃ ℕ) (n : ℕ) :
    standardSumLeftEmbedding e n ∉ Set.range (standardSumRightEmbedding e) := by
  rintro ⟨m, hm⟩
  have he : Sum.inr m = Sum.inl n := e.injective hm
  cases he

private theorem standardSumRight_not_left (e : ℕ ⊕ ℕ ≃ ℕ) (n : ℕ) :
    standardSumRightEmbedding e n ∉ Set.range (standardSumLeftEmbedding e) := by
  rintro ⟨m, hm⟩
  have he : Sum.inl m = Sum.inr n := e.injective hm
  cases he

omit [PartialOrder B] [StarOrderedRing B] in
theorem standardCountableRestriction_cross (f g : ℕ ↪ ℕ)
    (h : ∀ n, f n ∉ Set.range g) (x : StandardCountableVectors B) :
    standardCountableRestrictionLinear f (standardCountableEmbeddingLinear g x) = 0 := by
  ext n
  simp only [standardCountableRestrictionLinear_apply, standardCountableEmbeddingLinear_apply,
    Finsupp.zero_apply]
  exact Finsupp.embDomain_of_notMem_range g x (f n) (h n)

/-- Disjoint coordinate injections have zero rectangular adjoint composition. -/
theorem standardCountableEmbedding_adjoint_comp_eq_zero (f g : ℕ ↪ ℕ)
    (h : ∀ n, f n ∉ Set.range g) :
    (standardCountableEmbedding (B := B) f).adjoint.comp (standardCountableEmbedding g) = 0 := by
  apply standardCountable_adjointable_ext_mk
  intro x
  simp only [AdjointableMap.comp_apply, standardCountableEmbedding_mk,
    standardCountableEmbedding_adjoint_mk, standardCountableRestriction_cross f g h,
    map_zero, AdjointableMap.coe_zero_apply]

/-- Disjoint injected coordinate ranges are orthogonal for the actual coefficient form. -/
theorem standardCountableEmbedding_inner_eq_zero (f g : ℕ ↪ ℕ)
    (h : ∀ n, f n ∉ Set.range g) (x y : StandardCountableHilbertModule B) :
    ⟪standardCountableEmbedding f x, standardCountableEmbedding g y⟫_(Bᵐᵒᵖ) = 0 := by
  rw [(standardCountableEmbedding (B := B) f).adjoint_identity]
  change ⟪x, (standardCountableEmbedding (B := B) f).adjoint
    (standardCountableEmbedding (B := B) g y)⟫_(Bᵐᵒᵖ) = 0
  rw [← AdjointableMap.comp_apply, standardCountableEmbedding_adjoint_comp_eq_zero f g h,
    AdjointableMap.coe_zero_apply]
  exact CStarModule.inner_zero_right (A := Bᵐᵒᵖ) (x := x)

/-- Coordinate inclusion is transported to the actual injected coordinate. -/
@[simp] theorem standardCountableEmbedding_inclusion (f : ℕ ↪ ℕ) (n : ℕ) (b : Bᵐᵒᵖ) :
    standardCountableEmbedding f (standardCountableInclusion n b) =
      standardCountableInclusion (f n) b := by
  simp only [standardCountableInclusion_apply, standardCountableEmbedding_mk,
    standardCountableEmbeddingLinear_apply, Finsupp.embDomain_eq_mapDomain,
    Finsupp.mapDomain_single]

omit [PartialOrder B] [StarOrderedRing B] in
private theorem standardCountableSum_recompose (e : ℕ ⊕ ℕ ≃ ℕ) (x : StandardCountableVectors B) :
    standardCountableEmbeddingLinear (standardSumLeftEmbedding e)
        (standardCountableRestrictionLinear (standardSumLeftEmbedding e) x) +
      standardCountableEmbeddingLinear (standardSumRightEmbedding e)
        (standardCountableRestrictionLinear (standardSumRightEmbedding e) x) = x := by
  ext k
  obtain ⟨n | n, rfl⟩ := e.surjective k
  · simp only [Finsupp.add_apply, standardCountableEmbeddingLinear_apply]
    change ((standardCountableRestrictionLinear (standardSumLeftEmbedding e) x).embDomain
        (standardSumLeftEmbedding e)) (standardSumLeftEmbedding e n) +
      ((standardCountableRestrictionLinear (standardSumRightEmbedding e) x).embDomain
        (standardSumRightEmbedding e)) (standardSumLeftEmbedding e n) =
      x (standardSumLeftEmbedding e n)
    rw [Finsupp.embDomain_apply_self,
      Finsupp.embDomain_of_notMem_range _ _ _ (standardSumLeft_not_right e n), add_zero]
    rfl
  · simp only [Finsupp.add_apply, standardCountableEmbeddingLinear_apply]
    change ((standardCountableRestrictionLinear (standardSumLeftEmbedding e) x).embDomain
        (standardSumLeftEmbedding e)) (standardSumRightEmbedding e n) +
      ((standardCountableRestrictionLinear (standardSumRightEmbedding e) x).embDomain
        (standardSumRightEmbedding e)) (standardSumRightEmbedding e n) =
      x (standardSumRightEmbedding e n)
    rw [Finsupp.embDomain_of_notMem_range _ _ _ (standardSumRight_not_left e n),
      Finsupp.embDomain_apply_self, zero_add]
    rfl

/-- Join two actual standard modules by disjoint coordinate injections. -/
def standardCountableInterleave (e : ℕ ⊕ ℕ ≃ ℕ) :
    AdjointableMap B (HilbertModuleSum B (StandardCountableHilbertModule B)
      (StandardCountableHilbertModule B)) (StandardCountableHilbertModule B) :=
  (standardCountableEmbedding (B := B) (standardSumLeftEmbedding e)).comp
      (sumFst (B := B) (E := StandardCountableHilbertModule B)
        (F := StandardCountableHilbertModule B)) +
    (standardCountableEmbedding (B := B) (standardSumRightEmbedding e)).comp
      (sumSnd (B := B) (E := StandardCountableHilbertModule B)
        (F := StandardCountableHilbertModule B))

@[simp] theorem standardCountableInterleave_apply (e : ℕ ⊕ ℕ ≃ ℕ)
    (x : HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) :
    standardCountableInterleave e x =
      standardCountableEmbedding (standardSumLeftEmbedding e) x.fst +
        standardCountableEmbedding (standardSumRightEmbedding e) x.snd := rfl

@[simp] theorem standardCountableInterleave_adjoint_apply (e : ℕ ⊕ ℕ ≃ ℕ)
    (x : StandardCountableHilbertModule B) :
    (standardCountableInterleave e).adjoint x =
      sumMk ((standardCountableEmbedding (standardSumLeftEmbedding e)).adjoint x)
        ((standardCountableEmbedding (standardSumRightEmbedding e)).adjoint x) := by
  apply Prod.ext
  · change (standardCountableEmbedding (B := B) (standardSumLeftEmbedding e)).adjoint x + 0 = _
    exact add_zero _
  · change 0 + (standardCountableEmbedding (B := B) (standardSumRightEmbedding e)).adjoint x = _
    exact zero_add _

@[simp] theorem standardCountableInterleave_mk (e : ℕ ⊕ ℕ ≃ ℕ)
    (x y : StandardCountableVectors B) :
    standardCountableInterleave e (sumMk (standardCountableMk x) (standardCountableMk y)) =
      standardCountableMk (standardCountableEmbeddingLinear (standardSumLeftEmbedding e) x +
        standardCountableEmbeddingLinear (standardSumRightEmbedding e) y) := by
  simp only [standardCountableInterleave_apply, sumMk_fst, sumMk_snd,
    standardCountableEmbedding_mk, map_add]

private theorem standardCountableSumMk_denseRange :
    DenseRange (fun p : StandardCountableVectors B × StandardCountableVectors B =>
      sumMk (B := B) (standardCountableMk p.1) (standardCountableMk p.2)) := by
  let e := (WithCStarModule.equivL ℂ (A := Bᵐᵒᵖ)
    (E := StandardCountableHilbertModule B × StandardCountableHilbertModule B)).symm
  exact e.surjective.denseRange.comp
    (standardCountableMk_denseRange.prodMap standardCountableMk_denseRange) e.continuous

@[simp] theorem standardCountableInterleave_adjoint_comp_self (e : ℕ ⊕ ℕ ≃ ℕ) :
    (standardCountableInterleave (B := B) e).adjoint.comp (standardCountableInterleave e) =
      AdjointableMap.id := by
  apply AdjointableMap.ext
  intro x
  have he := (standardCountableSumMk_denseRange (B := B)).equalizer
    (((standardCountableInterleave (B := B) e).adjoint.comp
      (standardCountableInterleave e)).toCLM.continuous)
    (AdjointableMap.id (B := B)
      (E := HilbertModuleSum B (StandardCountableHilbertModule B)
        (StandardCountableHilbertModule B))).toCLM.continuous (by
      funext p
      simp only [Function.comp_def, AdjointableMap.comp_apply, standardCountableInterleave_mk,
        standardCountableInterleave_adjoint_apply, standardCountableEmbedding_adjoint_mk,
        map_add, standardCountableRestriction_embedding, AdjointableMap.id_apply]
      rw [standardCountableRestriction_cross _ _ (standardSumLeft_not_right e),
        standardCountableRestriction_cross _ _ (standardSumRight_not_left e)]
      simp only [map_zero, sumMk_add, add_zero, zero_add])
  exact congrFun he x

@[simp] theorem standardCountableInterleave_comp_adjoint (e : ℕ ⊕ ℕ ≃ ℕ) :
    (standardCountableInterleave (B := B) e).comp (standardCountableInterleave e).adjoint =
      AdjointableMap.id := by
  apply standardCountable_adjointable_ext_mk
  intro x
  simp only [AdjointableMap.comp_apply, standardCountableInterleave_adjoint_apply,
    standardCountableEmbedding_adjoint_mk, standardCountableInterleave_mk,
    standardCountableSum_recompose, AdjointableMap.id_apply]

theorem standardCountableInterleave_inner (e : ℕ ⊕ ℕ ≃ ℕ)
    (x y : HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) :
    ⟪standardCountableInterleave e x, standardCountableInterleave e y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) := by
  rw [(standardCountableInterleave (B := B) e).adjoint_identity]
  change ⟪x, (standardCountableInterleave e).adjoint (standardCountableInterleave e y)⟫_(Bᵐᵒᵖ) = _
  have h := congrArg (fun T : AdjointableMap B
    (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
    (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) => T y)
      (standardCountableInterleave_adjoint_comp_self e)
  simpa only [AdjointableMap.comp_apply, AdjointableMap.id_apply] using congrArg
    (fun z : HilbertModuleSum B (StandardCountableHilbertModule B)
      (StandardCountableHilbertModule B) => ⟪x, z⟫_(Bᵐᵒᵖ)) h

/-- The standard module's genuine coordinate self-absorption unitary. -/
def standardCountableSumEquiv (e : ℕ ⊕ ℕ ≃ ℕ) :
    HilbertModuleEquiv B (HilbertModuleSum B (StandardCountableHilbertModule B)
      (StandardCountableHilbertModule B)) (StandardCountableHilbertModule B) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun := standardCountableInterleave (B := B) e
          invFun := (standardCountableInterleave (B := B) e).adjoint
          left_inv := fun x => by
            simpa only [AdjointableMap.comp_apply, AdjointableMap.id_apply] using
              congrArg (fun T => T x) (standardCountableInterleave_adjoint_comp_self e)
          right_inv := fun x => by
            simpa only [AdjointableMap.comp_apply, AdjointableMap.id_apply] using
              congrArg (fun T => T x) (standardCountableInterleave_comp_adjoint e)
          map_add' := (standardCountableInterleave (B := B) e).toCLM.map_add
          map_smul' := (standardCountableInterleave (B := B) e).toCLM.map_smul }
      norm_map' x := by
        change ‖standardCountableInterleave e x‖ = ‖x‖
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) (standardCountableInterleave e x),
          standardCountableInterleave_inner]
        exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm }
  inner_map := standardCountableInterleave_inner e

/-- Explicitly interleave the even and odd coefficient coordinates. -/
def standardCountableSelfAbsorption :
    HilbertModuleEquiv B (HilbertModuleSum B (StandardCountableHilbertModule B)
      (StandardCountableHilbertModule B)) (StandardCountableHilbertModule B) :=
  standardCountableSumEquiv Equiv.natSumNatEquivNat

end BC4lean.KKTheory
