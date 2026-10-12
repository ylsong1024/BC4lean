import BC4lean.OddKTheoryCountableDiagonal
import Mathlib.Logic.Equiv.Nat

/-! # Actual coordinate embeddings of countable row-module sums

Coordinate injection and restriction are extended from finite row vectors
through the genuine coefficient-form quotient and completion. These actual
row-module maps commute with every coordinatewise adjointable coefficient
operator. Their ranges are not declared compact.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

abbrev OddKTheoryCountableOperator (B E : Type*) [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] :=
  AdjointableMap B (CountableHilbertModuleSum B E) (CountableHilbertModuleSum B E)

omit [CompleteSpace E] in
/-- Genuine finite row vectors determine completed-module operators. -/
theorem oddKTheoryCountableOperator_ext_mk
    (S T : OddKTheoryCountableOperator B E)
    (h : ∀ x : CountableModuleVectors E,
      S (countableModuleMk (B := B) x) = T (countableModuleMk (B := B) x)) : S = T := by
  apply AdjointableMap.toCLM_injective
  apply ContinuousLinearMap.coeFn_injective
  exact (countableModuleMk_denseRange (B := B) (E := E)).equalizer
    S.toCLM.continuous T.toCLM.continuous (funext h)

/-- Inject the actual finite coefficient coordinates. -/
def oddKTheoryCountableEmbeddingLinear (f : ℕ ↪ ℕ) :
    CountableModuleVectors E →ₗ[ℂ] CountableModuleVectors E :=
  Finsupp.lmapDomain E ℂ f

omit [CompleteSpace E] in
@[simp] theorem oddKTheoryCountableEmbeddingLinear_apply (f : ℕ ↪ ℕ)
    (x : CountableModuleVectors E) :
    oddKTheoryCountableEmbeddingLinear f x = x.embDomain f :=
  (Finsupp.embDomain_eq_mapDomain f x).symm

/-- Restrict the actual finite coefficient coordinates along an injection. -/
def oddKTheoryCountableRestrictionLinear (f : ℕ ↪ ℕ) :
    CountableModuleVectors E →ₗ[ℂ] CountableModuleVectors E :=
  Finsupp.lcomapDomain f f.injective

omit [CompleteSpace E] in
@[simp] theorem oddKTheoryCountableRestrictionLinear_apply (f : ℕ ↪ ℕ)
    (x : CountableModuleVectors E) (n : ℕ) :
    oddKTheoryCountableRestrictionLinear f x n = x (f n) := rfl

omit [StarOrderedRing B] [CompleteSpace E] in
/-- The finite coordinate maps satisfy the genuine coefficient adjoint identity. -/
theorem oddKTheoryCountableFiniteEmbedding_inner (f : ℕ ↪ ℕ)
    (x y : CountableModuleVectors E) :
    countableModuleFiniteInner (B := B) (oddKTheoryCountableEmbeddingLinear f x) y =
      countableModuleFiniteInner (B := B) x (oddKTheoryCountableRestrictionLinear f y) := by
  simp only [oddKTheoryCountableEmbeddingLinear_apply, countableModuleFiniteInner,
    Finsupp.sum_embDomain, oddKTheoryCountableRestrictionLinear_apply]

omit [CompleteSpace E] in
@[simp] theorem oddKTheoryCountableRestriction_embedding (f : ℕ ↪ ℕ)
    (x : CountableModuleVectors E) :
    oddKTheoryCountableRestrictionLinear f (oddKTheoryCountableEmbeddingLinear f x) = x := by
  ext n
  simp only [oddKTheoryCountableRestrictionLinear_apply, oddKTheoryCountableEmbeddingLinear_apply,
    Finsupp.embDomain_apply_self]

omit [StarOrderedRing B] [CompleteSpace E] in
theorem oddKTheoryCountableFiniteEmbedding_inner_map (f : ℕ ↪ ℕ)
    (x y : CountableModuleVectors E) :
    countableModuleFiniteInner (B := B) (oddKTheoryCountableEmbeddingLinear f x)
      (oddKTheoryCountableEmbeddingLinear f y) = countableModuleFiniteInner (B := B) x y := by
  rw [oddKTheoryCountableFiniteEmbedding_inner, oddKTheoryCountableRestriction_embedding]

omit [CompleteSpace E] in
/-- Coordinate injection is isometric for the actual finite-vector form norm. -/
theorem oddKTheoryCountableEmbedding_formNorm (f : ℕ ↪ ℕ) (x : CountableModuleVectors E) :
    PositiveModuleForm.formNorm (B := B) (oddKTheoryCountableEmbeddingLinear f x) =
      PositiveModuleForm.formNorm (B := B) x := by
  simp only [PositiveModuleForm.formNorm, countableModuleFinite_inner,
    oddKTheoryCountableFiniteEmbedding_inner_map]

omit [CompleteSpace E] in
/-- Restriction is contractive by the genuine form Cauchy--Schwarz inequality. -/
theorem oddKTheoryCountableRestriction_formNorm_le (f : ℕ ↪ ℕ) (x : CountableModuleVectors E) :
    PositiveModuleForm.formNorm (B := B) (oddKTheoryCountableRestrictionLinear f x) ≤
      1 * PositiveModuleForm.formNorm (B := B) x := by
  rw [one_mul]
  let y := oddKTheoryCountableRestrictionLinear f x
  have hsq : (PositiveModuleForm.formNorm (B := B) y) ^ 2 ≤
      PositiveModuleForm.formNorm (B := B) y * PositiveModuleForm.formNorm (B := B) x := by
    rw [PositiveModuleForm.formNorm_sq]
    change ‖countableModuleFiniteInner (B := B) y y‖ ≤ _
    rw [← oddKTheoryCountableFiniteEmbedding_inner f y x]
    simpa only [countableModuleFinite_inner, oddKTheoryCountableEmbedding_formNorm]
      using PositiveModuleForm.norm_inner_le (B := B) (oddKTheoryCountableEmbeddingLinear f y) x
  by_contra h
  have hlt : PositiveModuleForm.formNorm (B := B) x < PositiveModuleForm.formNorm (B := B) y :=
    lt_of_not_ge h
  have hy : 0 < PositiveModuleForm.formNorm (B := B) y :=
    lt_of_le_of_lt (PositiveModuleForm.formNorm_nonneg x) hlt
  have hm := mul_lt_mul_of_pos_left hlt hy
  rw [← pow_two] at hm
  exact not_lt_of_ge hsq hm

/-- Coordinate inclusion and restriction on the normed finite-vector quotient. -/
def oddKTheoryCountableQuotientEmbedding (f : ℕ ↪ ℕ) :
    AdjointableMap B (CountableHilbertModulePreSum B E) (CountableHilbertModulePreSum B E) where
  toCLM := positiveModuleQuotientLiftCLM (oddKTheoryCountableEmbeddingLinear f) (K := 1)
    (fun x => by rw [oddKTheoryCountableEmbedding_formNorm]; simp only [one_mul, le_refl])
  adjointCLM := positiveModuleQuotientLiftCLM (oddKTheoryCountableRestrictionLinear f)
    (oddKTheoryCountableRestriction_formNorm_le f)
  adjoint_identity q r := by
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
    obtain ⟨y, rfl⟩ := positiveModuleQuotientMk_surjective r
    rw [positiveModuleQuotientLiftCLM_mk, positiveModuleQuotientLiftCLM_mk,
      PositiveModuleQuotient.inner_mk, PositiveModuleQuotient.inner_mk]
    exact oddKTheoryCountableFiniteEmbedding_inner f x y

/-- The actual completed coordinate embedding, with the proved restriction adjoint. -/
def oddKTheoryCountableEmbedding (f : ℕ ↪ ℕ) :
    AdjointableMap B (CountableHilbertModuleSum B E) (CountableHilbertModuleSum B E) :=
  (oddKTheoryCountableQuotientEmbedding f).completion

omit [CompleteSpace E] in
@[simp] theorem oddKTheoryCountableEmbedding_mk (f : ℕ ↪ ℕ) (x : CountableModuleVectors E) :
    oddKTheoryCountableEmbedding f (countableModuleMk (B := B) x) =
      countableModuleMk (B := B) (oddKTheoryCountableEmbeddingLinear f x) := by
  rw [countableModuleMk_apply, oddKTheoryCountableEmbedding, AdjointableMap.completion_apply_coe,
    countableModuleMk_apply]
  rfl

omit [CompleteSpace E] in
@[simp] theorem oddKTheoryCountableEmbedding_adjoint_mk (f : ℕ ↪ ℕ) (x : CountableModuleVectors E) :
    (oddKTheoryCountableEmbedding f).adjoint (countableModuleMk (B := B) x) =
      countableModuleMk (B := B) (oddKTheoryCountableRestrictionLinear f x) := by
  rw [countableModuleMk_apply, oddKTheoryCountableEmbedding, AdjointableMap.completion_adjoint,
    AdjointableMap.completion_apply_coe, countableModuleMk_apply]
  rfl

omit [CompleteSpace E] in
@[simp] theorem oddKTheoryCountableEmbedding_adjoint_comp_self (f : ℕ ↪ ℕ) :
    (oddKTheoryCountableEmbedding (B := B) (E := E) f).adjoint.comp
      (oddKTheoryCountableEmbedding (B := B) (E := E) f) =
      AdjointableMap.id := by
  apply oddKTheoryCountableOperator_ext_mk (B := B) (E := E)
  intro x
  simp only [AdjointableMap.comp_apply, oddKTheoryCountableEmbedding_mk,
    oddKTheoryCountableEmbedding_adjoint_mk, oddKTheoryCountableRestriction_embedding,
    AdjointableMap.id_apply]

omit [CompleteSpace E] in
/-- The completed coordinate map preserves the actual coefficient-valued inner product. -/
theorem oddKTheoryCountableEmbedding_inner (f : ℕ ↪ ℕ) (x y : CountableHilbertModuleSum B E) :
    ⟪oddKTheoryCountableEmbedding f x, oddKTheoryCountableEmbedding f y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) := by
  rw [(oddKTheoryCountableEmbedding (B := B) f).adjoint_identity]
  change ⟪x, (oddKTheoryCountableEmbedding f).adjoint (oddKTheoryCountableEmbedding f y)⟫_(Bᵐᵒᵖ) = _
  have h := congrArg (fun T : AdjointableMap B (CountableHilbertModuleSum B E)
    (CountableHilbertModuleSum B E) => T y)
      (oddKTheoryCountableEmbedding_adjoint_comp_self (B := B) (E := E) f)
  simpa only [AdjointableMap.comp_apply, AdjointableMap.id_apply] using congrArg
    (fun z : CountableHilbertModuleSum B E => ⟪x, z⟫_(Bᵐᵒᵖ)) h

omit [CompleteSpace E] in
@[simp] theorem oddKTheoryCountableEmbedding_norm (f : ℕ ↪ ℕ) (x : CountableHilbertModuleSum B E) :
    ‖oddKTheoryCountableEmbedding f x‖ = ‖x‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) (oddKTheoryCountableEmbedding f x),
    oddKTheoryCountableEmbedding_inner]
  exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm

omit [CompleteSpace E] in
theorem norm_oddKTheoryCountableEmbedding_le (f : ℕ ↪ ℕ) :
    ‖oddKTheoryCountableEmbedding (B := B) (E := E) f‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound
    (oddKTheoryCountableEmbedding (B := B) (E := E) f).toCLM zero_le_one
  intro x
  simp only [oddKTheoryCountableEmbedding_norm, one_mul, le_refl]

/-- Evaluation in an injected coordinate recovers the actual original coefficient. -/
@[simp] theorem oddKTheoryCountableEvaluation_embedding (f : ℕ ↪ ℕ)
    (x : CountableHilbertModuleSum B E) (n : ℕ) :
    countableModuleEvaluation (B := B) (f n) (oddKTheoryCountableEmbedding f x) =
      countableModuleEvaluation (B := B) n x := by
  have h := (countableModuleMk_denseRange (B := B) (E := E)).equalizer
    ((countableModuleEvaluation (B := B) (f n)).toCLM.continuous.comp
      (oddKTheoryCountableEmbedding f).toCLM.continuous)
    (countableModuleEvaluation (B := B) n).toCLM.continuous (by
      funext y
      change countableModuleEvaluation (B := B) (f n)
          (oddKTheoryCountableEmbedding (B := B) (E := E) f (countableModuleMk (B := B) y)) =
        countableModuleEvaluation (B := B) n (countableModuleMk (B := B) y)
      simp only [oddKTheoryCountableEmbedding_mk, countableModuleEvaluation_mk,
        oddKTheoryCountableEmbeddingLinear_apply, Finsupp.embDomain_apply_self])
  exact congrFun h x

omit [CompleteSpace E] in
theorem oddKTheoryCountableRestriction_cross (f g : ℕ ↪ ℕ)
    (h : ∀ n, f n ∉ Set.range g) (x : CountableModuleVectors E) :
    oddKTheoryCountableRestrictionLinear f (oddKTheoryCountableEmbeddingLinear g x) = 0 := by
  ext n
  simp only [oddKTheoryCountableRestrictionLinear_apply, oddKTheoryCountableEmbeddingLinear_apply,
    Finsupp.zero_apply]
  exact Finsupp.embDomain_of_notMem_range g x (f n) (h n)

omit [CompleteSpace E] in
/-- Disjoint coordinate injections have zero rectangular adjoint composition. -/
theorem oddKTheoryCountableEmbedding_adjoint_comp_eq_zero (f g : ℕ ↪ ℕ)
    (h : ∀ n, f n ∉ Set.range g) :
    (oddKTheoryCountableEmbedding (B := B) (E := E) f).adjoint.comp
      (oddKTheoryCountableEmbedding (B := B) (E := E) g) = 0 := by
  apply oddKTheoryCountableOperator_ext_mk (B := B) (E := E)
  intro x
  simp only [AdjointableMap.comp_apply, oddKTheoryCountableEmbedding_mk,
    oddKTheoryCountableEmbedding_adjoint_mk, oddKTheoryCountableRestriction_cross f g h,
    map_zero, AdjointableMap.coe_zero_apply]

omit [CompleteSpace E] in
/-- Disjoint injected coordinate ranges are orthogonal for the actual coefficient form. -/
theorem oddKTheoryCountableEmbedding_inner_eq_zero (f g : ℕ ↪ ℕ)
    (h : ∀ n, f n ∉ Set.range g) (x y : CountableHilbertModuleSum B E) :
    ⟪oddKTheoryCountableEmbedding f x, oddKTheoryCountableEmbedding g y⟫_(Bᵐᵒᵖ) = 0 := by
  rw [(oddKTheoryCountableEmbedding (B := B) (E := E) f).adjoint_identity]
  change ⟪x, (oddKTheoryCountableEmbedding (B := B) (E := E) f).adjoint
    (oddKTheoryCountableEmbedding (B := B) (E := E) g y)⟫_(Bᵐᵒᵖ) = 0
  rw [← AdjointableMap.comp_apply,
    oddKTheoryCountableEmbedding_adjoint_comp_eq_zero (B := B) (E := E) f g h,
    AdjointableMap.coe_zero_apply]
  exact CStarModule.inner_zero_right (A := Bᵐᵒᵖ) (E := CountableHilbertModuleSum B E) (x := x)

/-- Coordinate inclusion is transported to the actual injected coordinate. -/
@[simp] theorem oddKTheoryCountableEmbedding_inclusion (f : ℕ ↪ ℕ) (n : ℕ) (b : E) :
    oddKTheoryCountableEmbedding f (countableModuleInclusion (B := B) n b) =
      countableModuleInclusion (B := B) (f n) b := by
  simp only [countableModuleInclusion_apply, oddKTheoryCountableEmbedding_mk,
    oddKTheoryCountableEmbeddingLinear_apply, Finsupp.embDomain_eq_mapDomain,
    Finsupp.mapDomain_single]


omit [StarOrderedRing B] [CompleteSpace E] in
/-- Reindexing finite row coordinates commutes exactly with every actual
coordinatewise coefficient operator. -/
theorem oddKTheoryCountableEmbeddingLinear_diagonal
    (f : ℕ ↪ ℕ) (S : AdjointableMap B E E) (x : CountableModuleVectors E) :
    oddKTheoryCountableEmbeddingLinear f (countableModuleDiagonalLinear S x) =
      countableModuleDiagonalLinear S (oddKTheoryCountableEmbeddingLinear f x) := by
  ext n
  by_cases hn : n ∈ Set.range f
  · obtain ⟨m, rfl⟩ := hn
    simp only [oddKTheoryCountableEmbeddingLinear_apply, Finsupp.embDomain_apply_self,
      countableModuleDiagonalLinear_apply]
  · simp only [oddKTheoryCountableEmbeddingLinear_apply,
      Finsupp.embDomain_of_notMem_range f _ n hn, countableModuleDiagonalLinear_apply,
      map_zero]

/-- The actual completed coordinate maps commute with the genuine diagonal
coefficient action, by the finite-vector identity and completion density. -/
theorem oddKTheoryCountableEmbedding_diagonal_commute
    (f : ℕ ↪ ℕ) (S : AdjointableMap B E E) :
    Commute (oddKTheoryCountableEmbedding (B := B) f) (countableModuleDiagonal S) := by
  change oddKTheoryCountableEmbedding f * countableModuleDiagonal S =
    countableModuleDiagonal S * oddKTheoryCountableEmbedding f
  apply oddKTheoryCountableOperator_ext_mk
  intro x
  simp only [AdjointableMap.mul_apply, countableModuleDiagonal_mk,
    oddKTheoryCountableEmbedding_mk, oddKTheoryCountableEmbeddingLinear_diagonal]

end BC4lean.KKTheory
