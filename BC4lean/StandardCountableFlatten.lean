import BC4lean.CountableHilbertModuleSum
import BC4lean.StandardCountableReindex
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Data.Nat.Pairing

/-! # Countably many genuine standard modules are unitarily one standard module

The nth row of H_B is injected in the coordinates pair(n,m). The row ranges
are orthogonal for the actual coefficient inner product. Finite row sums
therefore preserve their coefficient form and extend to an isometry of the
completed countable module sum. Every finite coefficient vector has an exact
finite-row preimage. The isometry has closed range by completeness and dense
range by those preimages, proving surjectivity and the actual unitary.
-/

noncomputable section
namespace BC4lean.KKTheory
open UniformSpace
open scoped InnerProductSpace

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def standardCountableRowEmbedding (n : ℕ) : ℕ ↪ ℕ where
  toFun m := Nat.pair n m
  inj' _m _k h := (Nat.pair_eq_pair.mp h).2

@[simp] theorem standardCountableRowEmbedding_apply (n m : ℕ) :
    standardCountableRowEmbedding n m = Nat.pair n m := rfl

theorem standardCountableRowEmbedding_disjoint {n m : ℕ} (hnm : n ≠ m) (k : ℕ) :
    standardCountableRowEmbedding n k ∉ Set.range (standardCountableRowEmbedding m) := by
  rintro ⟨j, hj⟩
  have he : m = n := (Nat.pair_eq_pair.mp hj).1
  exact hnm he.symm

theorem standardCountableRow_inner (n m : ℕ) (x y : StandardCountableHilbertModule B) :
    ⟪standardCountableEmbedding (standardCountableRowEmbedding n) x,
      standardCountableEmbedding (standardCountableRowEmbedding m) y⟫_(Bᵐᵒᵖ) =
      if n = m then ⟪x, y⟫_(Bᵐᵒᵖ) else 0 := by
  by_cases hnm : n = m
  · subst m
    rw [if_pos rfl, standardCountableEmbedding_inner]
  · rw [if_neg hnm]
    exact standardCountableEmbedding_inner_eq_zero _ _ (standardCountableRowEmbedding_disjoint hnm) x y

/-- A finite family of actual completed standard-module rows is interleaved linearly. -/
def standardCountableFlattenLinear :
    CountableModuleVectors (StandardCountableHilbertModule B) →ₗ[ℂ] StandardCountableHilbertModule B :=
  Finsupp.lsum ℂ (fun n => (standardCountableEmbedding (standardCountableRowEmbedding n)).toCLM.toLinearMap)

@[simp] theorem standardCountableFlattenLinear_apply
    (x : CountableModuleVectors (StandardCountableHilbertModule B)) :
    standardCountableFlattenLinear x =
      x.sum (fun n v => standardCountableEmbedding (standardCountableRowEmbedding n) v) := rfl

@[simp] theorem standardCountableFlattenLinear_single (n : ℕ) (x : StandardCountableHilbertModule B) :
    standardCountableFlattenLinear (Finsupp.single n x) =
      standardCountableEmbedding (standardCountableRowEmbedding n) x :=
  Finsupp.lsum_single _ _ _ _

/-- Interleaving finitely many full rows preserves the actual coefficient form. -/
theorem standardCountableFlattenLinear_inner
    (x y : CountableModuleVectors (StandardCountableHilbertModule B)) :
    ⟪standardCountableFlattenLinear x, standardCountableFlattenLinear y⟫_(Bᵐᵒᵖ) =
      countableModuleFiniteInner (B := B) x y := by
  classical
  rw [standardCountableFlattenLinear_apply, standardCountableFlattenLinear_apply]
  change ⟪∑ n ∈ x.support, standardCountableEmbedding (standardCountableRowEmbedding n) (x n),
    ∑ m ∈ y.support, standardCountableEmbedding (standardCountableRowEmbedding m) (y m)⟫_(Bᵐᵒᵖ) =
    ∑ n ∈ x.support, ⟪x n, y n⟫_(Bᵐᵒᵖ)
  rw [CStarModule.inner_sum_left (A := Bᵐᵒᵖ) (E := StandardCountableHilbertModule B)]
  simp only [CStarModule.inner_sum_right (A := Bᵐᵒᵖ) (E := StandardCountableHilbertModule B),
    standardCountableRow_inner]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n ∈ y.support
  · rw [Finset.sum_eq_single n]
    · rw [if_pos rfl]
    · intro m _ hmn
      exact if_neg hmn.symm
    · exact fun h => False.elim (h hn)
  · have hy : y n = 0 := Finsupp.notMem_support_iff.mp hn
    rw [hy, CStarModule.inner_zero_right (A := Bᵐᵒᵖ) (E := StandardCountableHilbertModule B)]
    apply Finset.sum_eq_zero
    intro m hm
    apply if_neg
    intro hnm
    exact hn (hnm.symm ▸ hm)

def standardCountableFlattenQuotientLinear :
    CountableHilbertModulePreSum B (StandardCountableHilbertModule B) →ₗ[ℂ]
      StandardCountableHilbertModule B :=
  (PositiveModuleForm.nullRadical (B := B)
    (E := CountableModuleVectors (StandardCountableHilbertModule B))).liftQ
      standardCountableFlattenLinear (fun x hx => by
        rw [countableModuleFinite_nullRadical_eq_bot, Submodule.mem_bot] at hx
        simp [hx])

@[simp] theorem standardCountableFlattenQuotientLinear_mk
    (x : CountableModuleVectors (StandardCountableHilbertModule B)) :
    standardCountableFlattenQuotientLinear (positiveModuleQuotientMk (B := B) x) =
      standardCountableFlattenLinear x := rfl

theorem standardCountableFlattenQuotientLinear_norm
    (x : CountableHilbertModulePreSum B (StandardCountableHilbertModule B)) :
    ‖standardCountableFlattenQuotientLinear x‖ = ‖x‖ := by
  obtain ⟨v, rfl⟩ := positiveModuleQuotientMk_surjective x
  rw [standardCountableFlattenQuotientLinear_mk, PositiveModuleQuotient.norm_mk,
    CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) (standardCountableFlattenLinear v), standardCountableFlattenLinear_inner]
  rfl

def standardCountableFlattenQuotientCLM :
    CountableHilbertModulePreSum B (StandardCountableHilbertModule B) →L[ℂ]
      StandardCountableHilbertModule B :=
  standardCountableFlattenQuotientLinear.mkContinuous 1
    (fun x => by rw [standardCountableFlattenQuotientLinear_norm]; simp only [one_mul, le_refl])

/-- The actual continuous linear extension from the genuine completed countable sum. -/
def standardCountableFlattenCLM :
    CountableHilbertModuleSum B (StandardCountableHilbertModule B) →L[ℂ]
      StandardCountableHilbertModule B := standardCountableFlattenQuotientCLM.fromCompletion

@[simp] theorem standardCountableFlattenCLM_mk
    (x : CountableModuleVectors (StandardCountableHilbertModule B)) :
    standardCountableFlattenCLM (countableModuleMk (B := B) x) = standardCountableFlattenLinear x := by
  rw [countableModuleMk_apply]
  change standardCountableFlattenQuotientCLM.fromCompletion
    ((positiveModuleQuotientMk (B := B) x) :
      CountableHilbertModuleSum B (StandardCountableHilbertModule B)) = _
  rw [ContinuousLinearMap.fromCompletion_apply_coe]
  rfl

theorem standardCountableFlattenCLM_norm
    (x : CountableHilbertModuleSum B (StandardCountableHilbertModule B)) :
    ‖standardCountableFlattenCLM x‖ = ‖x‖ := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq (continuous_norm.comp standardCountableFlattenCLM.continuous) continuous_norm
  · intro q
    change ‖standardCountableFlattenQuotientCLM.fromCompletion
      (q : CountableHilbertModuleSum B (StandardCountableHilbertModule B))‖ = _
    rw [ContinuousLinearMap.fromCompletion_apply_coe, Completion.norm_coe]
    exact standardCountableFlattenQuotientLinear_norm q

theorem standardCountableFlattenCLM_inner
    (x y : CountableHilbertModuleSum B (StandardCountableHilbertModule B)) :
    ⟪standardCountableFlattenCLM x, standardCountableFlattenCLM y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) := by
  refine Completion.induction_on₂ x y ?_ ?_
  · exact isClosed_eq
      (CStarModule.continuous_inner.comp
        ((standardCountableFlattenCLM.continuous.comp continuous_fst).prodMk
          (standardCountableFlattenCLM.continuous.comp continuous_snd)))
      CStarModule.continuous_inner
  · intro q r
    obtain ⟨v, rfl⟩ := positiveModuleQuotientMk_surjective q
    obtain ⟨w, rfl⟩ := positiveModuleQuotientMk_surjective r
    change ⟪standardCountableFlattenCLM (countableModuleMk (B := B) v),
      standardCountableFlattenCLM (countableModuleMk (B := B) w)⟫_(Bᵐᵒᵖ) = _
    rw [standardCountableFlattenCLM_mk, standardCountableFlattenCLM_mk,
      completionInner_coe, PositiveModuleQuotient.inner_mk]
    exact standardCountableFlattenLinear_inner v w

private theorem standardCountableFlatten_finite_preimage (v : StandardCountableVectors B) :
    ∃ x : CountableHilbertModuleSum B (StandardCountableHilbertModule B),
      standardCountableFlattenCLM x = standardCountableMk v := by
  let w : CountableModuleVectors (StandardCountableHilbertModule B) := v.sum fun n b =>
    Finsupp.single (Nat.unpair n).1 (standardCountableInclusion (Nat.unpair n).2 b)
  refine ⟨countableModuleMk (B := B) w, ?_⟩
  rw [standardCountableFlattenCLM_mk]
  change standardCountableFlattenLinear
    (∑ n ∈ v.support, Finsupp.single (Nat.unpair n).1 (standardCountableInclusion (Nat.unpair n).2 (v n))) = _
  rw [map_sum]
  calc
    (∑ n ∈ v.support, standardCountableFlattenLinear
        (Finsupp.single (Nat.unpair n).1 (standardCountableInclusion (Nat.unpair n).2 (v n)))) =
        ∑ n ∈ v.support, standardCountableMk (Finsupp.single n (v n)) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [standardCountableFlattenLinear_single, standardCountableInclusion_apply,
        standardCountableEmbedding_mk, standardCountableEmbeddingLinear_apply,
        Finsupp.embDomain_eq_mapDomain, Finsupp.mapDomain_single,
        standardCountableRowEmbedding_apply, Nat.pair_unpair]
    _ = standardCountableMk v := by
      rw [← map_sum]
      exact congrArg (standardCountableMk (B := B)) v.sum_single

theorem standardCountableFlattenCLM_surjective :
    Function.Surjective (standardCountableFlattenCLM (B := B)) := by
  have hi : Isometry (standardCountableFlattenCLM (B := B)) :=
    AddMonoidHomClass.isometry_of_norm _ standardCountableFlattenCLM_norm
  have hc : IsClosed (Set.range (standardCountableFlattenCLM (B := B))) := hi.isClosedEmbedding.isClosed_range
  have hd : Dense (Set.range (standardCountableFlattenCLM (B := B))) :=
    (standardCountableMk_denseRange (B := B)).mono (by
      rintro x ⟨v, rfl⟩
      exact standardCountableFlatten_finite_preimage v)
  have hu : Set.range (standardCountableFlattenCLM (B := B)) = Set.univ := by
    rw [← hc.closure_eq]
    exact hd.closure_eq
  exact Set.range_eq_univ.mp hu

/-- The actual unitary H_B^∞ ≅ H_B, proved onto using exact finite-vector preimages. -/
def standardCountableInfiniteSumEquiv :
    HilbertModuleEquiv B (CountableHilbertModuleSum B (StandardCountableHilbertModule B))
      (StandardCountableHilbertModule B) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective
    { toLinearMap := standardCountableFlattenCLM.toLinearMap
      norm_map' := standardCountableFlattenCLM_norm } standardCountableFlattenCLM_surjective
  inner_map := standardCountableFlattenCLM_inner

end BC4lean.KKTheory
