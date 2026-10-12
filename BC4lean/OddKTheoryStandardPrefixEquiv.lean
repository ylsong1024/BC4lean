import BC4lean.OddKTheoryStandardFiniteSplit
import BC4lean.StandardCountableReindex

/-! # The actual finite prefix and shifted completed standard tail

The injection k ↦ n+k is completed from actual finite coefficient vectors.
Its final projection is exactly I-Pₙ. Thus the closed orthogonal tail is
genuinely unitarily isomorphic to H_B, and Bⁿ ⊕ H_B is actually H_B.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

def oddKTheoryProjectionOneEquiv : HilbertModuleEquiv B E
    (ProjectionModule (1 : AdjointableMap B E E)) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun x := ⟨x, rfl⟩
          invFun x := (x : E)
          left_inv _ := rfl
          right_inv _ := rfl
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      norm_map' _ := rfl }
  inner_map _ _ := rfl

def oddKTheoryStandardShiftEmbedding (n : ℕ) : ℕ ↪ ℕ :=
  ⟨fun k => n + k, fun _ _ h => Nat.add_left_cancel h⟩

theorem oddKTheoryStandardShift_finalProjection (n : ℕ) :
    (standardCountableEmbedding (B := B) (oddKTheoryStandardShiftEmbedding n)).comp
      (standardCountableEmbedding (oddKTheoryStandardShiftEmbedding n)).adjoint =
        1 - standardCountableCutoff n := by
  apply standardCountable_adjointable_ext_mk
  intro x
  simp only [AdjointableMap.comp_apply, standardCountableEmbedding_adjoint_mk,
    standardCountableEmbedding_mk, AdjointableMap.coe_sub_apply,
    AdjointableMap.one_apply, standardCountableCutoff_mk, ← map_sub]
  congr 1
  ext k
  simp only [standardCountableEmbeddingLinear_apply, Finsupp.sub_apply, Finsupp.filter_apply]
  by_cases hk : k < n
  · have hr : k ∉ Set.range (oddKTheoryStandardShiftEmbedding n) := by
      rintro ⟨j, hj⟩
      change n + j = k at hj
      omega
    rw [Finsupp.embDomain_of_notMem_range _ _ _ hr, if_pos hk, sub_self]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hk)
    change (standardCountableRestrictionLinear (oddKTheoryStandardShiftEmbedding n) x).embDomain
      (oddKTheoryStandardShiftEmbedding n) (oddKTheoryStandardShiftEmbedding n j) =
        x (n + j) - (if n + j < n then x (n + j) else 0)
    rw [Finsupp.embDomain_apply_self, if_neg (by omega), sub_zero]
    rfl

def oddKTheoryStandardTailShiftEquiv (n : ℕ) : HilbertModuleEquiv B
    (StandardCountableHilbertModule B) (ProjectionModule (1 - standardCountableCutoff n)) :=
  oddKTheoryProjectionOneEquiv.trans
    (projectionRangeEquiv 1 (1 - standardCountableCutoff n)
      (standardCountableEmbedding (oddKTheoryStandardShiftEmbedding n))
      (standardCountableEmbedding_adjoint_comp_self _) (oddKTheoryStandardShift_finalProjection n))

@[simp] theorem oddKTheoryStandardTailShiftEquiv_coe (n : ℕ)
    (x : StandardCountableHilbertModule B) :
    (oddKTheoryStandardTailShiftEquiv n x : StandardCountableHilbertModule B) =
      standardCountableEmbedding (oddKTheoryStandardShiftEmbedding n) x := rfl

variable [TopologicalSpace.SeparableSpace B]

local instance oddContinuationOddKTheoryStandardPrefixEquivLocalInstance01 (n : ℕ) : CompleteSpace (FiniteStandardModule B (Fin n)) := finiteStandardModule_complete
local instance oddContinuationOddKTheoryStandardPrefixEquivLocalInstance02 (n : ℕ) : CompleteSpace (HilbertModuleSum B (FiniteStandardModule B (Fin n))
    (StandardCountableHilbertModule B)) := hilbertModuleSum_complete
local instance oddContinuationOddKTheoryStandardPrefixEquivLocalInstance03 (n : ℕ) : CompleteSpace (HilbertModuleSum B (FiniteStandardModule B (Fin n))
    (ProjectionModule (1 - standardCountableCutoff (B := B) n))) := hilbertModuleSum_complete

def oddKTheoryStandardPrefixEquiv (n : ℕ) : HilbertModuleEquiv B
    (HilbertModuleSum B (FiniteStandardModule B (Fin n)) (StandardCountableHilbertModule B))
    (StandardCountableHilbertModule B) :=
  ((HilbertModuleEquiv.refl (B := B) (E := FiniteStandardModule B (Fin n))).sum
    (oddKTheoryStandardTailShiftEquiv n)).trans (oddKTheoryStandardFiniteSplitEquiv n).symm

@[simp] theorem oddKTheoryStandardPrefixEquiv_inl (n : ℕ)
    (x : FiniteStandardModule B (Fin n)) :
    oddKTheoryStandardPrefixEquiv n (sumMk x 0) = oddFredholmStandardFiniteInclusion n x := by
  change oddFredholmStandardFiniteInclusion n x +
    (oddKTheoryStandardTailShiftEquiv n (0 : StandardCountableHilbertModule B) : _) = _
  rw [HilbertModuleEquiv.map_zero]
  exact add_zero _

@[simp] theorem oddKTheoryStandardPrefixEquiv_inr (n : ℕ)
    (x : StandardCountableHilbertModule B) :
    oddKTheoryStandardPrefixEquiv n (sumMk 0 x) =
      standardCountableEmbedding (oddKTheoryStandardShiftEmbedding n) x := by
  change oddFredholmStandardFiniteInclusion n 0 + (oddKTheoryStandardTailShiftEquiv n x : _) = _
  rw [map_zero, zero_add, oddKTheoryStandardTailShiftEquiv_coe]

end BC4lean.KKTheory
