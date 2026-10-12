import BC4lean.CountableModuleOperator
import BC4lean.GradedMatrixMoritaFibreEvaluation

/-! # Actual completed fibres of countable Hilbert module sums

Coordinate fibre evaluation preserves the whole finite coefficient form.
The form bound descends it through the radical quotient and completion.
Its evaluated-fibre isometry is onto because every finite fibre-coordinate
vector has an actual module preimage and those vectors are dense.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B X M : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, B)ᵐᵒᵖ M]
  [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

def countableModuleFiniteFibreEvaluation (t : X) : CountableModuleVectors M →ₗ[ℂ]
    CountableModuleVectors (HilbertModuleFibre B M t) :=
  Finsupp.mapRange.linearMap (hilbertModuleFibreMk (B := B) t).toLinearMap

omit [T2Space X] [CompleteSpace M] in
@[simp] theorem countableModuleFiniteFibreEvaluation_apply (t : X)
    (v : CountableModuleVectors M) (i : ℕ) :
    countableModuleFiniteFibreEvaluation t v i = hilbertModuleFibreMk (B := B) t (v i) := rfl

omit [T2Space X] [CompleteSpace M] in
theorem countableModuleFiniteFibreEvaluation_inner (t : X) (v w : CountableModuleVectors M) :
    countableModuleFiniteInner (B := B) (countableModuleFiniteFibreEvaluation (B := B) t v)
      (countableModuleFiniteFibreEvaluation (B := B) t w) =
        MulOpposite.op (MulOpposite.unop (countableModuleFiniteInner (B := C(X, B)) v w) t) := by
  rw [countableModuleFiniteInner_eq_sum (B := B)
    (countableModuleFiniteFibreEvaluation (B := B) t v)
    (countableModuleFiniteFibreEvaluation (B := B) t w) v.support
    (Finsupp.support_mapRange (hf := map_zero (hilbertModuleFibreMk (B := B) (M := M) t).toLinearMap))]
  simp only [countableModuleFiniteFibreEvaluation_apply, hilbertModuleFibre_inner_mk,
    countableModuleFiniteInner, Finsupp.sum, Finset.unop_sum,
    ContinuousMap.coe_sum, Finset.sum_apply, Finset.op_sum]

omit [T2Space X] [CompleteSpace M] in
theorem countableModuleFiniteFibreEvaluation_formNorm_le (t : X) (v : CountableModuleVectors M) :
    PositiveModuleForm.formNorm (B := B) (countableModuleFiniteFibreEvaluation (B := B) t v) ≤
      1 * PositiveModuleForm.formNorm (B := C(X, B)) v := by
  rw [one_mul, PositiveModuleForm.formNorm, PositiveModuleForm.formNorm,
    countableModuleFinite_inner, countableModuleFinite_inner,
    countableModuleFiniteFibreEvaluation_inner]
  apply Real.sqrt_le_sqrt
  simpa only [MulOpposite.norm_op, MulOpposite.norm_unop] using
    (MulOpposite.unop (countableModuleFiniteInner (B := C(X, B)) v v)).norm_coe_le_norm t

def countableModuleFibreEvaluation (t : X) : CountableHilbertModuleSum C(X, B) M →L[ℂ]
    CountableHilbertModuleSum B (HilbertModuleFibre B M t) :=
  (positiveModuleQuotientLiftCLM (B := C(X, B)) (C := B)
    (E := CountableModuleVectors M) (F := CountableModuleVectors (HilbertModuleFibre B M t))
    (countableModuleFiniteFibreEvaluation (B := B) (X := X) (M := M) t)
    (countableModuleFiniteFibreEvaluation_formNorm_le (B := B) (X := X) (M := M) t)).completion

omit [T2Space X] [CompleteSpace M] in
@[simp] theorem countableModuleFibreEvaluation_mk (t : X) (v : CountableModuleVectors M) :
    countableModuleFibreEvaluation t (countableModuleMk (B := C(X, B)) v) =
      countableModuleMk (B := B) (countableModuleFiniteFibreEvaluation t v) := by
  rw [countableModuleMk_apply, countableModuleFibreEvaluation,
    ContinuousLinearMap.completion_apply_coe, positiveModuleQuotientLiftCLM_mk,
    countableModuleMk_apply]

omit [T2Space X] [CompleteSpace M] in
theorem countableModuleFibreEvaluation_inner (t : X)
    (x y : CountableHilbertModuleSum C(X, B) M) :
    ⟪countableModuleFibreEvaluation t x, countableModuleFibreEvaluation t y⟫_(Bᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪x, y⟫_(C(X, B)ᵐᵒᵖ) t) := by
  refine ((countableModuleMk_denseRange (B := C(X, B)) (E := M)).prodMap
    (countableModuleMk_denseRange (B := C(X, B)) (E := M))).induction_on
      (p := fun z : CountableHilbertModuleSum C(X, B) M × CountableHilbertModuleSum C(X, B) M =>
        ⟪countableModuleFibreEvaluation t z.1, countableModuleFibreEvaluation t z.2⟫_(Bᵐᵒᵖ) =
          MulOpposite.op (MulOpposite.unop ⟪z.1, z.2⟫_(C(X, B)ᵐᵒᵖ) t)) (x, y) ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro v
    change ⟪countableModuleFibreEvaluation t (countableModuleMk (B := C(X, B)) v.1),
      countableModuleFibreEvaluation t (countableModuleMk (B := C(X, B)) v.2)⟫_(Bᵐᵒᵖ) =
        MulOpposite.op (MulOpposite.unop
          ⟪countableModuleMk (B := C(X, B)) v.1,
            countableModuleMk (B := C(X, B)) v.2⟫_(C(X, B)ᵐᵒᵖ) t)
    simp only [countableModuleFibreEvaluation_mk, countableModuleMk_inner]
    exact countableModuleFiniteFibreEvaluation_inner t v.1 v.2

omit [T2Space X] in
@[simp] theorem countableModuleFibreEvaluation_inclusion (t : X) (i : ℕ) (x : M) :
    countableModuleFibreEvaluation t (countableModuleInclusion i x) =
      countableModuleInclusion i (hilbertModuleFibreMk (B := B) t x) := by
  rw [countableModuleInclusion_apply, countableModuleFibreEvaluation_mk,
    countableModuleInclusion_apply]
  congr 1
  ext j
  by_cases hij : i = j
  · subst j
    simp only [countableModuleFiniteFibreEvaluation_apply, Finsupp.single_eq_same]
  · simp only [countableModuleFiniteFibreEvaluation_apply, Finsupp.single_apply, hij,
      ite_false, map_zero]

def countableModuleFibreIsometry (t : X) :
    HilbertModuleFibre B (CountableHilbertModuleSum C(X, B) M) t →ₗᵢ[ℂ]
      CountableHilbertModuleSum B (HilbertModuleFibre B M t) :=
  GradedMatrixMoritaFibreEvaluation.completedIsometry (B := B) (X := X)
    (M := CountableHilbertModuleSum C(X, B) M)
    (H := CountableHilbertModuleSum B (HilbertModuleFibre B M t)) t
    (countableModuleFibreEvaluation (B := B) (X := X) (M := M) t)
    (countableModuleFibreEvaluation_inner (B := B) (X := X) (M := M) t)

omit [T2Space X] [CompleteSpace M] in
@[simp] theorem countableModuleFibreIsometry_mk (t : X) (x : CountableHilbertModuleSum C(X, B) M) :
    countableModuleFibreIsometry t (hilbertModuleFibreMk (B := B) t x) =
      countableModuleFibreEvaluation t x :=
  GradedMatrixMoritaFibreEvaluation.completedIsometry_mk (B := B) (X := X)
    (M := CountableHilbertModuleSum C(X, B) M)
    (H := CountableHilbertModuleSum B (HilbertModuleFibre B M t)) t
    (countableModuleFibreEvaluation (B := B) (X := X) (M := M) t)
    (countableModuleFibreEvaluation_inner (B := B) (X := X) (M := M) t) x

theorem countableModuleFibreIsometry_finite_preimage (t : X)
    (v : CountableModuleVectors (HilbertModuleFibre B M t)) :
    ∃ x, countableModuleFibreIsometry t x = countableModuleMk (B := B) v := by
  choose w hw using fun i => hilbertModuleFibreMk_surjective (B := B) (M := M) t (v i)
  let y : CountableModuleVectors M := ∑ i ∈ v.support, Finsupp.single i (w i)
  refine ⟨hilbertModuleFibreMk (B := B) t (countableModuleMk (B := C(X, B)) y), ?_⟩
  rw [countableModuleFibreIsometry_mk, countableModuleFibreEvaluation_mk]
  congr 1
  unfold y
  rw [map_sum]
  have he : ∀ i, countableModuleFiniteFibreEvaluation t (Finsupp.single i (w i)) =
      Finsupp.single i (v i) := by
    intro i
    ext j
    by_cases hij : i = j
    · subst j
      simp only [countableModuleFiniteFibreEvaluation_apply, Finsupp.single_eq_same]
      exact hw i
    · simp only [countableModuleFiniteFibreEvaluation_apply, Finsupp.single_apply, hij,
        ite_false, map_zero]
  simp only [he]
  exact v.sum_single

theorem countableModuleFibreIsometry_surjective (t : X) :
    Function.Surjective (countableModuleFibreIsometry (B := B) (M := M) t) := by
  have hc : IsClosed (Set.range (countableModuleFibreIsometry (B := B) (M := M) t)) :=
    (countableModuleFibreIsometry t).isometry.isClosedEmbedding.isClosed_range
  have hd : Dense (Set.range (countableModuleFibreIsometry (B := B) (M := M) t)) :=
    (countableModuleMk_denseRange (B := B) (E := HilbertModuleFibre B M t)).mono (by
      rintro x ⟨v, rfl⟩
      exact countableModuleFibreIsometry_finite_preimage t v)
  rw [← Set.range_eq_univ]
  exact hc.closure_eq ▸ hd.closure_eq

def countableModuleFibreEquiv (t : X) :
    HilbertModuleEquiv B (HilbertModuleFibre B (CountableHilbertModuleSum C(X, B) M) t)
      (CountableHilbertModuleSum B (HilbertModuleFibre B M t)) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective
    (countableModuleFibreIsometry (B := B) (X := X) (M := M) t)
    (countableModuleFibreIsometry_surjective (B := B) (X := X) (M := M) t)
  inner_map := GradedMatrixMoritaFibreEvaluation.completedIsometry_inner (B := B) (X := X)
    (M := CountableHilbertModuleSum C(X, B) M)
    (H := CountableHilbertModuleSum B (HilbertModuleFibre B M t)) t
    (countableModuleFibreEvaluation (B := B) (X := X) (M := M) t)
    (countableModuleFibreEvaluation_inner (B := B) (X := X) (M := M) t)

@[simp] theorem countableModuleFibreEquiv_mk (t : X) (x : CountableHilbertModuleSum C(X, B) M) :
    countableModuleFibreEquiv t (hilbertModuleFibreMk (B := B) t x) =
      countableModuleFibreEvaluation t x := countableModuleFibreIsometry_mk t x

@[simp] theorem countableModuleFibreEquiv_mk_inclusion (t : X) (i : ℕ) (x : M) :
    countableModuleFibreEquiv t (hilbertModuleFibreMk (B := B) t (countableModuleInclusion i x)) =
      countableModuleInclusion i (hilbertModuleFibreMk (B := B) t x) := by
  rw [countableModuleFibreEquiv_mk, countableModuleFibreEvaluation_inclusion]

end BC4lean.KKTheory
