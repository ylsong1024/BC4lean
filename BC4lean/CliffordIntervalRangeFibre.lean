import BC4lean.CliffordIntervalCoefficients
import BC4lean.CliffordCycleIso
import BC4lean.OddIntervalKasparovFibre
import BC4lean.IntervalModuleFibreNorm

/-! # Evaluation commutes with the genuine Clifford coordinate range

The coordinate projection on an arbitrary interval module is the one already
constructed from coefficient approximate units. Its evaluation is proved to
be the actual coordinate projection on the completed fibre, by their exact
inner-product formulas. Consequently the fibre of its actual first range is
unitarily isomorphic to the first range of the fibre. Surjectivity follows
from the proved arbitrary-module fibre surjectivity, not from a section model.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B X M : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(X, B × B)ᵐᵒᵖ M] [CStarModule C(X, B × B)ᵐᵒᵖ M] [CompleteSpace M]

omit [T2Space X] in
/-- Evaluating the actual supported inner-product component commutes with
the explicit continuous-function product equivalence. -/
theorem cliffordSplitIntervalProjection_inner_left (k : Bool) (t : X) (x y : M) :
  MulOpposite.op (MulOpposite.unop
      ⟪coefficientChangedToOriginal (B := C(X, B × B))
        (C := C(X, B) × C(X, B)) (M := M)
        (continuousProductCoefficientEquiv (B := B) (X := X))
        (coordinateModuleProjection (B := C(X, B))
          (E := CliffordSplitIntervalModule (X := X) B M) k
          (coefficientChangedOfOriginal (B := C(X, B × B))
            (C := C(X, B) × C(X, B)) (M := M)
            (continuousProductCoefficientEquiv (B := B) (X := X)) x)),
        y⟫_(C(X, B × B)ᵐᵒᵖ) t) =
      coordinateCoefficient k
        (MulOpposite.op (MulOpposite.unop ⟪x, y⟫_(C(X, B × B)ᵐᵒᵖ) t)) := by
  have h := coordinateModuleProjection_inner_left (B := C(X, B))
    (E := CliffordSplitIntervalModule (X := X) B M) k
    (coefficientChangedOfOriginal (B := C(X, B × B))
      (C := C(X, B) × C(X, B)) (M := M)
      (continuousProductCoefficientEquiv (B := B) (X := X)) x)
    (coefficientChangedOfOriginal (B := C(X, B × B))
      (C := C(X, B) × C(X, B)) (M := M)
      (continuousProductCoefficientEquiv (B := B) (X := X)) y)
  have h' := congrArg (fun a : (C(X, B) × C(X, B))ᵐᵒᵖ =>
    MulOpposite.op ((MulOpposite.unop a).1 t, (MulOpposite.unop a).2 t)) h
  cases k <;> exact h'

/-- The actual coordinate approximate-unit projection commutes with
evaluation on every arbitrary complete interval module. -/
theorem cliffordSplitIntervalProjection_fibreMk (k : Bool) (t : X) (x : M) :
  hilbertModuleFibreMk (B := B × B) t
        (coefficientChangedToOriginal (B := C(X, B × B))
          (C := C(X, B) × C(X, B)) (M := M)
          (continuousProductCoefficientEquiv (B := B) (X := X))
          (coordinateModuleProjection (B := C(X, B))
            (E := CliffordSplitIntervalModule (X := X) B M) k
            (coefficientChangedOfOriginal (B := C(X, B × B))
              (C := C(X, B) × C(X, B)) (M := M)
              (continuousProductCoefficientEquiv (B := B) (X := X)) x))) =
      coordinateModuleProjection (B := B)
        (E := HilbertModuleFibre (B × B) M t) k
          (hilbertModuleFibreMk (B := B × B) t x) := by
  apply module_inner_ext_left (B := B × B)
  intro z
  obtain ⟨y, rfl⟩ := hilbertModuleFibreMk_surjective (B := B × B) (M := M) t z
  rw [hilbertModuleFibre_inner_mk, coordinateModuleProjection_inner_left,
    hilbertModuleFibre_inner_mk]
  exact cliffordSplitIntervalProjection_inner_left k t x y

/-- Evaluate vectors in the actual range, landing in the actual fibre range. -/
def cliffordIntervalRangeEvaluation (k : Bool) (t : X) :
    CliffordCoefficientRange C(X, B) (CliffordSplitIntervalModule (X := X) B M) k →L[ℂ]
      CliffordCoefficientRange B (HilbertModuleFibre (B × B) M t) k :=
  ({ toFun x := ⟨hilbertModuleFibreMk (B := B × B) t
       (coefficientChangedToOriginal (B := C(X, B × B))
         (C := C(X, B) × C(X, B)) (M := M)
         (continuousProductCoefficientEquiv (B := B) (X := X)) x.val), by
       change coordinateModuleProjection (B := B) k
         (hilbertModuleFibreMk (B := B × B) t
           (coefficientChangedToOriginal (B := C(X, B × B))
             (C := C(X, B) × C(X, B)) (M := M)
             (continuousProductCoefficientEquiv (B := B) (X := X)) x.val)) = _
       rw [← cliffordSplitIntervalProjection_fibreMk]
       change hilbertModuleFibreMk (B := B × B) t
         (coefficientChangedToOriginal (B := C(X, B × B))
           (C := C(X, B) × C(X, B)) (M := M)
           (continuousProductCoefficientEquiv (B := B) (X := X))
           (coordinateModuleProjection (B := C(X, B))
             (E := CliffordSplitIntervalModule (X := X) B M) k x.val)) = _
       rw [cliffordCoefficientRange_projection (B := C(X, B))
         (E := CliffordSplitIntervalModule (X := X) B M) k x]⟩
     map_add' x y := by
       apply Subtype.ext
       change hilbertModuleFibreMk (B := B × B) t
         (coefficientChangedToOriginal (B := C(X, B × B))
           (C := C(X, B) × C(X, B)) (M := M)
           (continuousProductCoefficientEquiv (B := B) (X := X)) x.val +
           coefficientChangedToOriginal (B := C(X, B × B))
             (C := C(X, B) × C(X, B)) (M := M)
             (continuousProductCoefficientEquiv (B := B) (X := X)) y.val) = _
       exact map_add _ _ _
     map_smul' c x := by
       apply Subtype.ext
       change hilbertModuleFibreMk (B := B × B) t
         (c • coefficientChangedToOriginal (B := C(X, B × B))
           (C := C(X, B) × C(X, B)) (M := M)
           (continuousProductCoefficientEquiv (B := B) (X := X)) x.val) = _
       exact map_smul _ _ _ } :
    CliffordCoefficientRange C(X, B) (CliffordSplitIntervalModule (X := X) B M) k →ₗ[ℂ]
      CliffordCoefficientRange B (HilbertModuleFibre (B × B) M t) k).mkContinuous
    1 (fun x => by
      change ‖hilbertModuleFibreMk (B := B × B) t
        (coefficientChangedToOriginal (B := C(X, B × B))
          (C := C(X, B) × C(X, B)) (M := M)
          (continuousProductCoefficientEquiv (B := B) (X := X)) x.val)‖ ≤
        1 * ‖coefficientChangedToOriginal (B := C(X, B × B))
          (C := C(X, B) × C(X, B)) (M := M)
          (continuousProductCoefficientEquiv (B := B) (X := X)) x.val‖
      simpa only [one_mul] using hilbertModuleFibreMk_norm_le (B := B × B) t
        (coefficientChangedToOriginal (B := C(X, B × B))
          (C := C(X, B) × C(X, B)) (M := M)
          (continuousProductCoefficientEquiv (B := B) (X := X)) x.val))

@[simp] theorem cliffordIntervalRangeEvaluation_coe (k : Bool) (t : X)
    (x : CliffordCoefficientRange C(X, B) (CliffordSplitIntervalModule (X := X) B M) k) :
    (cliffordIntervalRangeEvaluation k t x : HilbertModuleFibre (B × B) M t) =
      hilbertModuleFibreMk (B := B × B) t
        (coefficientChangedToOriginal (B := C(X, B × B))
          (C := C(X, B) × C(X, B)) (M := M)
          (continuousProductCoefficientEquiv (B := B) (X := X)) x.val) := rfl

theorem cliffordIntervalRangeEvaluation_inner (k : Bool) (t : X)
    (x y : CliffordCoefficientRange C(X, B) (CliffordSplitIntervalModule (X := X) B M) k) :
    ⟪cliffordIntervalRangeEvaluation k t x, cliffordIntervalRangeEvaluation k t y⟫_(Bᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪x, y⟫_(C(X, B)ᵐᵒᵖ) t) := by
  change cliffordCoordinateExtraction k
    ⟪hilbertModuleFibreMk (B := B × B) t
        (coefficientChangedToOriginal (B := C(X, B × B))
          (C := C(X, B) × C(X, B)) (M := M)
          (continuousProductCoefficientEquiv (B := B) (X := X)) x.val),
      hilbertModuleFibreMk (B := B × B) t
        (coefficientChangedToOriginal (B := C(X, B × B))
          (C := C(X, B) × C(X, B)) (M := M)
          (continuousProductCoefficientEquiv (B := B) (X := X)) y.val)⟫_((B × B)ᵐᵒᵖ) = _
  rw [hilbertModuleFibre_inner_mk]
  cases k <;> rfl

theorem cliffordIntervalRangeEvaluation_surjective (k : Bool) (t : X) :
    Function.Surjective (cliffordIntervalRangeEvaluation (B := B) (M := M) k t) := by
  intro y
  obtain ⟨x, hx⟩ := hilbertModuleFibreMk_surjective (B := B × B) (M := M) t (y : _)
  refine ⟨cliffordCoefficientRangeProject (B := C(X, B))
    (E := CliffordSplitIntervalModule (X := X) B M) k
    (coefficientChangedOfOriginal (B := C(X, B × B))
      (C := C(X, B) × C(X, B)) (M := M)
      (continuousProductCoefficientEquiv (B := B) (X := X)) x), ?_⟩
  apply Subtype.ext
  change hilbertModuleFibreMk (B := B × B) t
    (coefficientChangedToOriginal (B := C(X, B × B))
      (C := C(X, B) × C(X, B)) (M := M)
      (continuousProductCoefficientEquiv (B := B) (X := X))
      (coordinateModuleProjection (B := C(X, B))
        (E := CliffordSplitIntervalModule (X := X) B M) k
        (coefficientChangedOfOriginal (B := C(X, B × B))
          (C := C(X, B) × C(X, B)) (M := M)
          (continuousProductCoefficientEquiv (B := B) (X := X)) x))) = y.val
  rw [cliffordSplitIntervalProjection_fibreMk, hx]
  exact cliffordCoefficientRange_projection (B := B)
    (E := HilbertModuleFibre (B × B) M t) k y

/-- An actual Hilbert B-module unitary identifies extraction before and
after genuine evaluated quotient completion. -/
def cliffordIntervalRangeFibreEquiv (k : Bool) (t : X) :
    HilbertModuleEquiv B
      (HilbertModuleFibre B
        (CliffordCoefficientRange C(X, B) (CliffordSplitIntervalModule (X := X) B M) k) t)
      (CliffordCoefficientRange B (HilbertModuleFibre (B × B) M t) k) :=
  hilbertModuleFibreEquivOfEvaluation t (cliffordIntervalRangeEvaluation k t)
    (cliffordIntervalRangeEvaluation_inner k t) (cliffordIntervalRangeEvaluation_surjective k t)

@[simp] theorem cliffordIntervalRangeFibreEquiv_mk (k : Bool) (t : X)
    (x : CliffordCoefficientRange C(X, B) (CliffordSplitIntervalModule (X := X) B M) k) :
    cliffordIntervalRangeFibreEquiv k t (hilbertModuleFibreMk (B := B) t x) =
      cliffordIntervalRangeEvaluation k t x :=
  hilbertModuleFibreEquivOfEvaluation_mk t _ _ _ x

section WholeCycle

variable {Γ A : Type*} [Group Γ] [NonUnitalCStarAlgebra A]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

set_option maxHeartbeats 800000 in
private theorem cliffordIntervalExtractionFibre_action
    (c : GradedKasparovCycle α ((cliffordCoefficientAction β).continuousSections (X := X))
      CStarGrading.trivial (cliffordCoefficientGrading : CStarGrading (B × B)).continuousSections M)
    (t : X) (g : Γ)
    (z : HilbertModuleFibre B
      (CliffordCoefficientRange C(X, B) (CliffordSplitIntervalModule (X := X) B M) true) t) :
    cliffordIntervalRangeFibreEquiv (B := B) (X := X) (M := M) true t
      ((c.cliffordIntervalExtraction.fibre t).groupAction.action g z) =
      (cliffordExtractOddCycle true (c.fibre t)).groupAction.action g
        (cliffordIntervalRangeFibreEquiv (B := B) (X := X) (M := M) true t z) := by
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B)
    (M := CliffordCoefficientRange C(X, B) (CliffordSplitIntervalModule (X := X) B M) true) t z
  rw [c.cliffordIntervalExtraction.fibre_action_mk t g x, cliffordIntervalRangeFibreEquiv_mk (B := B) (X := X) (M := M),
    cliffordIntervalRangeFibreEquiv_mk (B := B) (X := X) (M := M)]
  apply Subtype.ext
  change hilbertModuleFibreMk (B := B × B) t
    (c.groupAction.action g
      (coefficientChangedToOriginal (B := C(X, B × B))
        (C := C(X, B) × C(X, B)) (M := M)
        (continuousProductCoefficientEquiv (B := B) (X := X)) x.val)) =
    (c.fibre t).groupAction.action g
      (hilbertModuleFibreMk (B := B × B) t
        (coefficientChangedToOriginal (B := C(X, B × B))
          (C := C(X, B) × C(X, B)) (M := M)
          (continuousProductCoefficientEquiv (B := B) (X := X)) x.val))
  exact (c.fibre_action_mk t g
    (coefficientChangedToOriginal (B := C(X, B × B))
      (C := C(X, B) × C(X, B)) (M := M)
      (continuousProductCoefficientEquiv (B := B) (X := X)) x.val)).symm

set_option maxHeartbeats 800000 in
private theorem cliffordIntervalExtractionFibre_representation
    (c : GradedKasparovCycle α ((cliffordCoefficientAction β).continuousSections (X := X))
      CStarGrading.trivial (cliffordCoefficientGrading : CStarGrading (B × B)).continuousSections M)
    (t : X) (a : A)
    (z : HilbertModuleFibre B
      (CliffordCoefficientRange C(X, B) (CliffordSplitIntervalModule (X := X) B M) true) t) :
    cliffordIntervalRangeFibreEquiv (B := B) (X := X) (M := M) true t
      ((c.cliffordIntervalExtraction.fibre t).representation a z) =
      (cliffordExtractOddCycle true (c.fibre t)).representation a
        (cliffordIntervalRangeFibreEquiv (B := B) (X := X) (M := M) true t z) := by
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B)
    (M := CliffordCoefficientRange C(X, B) (CliffordSplitIntervalModule (X := X) B M) true) t z
  rw [c.cliffordIntervalExtraction.fibre_representation_mk t a x, cliffordIntervalRangeFibreEquiv_mk (B := B) (X := X) (M := M),
    cliffordIntervalRangeFibreEquiv_mk (B := B) (X := X) (M := M)]
  apply Subtype.ext
  change hilbertModuleFibreMk (B := B × B) t
    (c.representation a
      (coefficientChangedToOriginal (B := C(X, B × B))
        (C := C(X, B) × C(X, B)) (M := M)
        (continuousProductCoefficientEquiv (B := B) (X := X)) x.val)) =
    (c.fibre t).representation a
      (hilbertModuleFibreMk (B := B × B) t
        (coefficientChangedToOriginal (B := C(X, B × B))
          (C := C(X, B) × C(X, B)) (M := M)
          (continuousProductCoefficientEquiv (B := B) (X := X)) x.val))
  exact (c.fibre_representation_mk t a
    (coefficientChangedToOriginal (B := C(X, B × B))
      (C := C(X, B) × C(X, B)) (M := M)
      (continuousProductCoefficientEquiv (B := B) (X := X)) x.val)).symm

set_option maxHeartbeats 800000 in
private theorem cliffordIntervalExtractionFibre_operator
    (c : GradedKasparovCycle α ((cliffordCoefficientAction β).continuousSections (X := X))
      CStarGrading.trivial (cliffordCoefficientGrading : CStarGrading (B × B)).continuousSections M)
    (t : X)
    (z : HilbertModuleFibre B
      (CliffordCoefficientRange C(X, B) (CliffordSplitIntervalModule (X := X) B M) true) t) :
    cliffordIntervalRangeFibreEquiv (B := B) (X := X) (M := M) true t
      ((c.cliffordIntervalExtraction.fibre t).operator z) =
      (cliffordExtractOddCycle true (c.fibre t)).operator
        (cliffordIntervalRangeFibreEquiv (B := B) (X := X) (M := M) true t z) := by
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B)
    (M := CliffordCoefficientRange C(X, B) (CliffordSplitIntervalModule (X := X) B M) true) t z
  rw [c.cliffordIntervalExtraction.fibre_operator_mk t x, cliffordIntervalRangeFibreEquiv_mk (B := B) (X := X) (M := M),
    cliffordIntervalRangeFibreEquiv_mk (B := B) (X := X) (M := M)]
  apply Subtype.ext
  change hilbertModuleFibreMk (B := B × B) t
    (c.operator
      (coefficientChangedToOriginal (B := C(X, B × B))
        (C := C(X, B) × C(X, B)) (M := M)
        (continuousProductCoefficientEquiv (B := B) (X := X)) x.val)) =
    (c.fibre t).operator
      (hilbertModuleFibreMk (B := B × B) t
        (coefficientChangedToOriginal (B := C(X, B × B))
          (C := C(X, B) × C(X, B)) (M := M)
          (continuousProductCoefficientEquiv (B := B) (X := X)) x.val))
  exact (c.fibre_operator_mk t
    (coefficientChangedToOriginal (B := C(X, B × B))
      (C := C(X, B) × C(X, B)) (M := M)
      (continuousProductCoefficientEquiv (B := B) (X := X)) x.val)).symm

set_option maxHeartbeats 800000 in
/-- Extraction commutes with the genuine arbitrary-module fibre for every
part of the cycle, using the same actual range-fibre unitary. -/
def GradedKasparovCycle.cliffordIntervalExtractionFibreIso
    (c : GradedKasparovCycle α ((cliffordCoefficientAction β).continuousSections (X := X))
      CStarGrading.trivial (cliffordCoefficientGrading : CStarGrading (B × B)).continuousSections M)
    (t : X) :
    OddKasparovCycleIso (c.cliffordIntervalExtraction.fibre t)
      (cliffordExtractOddCycle true (c.fibre t)) := by
  exact {
    moduleEquiv := cliffordIntervalRangeFibreEquiv (B := B) (X := X) (M := M) true t
    action_intertwine := cliffordIntervalExtractionFibre_action c t
    representation_intertwine := cliffordIntervalExtractionFibre_representation c t
    operator_intertwine := cliffordIntervalExtractionFibre_operator c t
  }

end WholeCycle

end BC4lean.KKTheory
