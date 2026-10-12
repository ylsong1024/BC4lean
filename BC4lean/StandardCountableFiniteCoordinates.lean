import BC4lean.StandardCountablePairedCutoff
import BC4lean.FiniteModuleCompactMatrix
import Mathlib.Algebra.BigOperators.Fin

/-! # Actual finite coordinates inside the paired standard Hilbert module

The finite coordinates are the actual standard coefficient inclusions on the
two summands. Their finite sum gives an adjointable isometry, and its range
projection is exactly the paired cutoff. No coordinate inclusion or cutoff is
declared compact for a nonunital coefficient algebra.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The finite coordinate set retains the two Julia summands. -/
abbrev PairedStandardFiniteIndex (n : ℕ) := Fin n ⊕ Fin n

/-- The genuine coefficient coordinate inclusion in the paired standard module. -/
def pairedStandardCoordinateInclusion (n : ℕ) (i : PairedStandardFiniteIndex n) :
    AdjointableMap B Bᵐᵒᵖ
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) :=
  match i with
  | Sum.inl j => sumInl.comp (standardCountableInclusion j.val)
  | Sum.inr j => sumInr.comp (standardCountableInclusion j.val)

@[simp] theorem pairedStandardCoordinateInclusion_adjoint_apply (n : ℕ)
    (i : PairedStandardFiniteIndex n)
    (x : HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) :
    (pairedStandardCoordinateInclusion n i).adjoint x =
      match i with
      | Sum.inl j => standardCountableEvaluation j.val x.fst
      | Sum.inr j => standardCountableEvaluation j.val x.snd := by
  cases i <;> rfl

/-- The actual coordinate inclusions are mutually orthogonal adjoint pairs. -/
@[simp] theorem pairedStandardCoordinateInclusion_adjoint_inclusion (n : ℕ)
    (i j : PairedStandardFiniteIndex n) (b : Bᵐᵒᵖ) :
    (pairedStandardCoordinateInclusion n i).adjoint
        (pairedStandardCoordinateInclusion n j b) = if j = i then b else 0 := by
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      change standardCountableEvaluation i.val (standardCountableInclusion j.val b) = _
      rw [standardCountableEvaluation_inclusion]
      simp only [Fin.val_inj, Sum.inl.injEq]
    | inr j =>
      change (standardCountableEvaluation (B := B) i.val).toCLM 0 = 0
      exact (standardCountableEvaluation (B := B) i.val).toCLM.map_zero
  | inr i =>
    cases j with
    | inl j =>
      change (standardCountableEvaluation (B := B) i.val).toCLM 0 = 0
      exact (standardCountableEvaluation (B := B) i.val).toCLM.map_zero
    | inr j =>
      change standardCountableEvaluation i.val (standardCountableInclusion j.val b) = _
      rw [standardCountableEvaluation_inclusion]
      simp only [Fin.val_inj, Sum.inr.injEq]

/-- The finite coordinate map is assembled from actual adjointable inclusions. -/
def pairedStandardFiniteInclusion (n : ℕ) :
    AdjointableMap B (FiniteStandardModule B (PairedStandardFiniteIndex n))
      (HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B)) :=
  ∑ i : PairedStandardFiniteIndex n,
    (pairedStandardCoordinateInclusion n i).comp (finiteStandardEvaluation i)

@[simp] theorem pairedStandardFiniteInclusion_apply (n : ℕ)
    (x : FiniteStandardModule B (PairedStandardFiniteIndex n)) :
    pairedStandardFiniteInclusion n x =
      ∑ i : PairedStandardFiniteIndex n, pairedStandardCoordinateInclusion n i (x i) := by
  simp only [pairedStandardFiniteInclusion, finiteAdjointable_sum_apply,
    AdjointableMap.comp_apply, finiteStandardEvaluation_apply]

/-- Its actual adjoint extracts precisely the finite coefficient coordinates. -/
@[simp] theorem pairedStandardFiniteInclusion_adjoint_apply (n : ℕ)
    (x : HilbertModuleSum B (StandardCountableHilbertModule B) (StandardCountableHilbertModule B))
    (i : PairedStandardFiniteIndex n) :
    (pairedStandardFiniteInclusion n).adjoint x i =
      (pairedStandardCoordinateInclusion n i).adjoint x := by
  rw [pairedStandardFiniteInclusion, finiteAdjointable_sum_adjoint]
  simp only [AdjointableMap.adjoint_comp, finiteStandardEvaluation,
    AdjointableMap.adjoint_adjoint, finiteAdjointable_sum_apply, AdjointableMap.comp_apply]
  change finiteStandardEvaluation (B := B) i
      (∑ j : PairedStandardFiniteIndex n,
        finiteStandardInclusion (B := B) j
          ((pairedStandardCoordinateInclusion n j).adjoint x)) = _
  rw [map_sum (finiteStandardEvaluation (B := B) i).toCLM]
  simp [finiteStandardEvaluation_apply, finiteStandardInclusion_apply,
    finiteStandardSingle_apply, Pi.single_apply]

/-- This finite coordinate map is an actual adjointable isometry. -/
@[simp] theorem pairedStandardFiniteInclusion_adjoint_comp_self (n : ℕ) :
    (pairedStandardFiniteInclusion (B := B) n).adjoint.comp (pairedStandardFiniteInclusion n) =
      AdjointableMap.id := by
  ext x i
  simp only [AdjointableMap.comp_apply, pairedStandardFiniteInclusion_adjoint_apply,
    pairedStandardFiniteInclusion_apply]
  rw [map_sum (pairedStandardCoordinateInclusion (B := B) n i).adjoint.toCLM]
  simp only [pairedStandardCoordinateInclusion_adjoint_inclusion]
  cases i <;> simp

/-- The isometry has exactly the actual paired cutoff as its range projection. -/
@[simp] theorem pairedStandardFiniteInclusion_comp_adjoint (n : ℕ) :
    (pairedStandardFiniteInclusion (B := B) n).comp (pairedStandardFiniteInclusion n).adjoint =
      standardCountablePairedCutoff n := by
  have hs (y : StandardCountableHilbertModule B) :
      (∑ i : Fin n, standardCountableInclusion (B := B) i.val
        (standardCountableEvaluation (B := B) i.val y)) = standardCountableCutoff n y := by
    rw [Fin.sum_univ_eq_sum_range
      (fun i : ℕ => standardCountableInclusion (B := B) i
        (standardCountableEvaluation (B := B) i y)) n]
    exact (standardCountableCutoff_apply n y).symm
  ext x
  let x₁ : StandardCountableHilbertModule B := x.fst
  let x₂ : StandardCountableHilbertModule B := x.snd
  simp only [AdjointableMap.comp_apply, pairedStandardFiniteInclusion_apply,
    pairedStandardFiniteInclusion_adjoint_apply, Fintype.sum_sum_type]
  change
    (∑ i : Fin n, (sumInl (B := B) (F := StandardCountableHilbertModule B))
      (standardCountableInclusion i.val (standardCountableEvaluation i.val x₁))) +
    (∑ i : Fin n, (sumInr (B := B) (E := StandardCountableHilbertModule B))
      (standardCountableInclusion i.val (standardCountableEvaluation i.val x₂))) =
    standardCountablePairedCutoff n x
  rw [← map_sum (sumInl (B := B) (F := StandardCountableHilbertModule B)).toCLM,
    ← map_sum (sumInr (B := B) (E := StandardCountableHilbertModule B)).toCLM]
  calc
    _ = sumInl (B := B) (F := StandardCountableHilbertModule B)
          (standardCountableCutoff n x₁) +
        sumInr (B := B) (E := StandardCountableHilbertModule B)
          (standardCountableCutoff n x₂) :=
      congrArg₂ (fun y₁ y₂ : StandardCountableHilbertModule B =>
        sumInl (B := B) (F := StandardCountableHilbertModule B) y₁ +
          sumInr (B := B) (E := StandardCountableHilbertModule B) y₂) (hs x₁) (hs x₂)
    _ = standardCountablePairedCutoff n x := by
      rw [standardCountablePairedCutoff, sumMap_apply]
      apply (WithCStarModule.equiv Bᵐᵒᵖ
        (StandardCountableHilbertModule B × StandardCountableHilbertModule B)).injective
      apply Prod.ext
      · change standardCountableCutoff n x₁ + 0 = standardCountableCutoff n x₁
        exact add_zero _
      · change 0 + standardCountableCutoff n x₂ = standardCountableCutoff n x₂
        exact zero_add _

end BC4lean.KKTheory
