import BC4lean.FiniteJuliaAlignedCorner
import BC4lean.StandardCountableFiniteCoordinates

/-! # Actual paired finite prefix coordinates

The two finite standard-prefix inclusions use the same finite reindexing.
Their combined inclusion is therefore exactly the genuine paired coordinate
inclusion after that actual finite-coordinate unitary. This identifies its
range projection with the prescribed paired cutoff.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B : Type*} {ι : Type} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B] [Fintype ι] [DecidableEq ι]
local notation "Std" => StandardCountableHilbertModule B
local notation "FinMod" => FiniteStandardModule B ι

local instance standardFinitePairedPrefixCoordinatesLocalInstance01 (κ : Type) [Fintype κ] : CompleteSpace (FiniteStandardModule B κ) := finiteStandardModule_complete
local instance standardFinitePairedPrefixCoordinatesLocalInstance02 {M N : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Bᵐᵒᵖ M]
    [CStarModule Bᵐᵒᵖ M] [CompleteSpace M] [NormedAddCommGroup N] [NormedSpace ℂ N]
    [SMul Bᵐᵒᵖ N] [CStarModule Bᵐᵒᵖ N] [CompleteSpace N] :
    CompleteSpace (HilbertModuleSum B M N) := hilbertModuleSum_complete

def finitePairedPrefixReindex : ι ⊕ ι ≃ PairedStandardFiniteIndex (Fintype.card ι) :=
  Equiv.sumCongr (Fintype.equivFin ι) (Fintype.equivFin ι)

def finitePairedPrefixCoordinateInclusion :
    AdjointableMap B (FiniteStandardModule B (ι ⊕ ι)) (HilbertModuleSum B Std Std) :=
  finitePairedPrefixInclusion.comp (oddKTheoryFiniteSumEquiv (B := B) (ι := ι) (κ := ι)).toAdjointable

theorem finiteStandardPrefixInclusion_eq_reindex :
    finiteStandardPrefixInclusion (B := B) (ι := ι) =
      (oddFredholmStandardFiniteInclusion (Fintype.card ι)).comp
        (oddKTheoryFiniteReindexEquiv (B := B) (Fintype.equivFin ι)).toAdjointable := by
  ext x
  exact finiteStandardPrefixInclusion_apply x

@[simp] theorem finiteStandardPrefixInclusion_adjoint_apply (x : Std) (i : ι) :
    (finiteStandardPrefixInclusion (B := B) (ι := ι)).adjoint x i =
      standardCountableEvaluation ((Fintype.equivFin ι i).val) x := by
  rw [finiteStandardPrefixInclusion_eq_reindex, AdjointableMap.adjoint_comp]
  change (oddFredholmStandardFiniteInclusion (Fintype.card ι)).adjoint x
      (Fintype.equivFin ι i) = _
  exact oddFredholmStandardFiniteInclusion_adjoint_apply _ _ _

theorem finitePairedPrefixCoordinateInclusion_eq_reindex :
    finitePairedPrefixCoordinateInclusion (B := B) (ι := ι) =
      (pairedStandardFiniteInclusion (Fintype.card ι)).comp
        (oddKTheoryFiniteReindexEquiv (B := B) (finitePairedPrefixReindex (ι := ι))).toAdjointable := by
  have ha : (finitePairedPrefixCoordinateInclusion (B := B) (ι := ι)).adjoint =
      (oddKTheoryFiniteReindexEquiv (B := B) (finitePairedPrefixReindex (ι := ι))).toAdjointable.adjoint.comp
        (pairedStandardFiniteInclusion (Fintype.card ι)).adjoint := by
    ext x i
    cases i with
    | inl i =>
      change finiteStandardPrefixInclusion.adjoint x.fst i =
        (pairedStandardFiniteInclusion (Fintype.card ι)).adjoint x
          (Sum.inl (Fintype.equivFin ι i))
      rw [finiteStandardPrefixInclusion_adjoint_apply,
        pairedStandardFiniteInclusion_adjoint_apply, pairedStandardCoordinateInclusion_adjoint_apply]
    | inr i =>
      change finiteStandardPrefixInclusion.adjoint x.snd i =
        (pairedStandardFiniteInclusion (Fintype.card ι)).adjoint x
          (Sum.inr (Fintype.equivFin ι i))
      rw [finiteStandardPrefixInclusion_adjoint_apply,
        pairedStandardFiniteInclusion_adjoint_apply, pairedStandardCoordinateInclusion_adjoint_apply]
  have h := congrArg AdjointableMap.adjoint ha
  simpa only [AdjointableMap.adjoint_adjoint, AdjointableMap.adjoint_comp] using h

theorem finitePairedPrefixCoordinateInclusion_comp_adjoint :
    (finitePairedPrefixCoordinateInclusion (B := B) (ι := ι)).comp
      finitePairedPrefixCoordinateInclusion.adjoint = standardCountablePairedCutoff (Fintype.card ι) := by
  simp only [finitePairedPrefixCoordinateInclusion_eq_reindex, AdjointableMap.adjoint_comp]
  have he :
      (oddKTheoryFiniteReindexEquiv (B := B) (finitePairedPrefixReindex (ι := ι))).toAdjointable.comp
        (oddKTheoryFiniteReindexEquiv (B := B) (finitePairedPrefixReindex (ι := ι))).toAdjointable.adjoint =
          AdjointableMap.id := by
    ext x
    exact HilbertModuleEquiv.apply_symm_apply _ x
  calc
    _ = ((pairedStandardFiniteInclusion (Fintype.card ι)).comp
        AdjointableMap.id).comp (pairedStandardFiniteInclusion (Fintype.card ι)).adjoint := by
      rw [← he]
      ext x
      rfl
    _ = standardCountablePairedCutoff (Fintype.card ι) := by
      simpa only [AdjointableMap.comp_id] using
        pairedStandardFiniteInclusion_comp_adjoint (B := B) (Fintype.card ι)

end BC4lean.KKTheory
