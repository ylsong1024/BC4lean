import BC4lean.CliffordOddOddFourierConnection
import BC4lean.CliffordExternalEvenMonoidalPositivity

/-! # Whole source and action data under the Pauli Fourier unitary

The full half representation of the genuine swap grading becomes the two
actual source coordinates. The opposite coefficient coordinate reverses
the swap projection and thus cancels the external lower-coordinate source
swap. Group action compatibility follows from the original complex-linear
isometric action on every sum coordinate.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordOddOddFourier
open CliffordExternalEvenRepresentation

variable {C M : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Cᵐᵒᵖ M] [CStarModule Cᵐᵒᵖ M]
  [CompleteSpace M]

local instance cliffordOddOddFourierCompatibilityLocalInstance1 : CompleteSpace (Sum (C := C) (M := M)) := hilbertModuleSum_complete

variable {A : Type*} [NonUnitalCStarAlgebra A]
  (ρ : A →⋆ₙₐ[ℂ] AdjointableMap C M M)

def diagonalRepresentation : A →⋆ₙₐ[ℂ] AdjointableMap C (Sum (C := C) (M := M)) (Sum (C := C) (M := M)) :=
  sumRepresentation ρ ρ

theorem diagonalRepresentation_commutes (a : A) :
    (CliffordOddSourceCycle.grading (C := C) (H := M)).toAdjointable * diagonalRepresentation ρ a =
      diagonalRepresentation ρ a * (CliffordOddSourceCycle.grading (C := C) (H := M)).toAdjointable := by
  let _retainedOriginalComplete : CompleteSpace M := inferInstance
  ext x
  change sumSwap (sumMap (ρ a) (ρ a) x) = sumMap (ρ a) (ρ a) (sumSwap x)
  simp only [sumSwap_apply, sumMap_apply, sumMk_fst, sumMk_snd]

theorem operator_half (a : A × A) (x : Sum (C := C) (M := M)) :
    operator (halfRepresentation (diagonalRepresentation ρ) CliffordOddSourceCycle.grading
      (diagonalRepresentation_commutes ρ) a x) =
      sumMap (ρ a.1) (ρ a.2) (operator x) := by
  have hhalf :
      halfRepresentation (diagonalRepresentation ρ) CliffordOddSourceCycle.grading
        (diagonalRepresentation_commutes ρ) a x =
      sumMk (B := C)
        ((2 : ℂ)⁻¹ • (ρ a.1 (x.fst + x.snd)) +
          (2 : ℂ)⁻¹ • (ρ a.2 (x.fst - x.snd)))
        ((2 : ℂ)⁻¹ • (ρ a.1 (x.fst + x.snd)) -
          (2 : ℂ)⁻¹ • (ρ a.2 (x.fst - x.snd))) := by
    apply Prod.ext <;>
      simp only [halfRepresentation_eq, diagonalRepresentation, sumRepresentation_apply,
        CliffordOne.plusProjection, CliffordOne.minusProjection,
        CliffordOddSourceCycle.grading, GradedHilbertModule.toAdjointable_apply,
        sumSwap_apply, sumMap_apply, sumMk_fst, sumMk_snd,
        AdjointableMap.coe_add_apply, AdjointableMap.coe_sub_apply,
        AdjointableMap.coe_smul_apply, AdjointableMap.mul_apply, AdjointableMap.one_apply,
        WithCStarModule.add_fst, WithCStarModule.add_snd,
        WithCStarModule.sub_fst, WithCStarModule.sub_snd,
        WithCStarModule.smul_fst, WithCStarModule.smul_snd,
        map_add, map_sub, map_smul]
    module
  rw [hhalf]
  apply Prod.ext <;>
    (simp only [operator_apply, sumMap_apply, sumMk_fst, sumMk_snd,
      map_add, map_sub, map_smul]; module)

theorem opposite_half (a : A × A) (x : Sum (C := C) (M := M)) :
    oppositeEquiv (halfRepresentation (diagonalRepresentation ρ) CliffordOddSourceCycle.grading
      (diagonalRepresentation_commutes ρ) (cliffordCoefficientGrading.automorphism a) x) =
      sumMap (ρ a.1) (ρ a.2) (oppositeEquiv x) := by
  have hswap (b : A × A) (z : Sum (C := C) (M := M)) :
      sumSwap (halfRepresentation (diagonalRepresentation ρ) CliffordOddSourceCycle.grading
        (diagonalRepresentation_commutes ρ) b z) =
      halfRepresentation (diagonalRepresentation ρ) CliffordOddSourceCycle.grading
        (diagonalRepresentation_commutes ρ) b (sumSwap z) := by
    have h := congrArg (fun T : AdjointableMap C (Sum (C := C) (M := M))
      (Sum (C := C) (M := M)) => T z)
      (grading_commutes_half (diagonalRepresentation ρ)
        (CliffordOddSourceCycle.grading (C := C) (H := M))
        (diagonalRepresentation_commutes ρ) b)
    simpa only [AdjointableMap.mul_apply, GradedHilbertModule.toAdjointable_apply,
      CliffordOddSourceCycle.grading] using h
  simp only [oppositeEquiv_apply, hswap, operator_half, sumSwap_apply, sumMap_apply,
    sumMk_fst, sumMk_snd, cliffordCoefficientGrading_apply]

theorem pairEquiv_representation (a : A × A)
    (x : CliffordPairModule C (Sum (C := C) (M := M))) :
    pairEquiv (representation (diagonalRepresentation ρ) CliffordOddSourceCycle.grading
      (diagonalRepresentation_commutes ρ) a x) =
      cliffordPairMap (sumMap (ρ a.1) (ρ a.2)) (sumMap (ρ a.1) (ρ a.2)) (pairEquiv x) := by
  apply Prod.ext
  · exact operator_half ρ a x.1
  · exact opposite_half ρ a x.2

variable {Γ : Type*} [Group Γ] {γ : CStarAlgebraAction Γ C}
  (U : EquivariantHilbertModule γ M)

theorem operator_action (g : Γ) (x : Sum (C := C) (M := M)) :
    operator ((U.sum U).action g x) = (U.sum U).action g (operator x) := by
  let _retainedOriginalComplete : CompleteSpace M := inferInstance
  apply Prod.ext <;>
    simp only [operator_apply, EquivariantHilbertModule.sum_action_apply,
      sumMk_fst, sumMk_snd, map_add, map_sub, map_smul]

theorem oppositeEquiv_action (g : Γ) (x : Sum (C := C) (M := M)) :
    oppositeEquiv ((U.sum U).action g x) = (U.sum U).action g (oppositeEquiv x) := by
  have hswap (z : Sum (C := C) (M := M)) :
      sumSwap ((U.sum U).action g z) = (U.sum U).action g (sumSwap z) := by
    simp only [sumSwap_apply, EquivariantHilbertModule.sum_action_apply,
      sumMk_fst, sumMk_snd]
  change sumSwap (operator (sumSwap ((U.sum U).action g x))) =
    (U.sum U).action g (sumSwap (operator (sumSwap x)))
  rw [hswap, operator_action U, hswap]

theorem pairEquiv_action (g : Γ) (x : CliffordPairModule C (Sum (C := C) (M := M))) :
    pairEquiv ((cliffordPairAction (U.sum U)).action g x) =
      (cliffordPairAction (U.sum U)).action g (pairEquiv x) := by
  apply Prod.ext
  · exact operator_action U g x.1
  · exact oppositeEquiv_action U g x.2

end BC4lean.KKTheory.CliffordOddOddFourier
