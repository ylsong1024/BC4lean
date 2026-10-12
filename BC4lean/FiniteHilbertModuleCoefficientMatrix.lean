import BC4lean.FiniteHilbertModuleSum
import BC4lean.NonunitalOperatorK
import BC4lean.FiniteModuleCompactMatrix

/-! # Actual finite matrix actions of a compact coefficient representation

The forced unitization extends the given actual nonunital representation.
Its matrix action is unital. Equality of full scalar matrices makes every
entry difference genuinely compact, so a scalar-identity matrix unitary
gives a compact unitary on the actual finite sum of the represented module.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BC4lean.KKTheory
open scoped CStarAlgebra
open BC4lean.OperatorKTheory

variable {A B E ι : Type*} [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E] [Fintype ι] [DecidableEq ι]

local instance oddContinuationFiniteHilbertModuleCoefficientMatrixLocalInstance01 : PartialOrder (Unitization ℂ A) := CStarAlgebra.spectralOrder _
local instance oddContinuationFiniteHilbertModuleCoefficientMatrixLocalInstance02 : StarOrderedRing (Unitization ℂ A) := CStarAlgebra.spectralOrderedRing _
local instance oddContinuationFiniteHilbertModuleCoefficientMatrixLocalInstance03 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance oddContinuationFiniteHilbertModuleCoefficientMatrixLocalInstance04 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _
local instance oddContinuationFiniteHilbertModuleCoefficientMatrixLocalInstance05 : CompleteSpace (FiniteHilbertModuleSum B E ι) := finiteHilbertModuleSum_complete

def finiteHilbertModuleCoefficientMatrixHom (ρ : A →⋆ₙₐ[ℂ] AdjointableMap B E E) :
    CStarMatrix ι ι (Unitization ℂ A) →⋆ₐ[ℂ]
      AdjointableMap B (FiniteHilbertModuleSum B E ι) (FiniteHilbertModuleSum B E ι) :=
  finiteHilbertModuleMatrixHom.comp (matrixMap (Unitization.starLift ρ))

@[simp] theorem finiteHilbertModuleCoefficientMatrixHom_apply
    (ρ : A →⋆ₙₐ[ℂ] AdjointableMap B E E) (M : CStarMatrix ι ι (Unitization ℂ A))
    (x : FiniteHilbertModuleSum B E ι) (i : ι) :
    finiteHilbertModuleCoefficientMatrixHom ρ M x i =
      ∑ j, Unitization.starLift ρ (M i j) (x j) := by
  change finiteHilbertModuleOperatorMatrix (fun i j => Unitization.starLift ρ (M i j)) x i = _
  rw [finiteHilbertModuleOperatorMatrix_apply]

omit [StarOrderedRing B] [CompleteSpace E] in
theorem finiteHilbertModuleCoefficientMatrix_sub_entry
    (ρ : A →⋆ₙₐ[ℂ] AdjointableMap B E E) (a b : Unitization ℂ A) (h : a.fst = b.fst) :
    Unitization.starLift ρ a - Unitization.starLift ρ b = ρ (a.snd - b.snd) := by
  change (algebraMap ℂ (AdjointableMap B E E) a.fst + ρ a.snd) -
    (algebraMap ℂ (AdjointableMap B E E) b.fst + ρ b.snd) = _
  rw [h, map_sub]
  abel

theorem finiteHilbertModuleCoefficientMatrix_sub_compact
    (ρ : A →⋆ₙₐ[ℂ] AdjointableMap B E E) (hρ : ∀ a, IsModuleCompact (ρ a))
    (M N : CStarMatrix ι ι (Unitization ℂ A))
    (hScalar : ∀ i j, (M i j).fst = (N i j).fst) :
    IsModuleCompact (finiteHilbertModuleCoefficientMatrixHom ρ M -
      finiteHilbertModuleCoefficientMatrixHom ρ N) := by
  have he : finiteHilbertModuleCoefficientMatrixHom ρ M - finiteHilbertModuleCoefficientMatrixHom ρ N =
      finiteHilbertModuleOperatorMatrix (fun i j => ρ ((M i j).snd - (N i j).snd)) := by
    ext x i
    simp only [AdjointableMap.coe_sub_apply, WithCStarModule.sub_apply,
      finiteHilbertModuleCoefficientMatrixHom_apply, finiteHilbertModuleOperatorMatrix_apply,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have h := congrArg (fun T : AdjointableMap B E E => T (x j))
      (finiteHilbertModuleCoefficientMatrix_sub_entry ρ (M i j) (N i j) (hScalar i j))
    simpa only [AdjointableMap.coe_sub_apply] using h
  rw [he]
  exact finiteHilbertModuleOperatorMatrix_compact _ (fun i j => hρ _)

def finiteHilbertModuleCoefficientUnitary
    (ρ : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (u : unitary (CStarMatrix ι ι (Unitization ℂ A))) :
    unitary (AdjointableMap B (FiniteHilbertModuleSum B E ι) (FiniteHilbertModuleSum B E ι)) :=
  ⟨finiteHilbertModuleCoefficientMatrixHom ρ (u : CStarMatrix ι ι (Unitization ℂ A)),
    Unitary.map_mem (finiteHilbertModuleCoefficientMatrixHom ρ) u.property⟩

theorem finiteHilbertModuleCoefficientUnitary_compact
    (ρ : A →⋆ₙₐ[ℂ] AdjointableMap B E E) (hρ : ∀ a, IsModuleCompact (ρ a))
    (u : unitary (CStarMatrix ι ι (Unitization ℂ A)))
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ A)) = 1) :
    IsModuleCompact ((finiteHilbertModuleCoefficientUnitary ρ u :
      AdjointableMap B (FiniteHilbertModuleSum B E ι) (FiniteHilbertModuleSum B E ι)) - 1) := by
  change IsModuleCompact (finiteHilbertModuleCoefficientMatrixHom ρ
    (u : CStarMatrix ι ι (Unitization ℂ A)) - 1)
  rw [← map_one (finiteHilbertModuleCoefficientMatrixHom ρ)]
  apply finiteHilbertModuleCoefficientMatrix_sub_compact ρ hρ
  intro i j
  have hi := congrArg (fun M => M i j) hu
  change ((u : CStarMatrix ι ι (Unitization ℂ A)) i j).fst =
    (1 : CStarMatrix ι ι ℂ) i j at hi
  by_cases hij : i = j <;> simpa [CStarMatrix.one_apply, hij] using hi

end BC4lean.KKTheory
