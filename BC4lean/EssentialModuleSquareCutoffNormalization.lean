import BC4lean.EssentialModuleSpectrumCutoff
import BC4lean.ModuleSquareCutoffNormalization

/-! # Local compact square defects from essential spectral lower bounds

The actual continuous square-cutoff normalizer has locally compact square
defect whenever the original selfadjoint square has a localized positive
lower bound modulo actual compact operators. In particular the product
path lower bound `1/2` permits the cutoff `1/4`. This applies the actual
essential low-spectrum theorem rather than assuming a global spectral gap.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

local instance standardEssentialModuleSquareCutoffNormalizationLocalInstance01 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance standardEssentialModuleSquareCutoffNormalizationLocalInstance02 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _

/-- The scalar square-cutoff defect is compact at each actual localizer
whose square lower bound is essentially larger than the positive cutoff. -/
theorem moduleSquareCutoffDefect_mul_isModuleCompact_of_essential_lowerBound
    (Q X : AdjointableMap B E E) (hQ : IsSelfAdjoint Q)
    (δ k : ℝ) (hk : 0 < k) (hgap : k < δ)
    (hcomm : IsModuleCompact (Q * X - X * Q))
    (hlower : IsPositiveModuloModuleCompact
      (X * (Q - algebraMap ℝ (AdjointableMap B E E) δ) * star X)) :
    IsModuleCompact (cfc (moduleSquareCutoffDefect k) Q * X) :=
  cfc_mul_isModuleCompact_of_essential_lowerBound Q X hQ δ k hgap hcomm hlower
    (moduleSquareCutoffDefect k) (continuous_moduleSquareCutoffDefect hk)
    (fun _s hs => moduleSquareCutoffDefect_eq_zero hk hs)

/-- Essential localized square positivity makes the actual normalized
selfadjoint operator's square defect locally compact. -/
theorem moduleSquareCutoffNormalization_square_mul_isModuleCompact_of_essential_lowerBound
    (H X : AdjointableMap B E E) (hH : IsSelfAdjoint H)
    (δ k : ℝ) (hk : 0 < k) (hgap : k < δ)
    (hcomm : IsModuleCompact ((H * H) * X - X * (H * H)))
    (hlower : IsPositiveModuloModuleCompact
      (X * (H * H - algebraMap ℝ (AdjointableMap B E E) δ) * star X)) :
    IsModuleCompact ((moduleSquareCutoffNormalization k H *
      moduleSquareCutoffNormalization k H - 1) * X) := by
  rw [moduleSquareCutoffNormalization_square_defect hk H hH]
  have hQ : IsSelfAdjoint (H * H) := by
    change star (H * H) = H * H
    simp only [star_mul, hH.star_eq]
  exact moduleSquareCutoffDefect_mul_isModuleCompact_of_essential_lowerBound
    (H * H) X hQ δ k hk hgap hcomm hlower

/-- The genuine product convex-path lower bound one half yields an actual
locally compact normalized square defect with cutoff one quarter. -/
theorem quarterSquareCutoffNormalization_square_mul_isModuleCompact
    (H X : AdjointableMap B E E) (hH : IsSelfAdjoint H)
    (hcomm : IsModuleCompact ((H * H) * X - X * (H * H)))
    (hlower : IsPositiveModuloModuleCompact
      (X * (H * H - algebraMap ℝ (AdjointableMap B E E) (1 / 2)) * star X)) :
    IsModuleCompact ((moduleSquareCutoffNormalization (1 / 4) H *
      moduleSquareCutoffNormalization (1 / 4) H - 1) * X) :=
  moduleSquareCutoffNormalization_square_mul_isModuleCompact_of_essential_lowerBound
    H X hH (1 / 2) (1 / 4) (by norm_num) (by norm_num) hcomm hlower

end BC4lean.KKTheory
