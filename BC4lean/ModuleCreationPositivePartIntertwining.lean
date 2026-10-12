import BC4lean.ModuleCompactLocalizedNegativePart
import BC4lean.ModuleCreationLocalCompactCFC

/-! # Positive-part residuals of genuine even creation connections

An actual selfadjoint tensor operator intertwining the creation maps with a
selfadjoint second operator has compact positive-part intertwining errors.
If the second operator is positive modulo compacts after every coefficient
compression and commutes with coefficients modulo compacts, its negative
part is locally compact by actual norm limits of separated spectral cutoffs.
The resulting tensor residual is therefore creation-locally compact.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B C E F : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)

local instance standardModuleCreationPositivePartIntertwiningLocalInstance01 : PartialOrder (AdjointableMap C F F) := CStarAlgebra.spectralOrder _
local instance standardModuleCreationPositivePartIntertwiningLocalInstance02 : StarOrderedRing (AdjointableMap C F F) := CStarAlgebra.spectralOrderedRing _
local instance standardModuleCreationPositivePartIntertwiningLocalInstance03 : PartialOrder
    (AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ)) :=
  CStarAlgebra.spectralOrder _
local instance standardModuleCreationPositivePartIntertwiningLocalInstance04 : StarOrderedRing
    (AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ)) :=
  CStarAlgebra.spectralOrderedRing _

/-- Actual rectangular CFC intertwining specializes to the positive parts. -/
theorem creation_posPart_intertwining_isModuleCompact
    (T : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ))
    (S : AdjointableMap C F F) (hT : IsSelfAdjoint T) (hS : IsSelfAdjoint S)
    (x : E) (hx : IsModuleCompact (T.comp (moduleCreationMap φ x) -
      (moduleCreationMap φ x).comp S)) :
    IsModuleCompact (T⁺.comp (moduleCreationMap φ x) - (moduleCreationMap φ x).comp S⁺) := by
  have h := cfc_intertwining_isModuleCompact T S hT hS (moduleCreationMap φ x) hx
    (fun s : ℝ => max s 0) (continuous_id.max continuous_const)
  have hTpart : cfc (fun s : ℝ => max s 0) T = T⁺ := by
    rw [CFC.posPart_def]
    simp only [_root_.posPart_def]
    exact (cfcₙ_eq_cfc (a := T) (f := fun s : ℝ => max s 0)
      (hf := (continuous_id.max continuous_const).continuousOn) (hf0 := by simp)).symm
  have hSpart : cfc (fun s : ℝ => max s 0) S = S⁺ := by
    rw [CFC.posPart_def]
    simp only [_root_.posPart_def]
    exact (cfcₙ_eq_cfc (a := S) (f := fun s : ℝ => max s 0)
      (hf := (continuous_id.max continuous_const).continuousOn) (hf0 := by simp)).symm
  simpa only [hTpart, hSpart] using h

/-- The actual coefficient-local positivity, rather than a global
essential positive lift, suffices for the creation-local residual. -/
theorem creation_sub_posPart_isCreationLocallyCompact
    (T : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ))
    (S : AdjointableMap C F F) (hT : IsSelfAdjoint T) (hS : IsSelfAdjoint S)
    (hconnection : ∀ x : E, IsModuleCompact (T.comp (moduleCreationMap φ x) -
      (moduleCreationMap φ x).comp S))
    (hcomm : ∀ b : B, IsModuleCompact (S * φ b - φ b * S))
    (hpositive : ∀ b : B, IsPositiveModuloModuleCompact (φ b * S * star (φ b))) :
    IsCreationLocallyCompact φ (T - T⁺) := by
  apply IsCreationLocallyCompact.of_selfadjoint (hT.sub (CFC.posPart_nonneg T).isSelfAdjoint)
  intro x
  have hsecond := moduleCreationMap_comp_isModuleCompact_of_left_local φ x (S - S⁺)
    (fun b => (sub_posPart_localization_isModuleCompact S (φ b) hS (hcomm b) (hpositive b)).1)
  have h := ((hconnection x).sub
    (creation_posPart_intertwining_isModuleCompact φ T S hT hS x (hconnection x))).add hsecond
  convert h using 1
  apply AdjointableMap.ext
  intro y
  simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
    AdjointableMap.coe_add_apply, map_sub]
  abel

end BC4lean.KKTheory
