import BC4lean.ModuleCompactLocalizedNegativePart
import BC4lean.ModuleCompactEssentialPositivity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Tactic.Module

/-! # Norm closedness of actual positivity modulo module compacts



The existing localized negative-part theorem with localizer 1 proves that
a selfadjoint positive-modulo-compact operator has compact negative part.
For arbitrary operators the exact criterion is compact skew part and
compact negative part of the selfadjoint part. Both compactness conditions
are closed; real continuous functional calculus supplies continuity of the
second map. No Calkin quotient or quotient-positivity assertion is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped Topology

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

local instance essentialPositivityClosedOperatorPartialOrder : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance essentialPositivityClosedOperatorStarOrderedRing : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _

/-- The actual selfadjoint part in the real normed module of operators. -/
def essentialRealPart (T : AdjointableMap B E E) : AdjointableMap B E E :=
  (1 / 2 : ℝ) • (T + star T)

omit [StarOrderedRing B] [CompleteSpace E] in
theorem essentialRealPart_isSelfAdjoint (T : AdjointableMap B E E) :
    IsSelfAdjoint (essentialRealPart T) := by
  change star ((1 / 2 : ℝ) • (T + star T)) = (1 / 2 : ℝ) • (T + star T)
  rw [star_smul, star_trivial, star_add, star_star, add_comm]

theorem continuous_essentialRealPart :
    Continuous (essentialRealPart (B := B) (E := E)) :=
  (continuous_id.add continuous_star).const_smul (1 / 2 : ℝ)

/-- Positivity of an actual lift implies compactness of the skew part. -/
theorem IsPositiveModuloModuleCompact.skew_compact {T : AdjointableMap B E E}
    (hT : IsPositiveModuloModuleCompact T) : IsModuleCompact (T - star T) := by
  obtain ⟨P, hP, herror⟩ := hT
  have heq : T - star T = (T - P) - star (T - P) := by
    rw [star_sub, hP.isSelfAdjoint.star_eq]
    abel
  rw [heq]
  exact herror.sub herror.adjoint

/-- The same positive lift works for the actual selfadjoint part. -/
theorem IsPositiveModuloModuleCompact.realPart {T : AdjointableMap B E E}
    (hT : IsPositiveModuloModuleCompact T) :
    IsPositiveModuloModuleCompact (essentialRealPart T) := by
  obtain ⟨P, hP, herror⟩ := hT
  refine ⟨P, hP, ?_⟩
  have heq : essentialRealPart T - P =
      (1 / 2 : ℝ) • ((T - P) + star (T - P)) := by
    rw [essentialRealPart, star_sub, hP.isSelfAdjoint.star_eq]
    module
  rw [heq]
  exact (herror.add herror.adjoint).real_smul (1 / 2)

/-- The already proved localized negative-part theorem specializes to the
whole selfadjoint operator when the actual localizer is the identity. -/
theorem IsPositiveModuloModuleCompact.negPart_compact
    {T : AdjointableMap B E E} (hT : IsPositiveModuloModuleCompact T)
    (hSA : IsSelfAdjoint T) : IsModuleCompact (T⁻) := by
  have hcomm : IsModuleCompact (T * 1 - 1 * T) := by
    simpa only [mul_one, one_mul, sub_self] using
      (IsModuleCompact.zero (B := B) (E := E) (F := E))
  have hpos : IsPositiveModuloModuleCompact (1 * T * star (1 : AdjointableMap B E E)) := by
    simpa only [one_mul, star_one, mul_one] using hT
  have h := negativePart_localization_isModuleCompact T 1 hSA hcomm hpos
  simpa only [one_mul] using h.1

/-- A compact negative part supplies the actual positive-part lift. -/
theorem isPositiveModuloModuleCompact_of_negPart_compact
    {T : AdjointableMap B E E} (hSA : IsSelfAdjoint T)
    (hneg : IsModuleCompact (T⁻)) : IsPositiveModuloModuleCompact T := by
  refine ⟨T⁺, CFC.posPart_nonneg T, ?_⟩
  have heq : T - T⁺ = -T⁻ := by
    have h := CFC.posPart_sub_negPart T hSA
    calc
      T - T⁺ = (T⁺ - T⁻) - T⁺ := congrArg (fun S => S - T⁺) h.symm
      _ = -T⁻ := by abel
  rw [heq]
  exact hneg.neg

/-- An exact compactness criterion for positive lifts of arbitrary operators. -/
theorem isPositiveModuloModuleCompact_iff_skew_and_negative (T : AdjointableMap B E E) :
    IsPositiveModuloModuleCompact T ↔
      IsModuleCompact (T - star T) ∧ IsModuleCompact ((essentialRealPart T)⁻) := by
  constructor
  · intro hT
    exact ⟨hT.skew_compact,
      hT.realPart.negPart_compact (essentialRealPart_isSelfAdjoint T)⟩
  · rintro ⟨hskew, hneg⟩
    have hreal := isPositiveModuloModuleCompact_of_negPart_compact
      (essentialRealPart_isSelfAdjoint T) hneg
    apply hreal.of_sub_compact
    have heq : T - essentialRealPart T = (1 / 2 : ℝ) • (T - star T) := by
      rw [essentialRealPart]
      module
    rw [heq]
    exact hskew.real_smul (1 / 2)

/-- Real CFC is continuous on the actual selfadjoint part of every operator. -/
theorem continuous_negative_essentialRealPart :
    Continuous (fun T : AdjointableMap B E E => (essentialRealPart T)⁻) := by
  have h := Continuous.cfcₙ_of_mem_nhdsSet
    (s := Set.univ) (fun s : ℝ => s⁻) (by simp)
    (continuous_essentialRealPart (B := B) (E := E))
    (fun T => essentialRealPart_isSelfAdjoint T)
    continuous_negPart.continuousOn (by simp)
  simpa only [← CFC.negPart_def] using h

/-- Positivity modulo the actual closed compact ideal is norm closed. -/
theorem isPositiveModuloModuleCompact_isClosed :
    IsClosed {T : AdjointableMap B E E | IsPositiveModuloModuleCompact T} := by
  have heq : {T : AdjointableMap B E E | IsPositiveModuloModuleCompact T} =
      {T : AdjointableMap B E E | IsModuleCompact (T - star T)} ∩
        {T : AdjointableMap B E E | IsModuleCompact ((essentialRealPart T)⁻)} := by
    ext T
    exact isPositiveModuloModuleCompact_iff_skew_and_negative T
  rw [heq]
  exact (moduleCompact_isClosed.preimage (continuous_id.sub continuous_star)).inter
    (moduleCompact_isClosed.preimage continuous_negative_essentialRealPart)

theorem IsPositiveModuloModuleCompact.of_tendsto
    {I : Type*} {l : Filter I} [l.NeBot]
    {T : I → AdjointableMap B E E} {S : AdjointableMap B E E}
    (hT : Tendsto T l (𝓝 S)) (hpos : ∀ᶠ i in l, IsPositiveModuloModuleCompact (T i)) :
    IsPositiveModuloModuleCompact S :=
  isPositiveModuloModuleCompact_isClosed.mem_of_tendsto hT hpos

section Map
variable {C F : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F]
  [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]

/-- An actual star homomorphism preserving the compact ideal transports
actual star-square lifts. Its positivity conclusion is proved here. -/
theorem IsPositiveModuloModuleCompact.map_of_compact
    (H : AdjointableMap B E E →⋆ₐ[ℂ] AdjointableMap C F F)
    (hH : ∀ K, IsModuleCompact K → IsModuleCompact (H K))
    {T : AdjointableMap B E E} (hT : IsPositiveModuloModuleCompact T) :
    IsPositiveModuloModuleCompact (H T) := by
  obtain ⟨V, hV⟩ := hT.exists_star_square
  apply (isPositiveModuloModuleCompact_iff_star_square _).mpr
  refine ⟨H V, ?_⟩
  simpa only [map_sub, map_mul, map_star] using hH (T - star V * V) hV

end Map
end BC4lean.KKTheory
