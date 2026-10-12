import BC4lean.EssentialModulePositivity
import BC4lean.RectangularModuleFibreOperator
import BC4lean.HilbertModuleEquiv

/-! # Positive lifts under genuine fibre evaluation and unitary transport

The lift is written as an actual star square before applying the fibre
homomorphism or the unitary star equivalence. The error remains in the
genuine module compact ideal. No order on an unconstructed quotient is used.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B X M E F : Type*} [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, B)ᵐᵒᵖ M]
  [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
  [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]

omit [T2Space X] in
theorem IsPositiveModuloModuleCompact.fibre
    {T : AdjointableMap C(X, B) M M} (hT : IsPositiveModuloModuleCompact T) (t : X) :
    IsPositiveModuloModuleCompact (hilbertModuleFibreOperator t T) := by
  obtain ⟨V, hV⟩ := hT.exists_star_square
  apply (isPositiveModuloModuleCompact_iff_star_square _).2
  refine ⟨hilbertModuleFibreOperator t V, ?_⟩
  simpa only [hilbertModuleFibreOperator_sub, hilbertModuleFibreOperator_mul,
    hilbertModuleFibreOperator_star] using hV.fibre t

theorem IsPositiveModuloModuleCompact.transport
    {T : AdjointableMap B E E} (hT : IsPositiveModuloModuleCompact T)
    (u : HilbertModuleEquiv B E F) : IsPositiveModuloModuleCompact (u.transport T) := by
  obtain ⟨V, hV⟩ := hT.exists_star_square
  apply (isPositiveModuloModuleCompact_iff_star_square _).2
  refine ⟨u.transport V, ?_⟩
  simpa only [HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_mul,
    HilbertModuleEquiv.transport_star] using (u.transport_isModuleCompact_iff _).2 hV

end BC4lean.KKTheory
