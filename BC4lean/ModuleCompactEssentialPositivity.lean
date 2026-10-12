import BC4lean.ModuleCompactOrderHereditary
import BC4lean.ModuleCompactPositivePart
import BC4lean.EssentialModulePositivity
import Mathlib.Tactic.NoncommRing

/-! # Order bounds and positive lifts in the actual compact ideal

A positive operator with an essentially nonpositive image is compact.
The concrete positive lift supplies a positive compact upper bound, to
which the genuine compact order-heredity theorem applies. A separate
wrapper permits a selfadjoint compact upper bound by taking its actual
compact positive part.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

local instance standardModuleCompactEssentialPositivityLocalInstance01 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance standardModuleCompactEssentialPositivityLocalInstance02 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _

namespace IsModuleCompact

omit [CompleteSpace E] in
/-- Real scalar multiplication preserves the actual complex compact ideal. -/
theorem real_smul {T : AdjointableMap B E E} (hT : IsModuleCompact T) (r : ℝ) :
    IsModuleCompact (r • T) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r T]
  exact hT.smul (r : ℂ)

/-- A selfadjoint compact upper bound can be replaced by its actual compact
positive part before applying order heredity. -/
theorem of_nonneg_of_le_selfAdjoint {T K : AdjointableMap B E E}
    (hK : IsModuleCompact K) (hKSA : IsSelfAdjoint K) (hT : 0 ≤ T) (hTK : T ≤ K) :
    IsModuleCompact T :=
  (hK.posPart hKSA).of_nonneg_of_le hT (hTK.trans (CFC.le_posPart hKSA))

end IsModuleCompact

/-- A positive operator whose negative has a positive lift modulo actual
compact operators is compact. The compact upper bound is `T + P`, where
`P` is the genuine positive lift of `-T`. -/
theorem isModuleCompact_of_nonneg_of_neg_positiveModuloModuleCompact
    {T : AdjointableMap B E E} (hT : 0 ≤ T)
    (hneg : IsPositiveModuloModuleCompact (-T)) : IsModuleCompact T := by
  obtain ⟨P, hP, herror⟩ := hneg
  have hupper : IsModuleCompact (T + P) := by
    have h := herror.neg
    have heq : -((-T) - P) = T + P := by abel
    rwa [heq] at h
  exact hupper.of_nonneg_of_le hT (le_add_of_nonneg_right hP)

omit [CompleteSpace E] in
/-- Compact perturbations of a localizing map induce compact perturbations
of its actual compression of any endomorphism. -/
theorem moduleCompact_star_right_conjugate_sub
    (S T R : AdjointableMap B E E) (hTS : IsModuleCompact (T - S)) :
    IsModuleCompact (T * R * star T - S * R * star S) := by
  have hstar : IsModuleCompact (star T - star S) := by
    have h := hTS.adjoint
    change IsModuleCompact (star (T - S)) at h
    simpa only [star_sub] using h
  have heq : T * R * star T - S * R * star S =
      (T - S) * R * star T + S * R * (star T - star S) := by noncomm_ring
  rw [heq]
  have hleft : IsModuleCompact ((T - S) * R * star T) :=
    mul_mem_moduleCompact_right (mul_mem_moduleCompact_right hTS R) (star T)
  have hright : IsModuleCompact (S * R * (star T - star S)) :=
    mul_mem_moduleCompact_left (S * R) hstar
  exact hleft.add hright

end BC4lean.KKTheory
