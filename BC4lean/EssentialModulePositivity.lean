import BC4lean.CompactModuleOperator
import BC4lean.AdjointableComplete
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic.NoncommRing

/-! # Positive lifts modulo compact module operators

An endomorphism is positive modulo compact operators when it differs from an
actual positive endomorphism by a compact module operator. This is a concrete
positive-lift formulation of the positivity condition used in the Kasparov
product. The order is the spectral C⋆-algebra order on actual adjointable
endomorphisms. No product existence or quotient-order theorem is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

local instance essentialModulePositivityOrder : PartialOrder (AdjointableMap B E E) :=
  CStarAlgebra.spectralOrder _
local instance essentialModulePositivityStarOrdered : StarOrderedRing (AdjointableMap B E E) :=
  CStarAlgebra.spectralOrderedRing _

/-- An actual positive lift of an endomorphism modulo the closed compact ideal. -/
def IsPositiveModuloModuleCompact (T : AdjointableMap B E E) : Prop :=
  ∃ P : AdjointableMap B E E, 0 ≤ P ∧ IsModuleCompact (T - P)

/-- Genuine positive operators supply their own positive lift. -/
theorem isPositiveModuloModuleCompact_of_nonneg {T : AdjointableMap B E E}
    (hT : 0 ≤ T) : IsPositiveModuloModuleCompact T :=
  ⟨T, hT, by simpa using (IsModuleCompact.zero (B := B) (E := E) (F := E))⟩

/-- Every compact operator is zero modulo the compact ideal. -/
theorem IsModuleCompact.isPositiveModuloModuleCompact {T : AdjointableMap B E E}
    (hT : IsModuleCompact T) : IsPositiveModuloModuleCompact T :=
  ⟨0, le_rfl, by simpa using hT⟩

namespace IsPositiveModuloModuleCompact

/-- Positive lifts add, with an actual compact sum of the two errors. -/
theorem add {T U : AdjointableMap B E E}
    (hT : IsPositiveModuloModuleCompact T) (hU : IsPositiveModuloModuleCompact U) :
    IsPositiveModuloModuleCompact (T + U) := by
  obtain ⟨P, hP, hTP⟩ := hT
  obtain ⟨Q, hQ, hUQ⟩ := hU
  refine ⟨P + Q, add_nonneg hP hQ, ?_⟩
  have heq : T + U - (P + Q) = (T - P) + (U - Q) := by abel
  rw [heq]
  exact hTP.add hUQ

/-- A compact perturbation preserves the same actual positive lift. -/
theorem add_compact {T K : AdjointableMap B E E}
    (hT : IsPositiveModuloModuleCompact T) (hK : IsModuleCompact K) :
    IsPositiveModuloModuleCompact (T + K) := by
  obtain ⟨P, hP, hTP⟩ := hT
  refine ⟨P, hP, ?_⟩
  have heq : T + K - P = (T - P) + K := by abel
  rw [heq]
  exact hTP.add hK

/-- Compactly congruent endomorphisms have the same positive-lift condition. -/
theorem of_sub_compact {T U : AdjointableMap B E E}
    (hT : IsPositiveModuloModuleCompact T) (hUT : IsModuleCompact (U - T)) :
    IsPositiveModuloModuleCompact U := by
  have h := hT.add_compact hUT
  have heq : T + (U - T) = U := by abel
  rwa [heq] at h

/-- Adjoint preserves positivity modulo the compact ideal. -/
theorem adjoint {T : AdjointableMap B E E}
    (hT : IsPositiveModuloModuleCompact T) :
    IsPositiveModuloModuleCompact (star T) := by
  obtain ⟨P, hP, hTP⟩ := hT
  refine ⟨P, hP, ?_⟩
  have h := hTP.adjoint
  change IsModuleCompact (star (T - P)) at h
  simpa only [star_sub, hP.isSelfAdjoint.star_eq] using h

/-- A positive lift is a star square in the actual complete endomorphism algebra. -/
theorem exists_star_square {T : AdjointableMap B E E}
    (hT : IsPositiveModuloModuleCompact T) :
    ∃ V : AdjointableMap B E E, IsModuleCompact (T - star V * V) := by
  obtain ⟨P, hP, hTP⟩ := hT
  refine ⟨CFC.sqrt P, ?_⟩
  simpa only [(CFC.sqrt_nonneg P).isSelfAdjoint.star_eq,
    CFC.sqrt_mul_sqrt_self P hP] using hTP

/-- Compression of a positive lift is positive, and its compact error is compressed. -/
theorem star_right_conjugate {T : AdjointableMap B E E}
    (hT : IsPositiveModuloModuleCompact T) (S : AdjointableMap B E E) :
    IsPositiveModuloModuleCompact (S * T * star S) := by
  obtain ⟨P, hP, hTP⟩ := hT
  refine ⟨S * P * star S, star_right_conjugate_nonneg hP S, ?_⟩
  have heq : S * T * star S - S * P * star S = S * (T - P) * star S := by
    noncomm_ring
  rw [heq]
  exact mul_mem_moduleCompact_right (mul_mem_moduleCompact_left S hTP) (star S)

/-- The left-star compression is likewise positive modulo compacts. -/
theorem star_left_conjugate {T : AdjointableMap B E E}
    (hT : IsPositiveModuloModuleCompact T) (S : AdjointableMap B E E) :
    IsPositiveModuloModuleCompact (star S * T * S) := by
  simpa only [star_star] using hT.star_right_conjugate (star S)

end IsPositiveModuloModuleCompact

/-- The positive-lift formulation is exactly the actual star-square lift condition. -/
theorem isPositiveModuloModuleCompact_iff_star_square (T : AdjointableMap B E E) :
    IsPositiveModuloModuleCompact T ↔
      ∃ V : AdjointableMap B E E, IsModuleCompact (T - star V * V) := by
  constructor
  · exact IsPositiveModuloModuleCompact.exists_star_square
  · rintro ⟨V, hV⟩
    exact ⟨star V * V, star_mul_self_nonneg V, hV⟩

/-- Compact congruence does not change the positive-lift condition. -/
theorem isPositiveModuloModuleCompact_iff_of_sub_compact
    {T U : AdjointableMap B E E} (hUT : IsModuleCompact (U - T)) :
    IsPositiveModuloModuleCompact T ↔ IsPositiveModuloModuleCompact U := by
  constructor
  · exact fun h => h.of_sub_compact hUT
  · intro h
    apply h.of_sub_compact
    simpa only [neg_sub] using hUT.neg

end BC4lean.KKTheory
