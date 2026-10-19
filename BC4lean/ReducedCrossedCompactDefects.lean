import BC4lean.ReducedCrossedNorm
import BC4lean.CompactModuleOperator
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Tactic.NoncommRing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Compact defect closure on the genuine reduced source algebra

These generic analytic lemmas use the actual reduced
completion and arbitrary actual target Hilbert modules. They assume only generator
compactness for the operator family in question, never a descended-cycle record.
-/

noncomputable section
namespace BC4lean.KKTheory.ReducedCrossedDefects
open scoped CStarAlgebra

variable {Γ A C H : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H]
  [CStarModule Cᵐᵒᵖ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- A continuous additive operator family is compact on the whole actual
reduced source algebra once it is compact on the concrete finite generators. -/
theorem continuous_additive_compact_of_generators
    (α : CStarAlgebraAction Γ A)
    (L : ReducedCrossedProduct α →+
      AdjointableMap C H H)
    (hL : Continuous L)
    (hgen : ∀ (g : Γ) (a : A), IsModuleCompact
      (L (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a))))
    (z : ReducedCrossedProduct α) : IsModuleCompact (L z) := by
  have hfinite : ∀ f : AlgebraicCrossedProduct α,
      IsModuleCompact (L (algebraicToReducedCrossed α f)) := by
    intro f
    induction f using AlgebraicCrossedProduct.induction_on α with
    | zero => simpa only [map_zero] using
        (IsModuleCompact.zero (B := C) (E := H) (F := H))
    | single g a => exact hgen g a
    | add f h ihf ihh => simpa only [map_add] using ihf.add ihh
  exact (algebraicToReducedCrossed_denseRange α).induction_on z
    (moduleCompact_isClosed.preimage hL) hfinite

/-- Once an actual integrated source representation exists, generator
adjoint defects suffice for all source elements by the genuine reduced norm. -/
theorem integrated_selfadjoint_compact_of_generators
    (α : CStarAlgebraAction Γ A)
    (ρ : ReducedCrossedProduct α →⋆ₙₐ[ℂ]
      AdjointableMap C H H)
    (T : AdjointableMap C H H)
    (hgen : ∀ (g : Γ) (a : A), IsModuleCompact
      ((T - star T) * ρ (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a))))
    (z : ReducedCrossedProduct α) : IsModuleCompact ((T - star T) * ρ z) := by
  let L : ReducedCrossedProduct α →+
      AdjointableMap C H H :=
    { toFun := fun z => (T - star T) * ρ z
      map_zero' := by simp
      map_add' := fun x y => by simp only [map_add, mul_add] }
  exact continuous_additive_compact_of_generators α L
    (continuous_const.mul (map_continuous ρ)) hgen z

theorem integrated_square_compact_of_generators
    (α : CStarAlgebraAction Γ A)
    (ρ : ReducedCrossedProduct α →⋆ₙₐ[ℂ]
      AdjointableMap C H H)
    (T : AdjointableMap C H H)
    (hgen : ∀ (g : Γ) (a : A), IsModuleCompact
      ((T * T - 1) * ρ (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a))))
    (z : ReducedCrossedProduct α) : IsModuleCompact ((T * T - 1) * ρ z) := by
  let L : ReducedCrossedProduct α →+
      AdjointableMap C H H :=
    { toFun := fun z => (T * T - 1) * ρ z
      map_zero' := by simp
      map_add' := fun x y => by simp only [map_add, mul_add] }
  exact continuous_additive_compact_of_generators α L
    (continuous_const.mul (map_continuous ρ)) hgen z

theorem integrated_commutator_compact_of_generators
    (α : CStarAlgebraAction Γ A)
    (ρ : ReducedCrossedProduct α →⋆ₙₐ[ℂ]
      AdjointableMap C H H)
    (T : AdjointableMap C H H)
    (hgen : ∀ (g : Γ) (a : A), IsModuleCompact
      (T * ρ (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a)) -
        ρ (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a)) * T))
    (z : ReducedCrossedProduct α) : IsModuleCompact (T * ρ z - ρ z * T) := by
  let L : ReducedCrossedProduct α →+
      AdjointableMap C H H :=
    { toFun := fun z => T * ρ z - ρ z * T
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [map_add, mul_add, add_mul]
        noncomm_ring }
  exact continuous_additive_compact_of_generators α L
    ((continuous_const.mul (map_continuous ρ)).sub
      ((map_continuous ρ).mul continuous_const)) hgen z


end BC4lean.KKTheory.ReducedCrossedDefects
