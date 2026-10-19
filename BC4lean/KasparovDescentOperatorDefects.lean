import BC4lean.KasparovDescentAction
import BC4lean.KasparovCycle
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Tactic.NoncommRing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Actual operator defects after crossed coefficient extension

This file uses the constructed module E tensor_B (B crossed_r Gamma) and
the constructed first-factor operator homomorphism. Every compactness result
is deduced from an actual source-module compactness hypothesis or the actual
raw Kasparov-cycle conditions. The generator commutator identity isolates
only its operator intertwining equation; no descended-cycle condition,
integrated representation, homotopy map, or product law is assumed.


-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent

open scoped KasparovDescent CStarAlgebra

variable {Γ A B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

variable (β : CStarAlgebraAction Γ B)

/-- Localized adjoint defects pass through the actual tensor star homomorphism. -/
theorem operatorHom_selfadjoint_defect (T K : AdjointableMap B E E)
    (h : IsModuleCompact ((T - star T) * K)) :
    IsModuleCompact ((operatorHom β E T - star (operatorHom β E T)) *
      operatorHom β E K) := by
  have h' := operatorHom_compact β E h
  simpa only [map_mul, map_sub, map_star] using h'

/-- The unital tensor operator map gives the genuine square defect. -/
theorem operatorHom_square_defect (T K : AdjointableMap B E E)
    (h : IsModuleCompact ((T * T - 1) * K)) :
    IsModuleCompact ((operatorHom β E T * operatorHom β E T - 1) *
      operatorHom β E K) := by
  have h' := operatorHom_compact β E h
  simpa only [map_mul, map_sub, map_one] using h'

/-- Both the ordinary and the graded source commutator pass through the
actual tensor map; K and L need not coincide. -/
theorem operatorHom_commutator_defect (T K L : AdjointableMap B E E)
    (h : IsModuleCompact (T * K - L * T)) :
    IsModuleCompact (operatorHom β E T * operatorHom β E K -
      operatorHom β E L * operatorHom β E T) := by
  have h' := operatorHom_compact β E h
  simpa only [map_sub, map_mul] using h'

/-- Right multiplication of a compact lifted defect by a concrete generator
multiplier preserves compactness. -/
theorem operatorHom_localized_mul_right (T K : AdjointableMap B E E)
    (V : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E))
    (h : IsModuleCompact (T * K)) :
    IsModuleCompact (operatorHom β E T * (operatorHom β E K * V)) := by
  have h' := mul_mem_moduleCompact_right (operatorHom_compact β E h) V
  simpa only [IsModuleCompact, map_mul, mul_assoc] using h'

private theorem generator_commutator_ring_identity {R : Type*} [Ring R]
    (t s k v : R) (h : t * v = v * s) :
    t * (v * k) - (v * k) * t = v * ((s - t) * k + (t * k - k * t)) := by
  calc
    _ = (t * v) * k - v * (k * t) := by noncomm_ring
    _ = (v * s) * k - v * (k * t) :=
      congrArg (fun r : R => r * k - v * (k * t)) h
    _ = _ := by noncomm_ring

/-- The generator commutator has a right-localized group error. This
orientation avoids assuming global equivariance or extra selfadjointness. -/
theorem operatorHom_generator_commutator_identity
    (T S K : AdjointableMap B E E)
    (V : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E))
    (hV : operatorHom β E T * V = V * operatorHom β E S) :
    operatorHom β E T * (V * operatorHom β E K) -
        (V * operatorHom β E K) * operatorHom β E T =
      V * operatorHom β E ((S - T) * K + (T * K - K * T)) := by
  simp only [map_add, map_sub, map_mul]
  exact generator_commutator_ring_identity (operatorHom β E T)
    (operatorHom β E S) (operatorHom β E K) V hV

/-- Actual localized compactness of the original commutator and group
defect proves compactness at a group-first integrated generator. -/
theorem operatorHom_generator_commutator_compact
    (T S K : AdjointableMap B E E)
    (V : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E))
    (hV : operatorHom β E T * V = V * operatorHom β E S)
    (heq : IsModuleCompact ((S - T) * K))
    (hcomm : IsModuleCompact (T * K - K * T)) :
    IsModuleCompact (operatorHom β E T * (V * operatorHom β E K) -
      (V * operatorHom β E K) * operatorHom β E T) := by
  rw [operatorHom_generator_commutator_identity β T S K V hV]
  exact mul_mem_moduleCompact_left V (operatorHom_compact β E (heq.add hcomm))

variable {α : CStarAlgebraAction Γ A}

theorem even_coefficient_selfadjoint_compact (c : KasparovCycle α β E) (a : A) :
    IsModuleCompact ((operatorHom β E c.operator - star (operatorHom β E c.operator)) *
      sourceRepresentation β E c.representation a) :=
  operatorHom_selfadjoint_defect β c.operator (c.representation a)
    (c.selfadjoint_mod_compact a)

theorem even_coefficient_square_compact (c : KasparovCycle α β E) (a : A) :
    IsModuleCompact ((operatorHom β E c.operator * operatorHom β E c.operator - 1) *
      sourceRepresentation β E c.representation a) :=
  operatorHom_square_defect β c.operator (c.representation a) (c.square_mod_compact a)

theorem even_coefficient_commutator_compact (c : KasparovCycle α β E) (a : A) :
    IsModuleCompact (operatorHom β E c.operator * sourceRepresentation β E c.representation a -
      sourceRepresentation β E c.representation a * operatorHom β E c.operator) :=
  operatorHom_commutator_defect β c.operator (c.representation a) (c.representation a)
    (c.commutator_compact a)

theorem odd_coefficient_selfadjoint_compact (c : OddKasparovCycle α β E) (a : A) :
    IsModuleCompact ((operatorHom β E c.operator - star (operatorHom β E c.operator)) *
      sourceRepresentation β E c.representation a) :=
  operatorHom_selfadjoint_defect β c.operator (c.representation a)
    (c.selfadjoint_mod_compact a)

theorem odd_coefficient_square_compact (c : OddKasparovCycle α β E) (a : A) :
    IsModuleCompact ((operatorHom β E c.operator * operatorHom β E c.operator - 1) *
      sourceRepresentation β E c.representation a) :=
  operatorHom_square_defect β c.operator (c.representation a) (c.square_mod_compact a)

theorem odd_coefficient_commutator_compact (c : OddKasparovCycle α β E) (a : A) :
    IsModuleCompact (operatorHom β E c.operator * sourceRepresentation β E c.representation a -
      sourceRepresentation β E c.representation a * operatorHom β E c.operator) :=
  operatorHom_commutator_defect β c.operator (c.representation a) (c.representation a)
    (c.commutator_compact a)

/-- On an actual raw even cycle the only group input needed here is the
intertwining equation, which the concrete balanced group operator supplies. -/
theorem even_generator_commutator_compact (c : KasparovCycle α β E) (g : Γ) (a : A)
    (V : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E))
    (hV : operatorHom β E c.operator * V =
      V * operatorHom β E (c.groupAction.conjugateOperator g⁻¹ c.operator)) :
    IsModuleCompact (operatorHom β E c.operator *
        (V * sourceRepresentation β E c.representation a) -
      (V * sourceRepresentation β E c.representation a) * operatorHom β E c.operator) :=
  operatorHom_generator_commutator_compact β c.operator
    (c.groupAction.conjugateOperator g⁻¹ c.operator) (c.representation a) V hV
    (c.equivariance_mod_compact g⁻¹ a) (c.commutator_compact a)

theorem odd_generator_commutator_compact (c : OddKasparovCycle α β E) (g : Γ) (a : A)
    (V : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E))
    (hV : operatorHom β E c.operator * V =
      V * operatorHom β E (c.groupAction.conjugateOperator g⁻¹ c.operator)) :
    IsModuleCompact (operatorHom β E c.operator *
        (V * sourceRepresentation β E c.representation a) -
      (V * sourceRepresentation β E c.representation a) * operatorHom β E c.operator) :=
  operatorHom_generator_commutator_compact β c.operator
    (c.groupAction.conjugateOperator g⁻¹ c.operator) (c.representation a) V hV
    (c.equivariance_mod_compact g⁻¹ a) (c.commutator_compact a)

section Closure

variable [PartialOrder A] [StarOrderedRing A]

/-- A continuous additive operator family is compact on the whole actual
reduced source algebra once it is compact on the concrete finite generators. -/
theorem continuous_additive_compact_of_generators
    (α : CStarAlgebraAction Γ A)
    (L : ReducedCrossedProduct α →+
      AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E))
    (hL : Continuous L)
    (hgen : ∀ (g : Γ) (a : A), IsModuleCompact
      (L (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a))))
    (z : ReducedCrossedProduct α) : IsModuleCompact (L z) := by
  have hfinite : ∀ f : AlgebraicCrossedProduct α,
      IsModuleCompact (L (algebraicToReducedCrossed α f)) := by
    intro f
    induction f using AlgebraicCrossedProduct.induction_on α with
    | zero => simpa only [map_zero] using
        (IsModuleCompact.zero (B := ReducedCrossedProduct β) (E := Module β E) (F := Module β E))
    | single g a => exact hgen g a
    | add f h ihf ihh => simpa only [map_add] using ihf.add ihh
  exact (algebraicToReducedCrossed_denseRange α).induction_on z
    (moduleCompact_isClosed.preimage hL) hfinite

/-- Once an actual integrated source representation exists, generator
adjoint defects suffice for all source elements by the genuine reduced norm. -/
theorem integrated_selfadjoint_compact_of_generators
    (α : CStarAlgebraAction Γ A)
    (ρ : ReducedCrossedProduct α →⋆ₙₐ[ℂ]
      AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E))
    (T : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E))
    (hgen : ∀ (g : Γ) (a : A), IsModuleCompact
      ((T - star T) * ρ (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a))))
    (z : ReducedCrossedProduct α) : IsModuleCompact ((T - star T) * ρ z) := by
  let L : ReducedCrossedProduct α →+
      AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) :=
    { toFun := fun z => (T - star T) * ρ z
      map_zero' := by simp
      map_add' := fun x y => by simp only [map_add, mul_add] }
  exact continuous_additive_compact_of_generators β α L
    (continuous_const.mul (map_continuous ρ)) hgen z

theorem integrated_square_compact_of_generators
    (α : CStarAlgebraAction Γ A)
    (ρ : ReducedCrossedProduct α →⋆ₙₐ[ℂ]
      AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E))
    (T : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E))
    (hgen : ∀ (g : Γ) (a : A), IsModuleCompact
      ((T * T - 1) * ρ (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a))))
    (z : ReducedCrossedProduct α) : IsModuleCompact ((T * T - 1) * ρ z) := by
  let L : ReducedCrossedProduct α →+
      AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) :=
    { toFun := fun z => (T * T - 1) * ρ z
      map_zero' := by simp
      map_add' := fun x y => by simp only [map_add, mul_add] }
  exact continuous_additive_compact_of_generators β α L
    (continuous_const.mul (map_continuous ρ)) hgen z

theorem integrated_commutator_compact_of_generators
    (α : CStarAlgebraAction Γ A)
    (ρ : ReducedCrossedProduct α →⋆ₙₐ[ℂ]
      AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E))
    (T : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E))
    (hgen : ∀ (g : Γ) (a : A), IsModuleCompact
      (T * ρ (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a)) -
        ρ (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a)) * T))
    (z : ReducedCrossedProduct α) : IsModuleCompact (T * ρ z - ρ z * T) := by
  let L : ReducedCrossedProduct α →+
      AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) :=
    { toFun := fun z => T * ρ z - ρ z * T
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [map_add, mul_add, add_mul]
        noncomm_ring }
  exact continuous_additive_compact_of_generators β α L
    ((continuous_const.mul (map_continuous ρ)).sub
      ((map_continuous ρ).mul continuous_const)) hgen z

end Closure
end BC4lean.KKTheory.KasparovDescent
