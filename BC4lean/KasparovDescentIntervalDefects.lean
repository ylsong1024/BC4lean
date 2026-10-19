import BC4lean.KasparovDescentIntervalRepresentation
import BC4lean.ReducedCrossedCompactDefects
import Mathlib.Tactic.NoncommRing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Compact defects on the actual arbitrary interval extension

The construction uses the concrete ordinary reduced representation.
 The only compactness inputs here are the original
localized source operator conditions. They imply compactness for the actual
constructed interval representation, rather than assuming descended fields.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent

variable {Γ A B X : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]

variable (β : CStarAlgebraAction Γ B) (M : Type*)
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, B)ᵐᵒᵖ M]
  [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

theorem intervalCoefficientRepresentation_compact (b : C(X, B)) :
    IsModuleCompact (intervalCoefficientRepresentation β b) :=
  GradedMatrixMoritaSectionRepresentation.leftAction_compact
    (coefficientRepresentation β) (coefficientRepresentation_compact β) b

theorem intervalOperatorHom_compact {T : AdjointableMap C(X, B) M M}
    (hT : IsModuleCompact T) : IsModuleCompact (intervalOperatorHom β M T) :=
  hT.interiorModuleTensorOperator (intervalCoefficientRepresentation β)
    (intervalCoefficientRepresentation_compact β)

private theorem interval_generator_commutator_ring_identity {R : Type*} [Ring R]
    (t s k v : R) (h : t * v = v * s) :
    t * (v * k) - (v * k) * t = v * ((s - t) * k + (t * k - k * t)) := by
  calc
    _ = (t * v) * k - v * (k * t) := by noncomm_ring
    _ = (v * s) * k - v * (k * t) :=
      congrArg (fun r : R => r * k - v * (k * t)) h
    _ = _ := by noncomm_ring

variable (α : CStarAlgebraAction Γ A)
  (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
  (π : A →⋆ₙₐ[ℂ] AdjointableMap C(X, B) M M)
  (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))

theorem interval_generator_selfadjoint_compact (T : AdjointableMap C(X, B) M M)
    (hT : ∀ a, IsModuleCompact ((T - star T) * π a)) (a : A) (g : Γ) :
    IsModuleCompact ((intervalOperatorHom β M T - star (intervalOperatorHom β M T)) *
      intervalReducedSourceRepresentation β M α U π hπ
        (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a))) := by
  rw [intervalReducedSourceRepresentation_single, ← mul_assoc]
  have hc := intervalOperatorHom_compact β M (hT a)
  have hc' : IsModuleCompact
      ((intervalOperatorHom β M T - star (intervalOperatorHom β M T)) *
        intervalSourceRepresentation β M π a) := by
    simpa only [intervalSourceRepresentation, NonUnitalStarAlgHom.comp_apply, StarAlgHom.coe_toNonUnitalStarAlgHom,
      map_mul, map_sub, map_star] using hc
  exact mul_mem_moduleCompact_right hc' (intervalGroupOperator β M U g)

theorem interval_generator_square_compact (T : AdjointableMap C(X, B) M M)
    (hT : ∀ a, IsModuleCompact ((T * T - 1) * π a)) (a : A) (g : Γ) :
    IsModuleCompact ((intervalOperatorHom β M T * intervalOperatorHom β M T - 1) *
      intervalReducedSourceRepresentation β M α U π hπ
        (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a))) := by
  rw [intervalReducedSourceRepresentation_single, ← mul_assoc]
  have hc := intervalOperatorHom_compact β M (hT a)
  have hc' : IsModuleCompact
      ((intervalOperatorHom β M T * intervalOperatorHom β M T - 1) *
        intervalSourceRepresentation β M π a) := by
    simpa only [intervalSourceRepresentation, NonUnitalStarAlgHom.comp_apply, StarAlgHom.coe_toNonUnitalStarAlgHom,
      map_mul, map_sub, map_one] using hc
  exact mul_mem_moduleCompact_right hc' (intervalGroupOperator β M U g)

theorem interval_generator_commutator_compact (T : AdjointableMap C(X, B) M M)
    (hcomm : ∀ a, IsModuleCompact (T * π a - π a * T))
    (heq : ∀ g a, IsModuleCompact ((U.conjugateOperator g T - T) * π a))
    (a : A) (g : Γ) :
    IsModuleCompact (intervalOperatorHom β M T *
        intervalReducedSourceRepresentation β M α U π hπ
          (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a)) -
      intervalReducedSourceRepresentation β M α U π hπ
          (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a)) *
        intervalOperatorHom β M T) := by
  let b := α.automorphism g⁻¹ a
  let V := intervalGroupOperator β M U g
  let H := intervalOperatorHom (X := X) β M
  have hgen : intervalReducedSourceRepresentation β M α U π hπ
      (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a)) = V * H (π b) := by
    rw [intervalReducedSourceRepresentation_single]
    have h := covariantGenerator_covariance (intervalGroupAction β M U)
      (intervalSourceRepresentation β M π) α
      (intervalSourceRepresentation_equivariant β M α U π hπ) g b
    simpa only [b, V, H, intervalGroupOperator, intervalSourceRepresentation,
      NonUnitalStarAlgHom.comp_apply, StarAlgHom.coe_toNonUnitalStarAlgHom, α.apply_inv_apply] using h
  have hV : H T * V = V * H (U.conjugateOperator g⁻¹ T) := by
    exact ((intervalGroupAction (X := X) β M U).trivialActionOperator_intertwine g (H T)).trans
      (congrArg
        (fun Q : AdjointableMap C(X, ReducedCrossedProduct β)
            (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) => V * Q)
        (intervalGroupAction_conjugateOperator (X := X) β M U g⁻¹ T))
  have hid : H T * (V * H (π b)) - (V * H (π b)) * H T =
      V * H ((U.conjugateOperator g⁻¹ T - T) * π b + (T * π b - π b * T)) := by
    simp only [map_add, map_sub, map_mul]
    exact interval_generator_commutator_ring_identity (H T)
      (H (U.conjugateOperator g⁻¹ T)) (H (π b)) V hV
  rw [hgen]
  change IsModuleCompact (H T * (V * H (π b)) - (V * H (π b)) * H T)
  rw [hid]
  exact mul_mem_moduleCompact_left V (intervalOperatorHom_compact β M
    ((heq g⁻¹ b).add (hcomm b)))

/-- All three actual source defects extend from finite generators by reduced
norm continuity and the closed ideal of module compact operators. -/
theorem interval_reduced_source_defects (T : AdjointableMap C(X, B) M M)
    (hadj : ∀ a, IsModuleCompact ((T - star T) * π a))
    (hsq : ∀ a, IsModuleCompact ((T * T - 1) * π a))
    (hcomm : ∀ a, IsModuleCompact (T * π a - π a * T))
    (heq : ∀ g a, IsModuleCompact ((U.conjugateOperator g T - T) * π a))
    (z : ReducedCrossedProduct α) :
    IsModuleCompact ((intervalOperatorHom β M T - star (intervalOperatorHom β M T)) *
        intervalReducedSourceRepresentation β M α U π hπ z) ∧
    IsModuleCompact ((intervalOperatorHom β M T * intervalOperatorHom β M T - 1) *
        intervalReducedSourceRepresentation β M α U π hπ z) ∧
    IsModuleCompact (intervalOperatorHom β M T * intervalReducedSourceRepresentation β M α U π hπ z -
      intervalReducedSourceRepresentation β M α U π hπ z * intervalOperatorHom β M T) := by
  constructor
  · exact ReducedCrossedDefects.integrated_selfadjoint_compact_of_generators α _ _
      (fun g a => interval_generator_selfadjoint_compact β M α U π hπ T hadj a g) z
  constructor
  · exact ReducedCrossedDefects.integrated_square_compact_of_generators α _ _
      (fun g a => interval_generator_square_compact β M α U π hπ T hsq a g) z
  · exact ReducedCrossedDefects.integrated_commutator_compact_of_generators α _ _
      (fun g a => interval_generator_commutator_compact β M α U π hπ T hcomm heq a g) z

end BC4lean.KKTheory.KasparovDescent
