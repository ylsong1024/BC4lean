import BC4lean.KasparovDescentGradedIntervalGrading
import BC4lean.KasparovDescentIntervalDefects

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Actual fully graded arbitrary interval cycles for reduced descent

The construction uses the genuine reduced norm bridge and induced crossed
gradings.
All source and coefficient gradings are retained on arbitrary C(X,B)-modules.
Localized original cycle defects prove the signed crossed-source defect;
no target compactness field or completed representation is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent CStarAlgebra

private theorem graded_interval_signed_generator_ring_identity {R : Type*} [Ring R]
    (t s k l v : R) (h : t * v = v * s) :
    t * (v * k) - (v * l) * t = v * ((s - t) * k + (t * k - l * t)) := by
  calc
    _ = (t * v) * k - v * (l * t) := by noncomm_ring
    _ = (v * s) * k - v * (l * t) :=
      congrArg (fun r : R => r * k - v * (l * t)) h
    _ = _ := by noncomm_ring

variable {Γ A B X : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]

variable (β : CStarAlgebraAction Γ B) (M : Type*)
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, B)ᵐᵒᵖ M]
  [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]
  (α : CStarAlgebraAction Γ A) {δA : CStarGrading A} {δB : CStarGrading B}

private theorem graded_interval_single_group_first_aux
    (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap C(X, B) M M)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))
    (a : A) (g : Γ) :
    intervalReducedSourceRepresentation (X := X) β M α U π hπ
        (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a)) =
      (intervalGroupAction (X := X) β M U).trivialActionOperator g *
        intervalOperatorHom (X := X) β M (π (α.automorphism g⁻¹ a)) := by
  have hsingle :
      intervalReducedSourceRepresentation (X := X) β M α U π hπ
          (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a)) =
        intervalSourceRepresentation (X := X) β M π a *
          intervalGroupOperator (X := X) β M U g :=
    intervalReducedSourceRepresentation_single
      (Γ := Γ) (A := A) (B := B) (X := X) β M α U π hπ g a
  have hgroup : intervalGroupOperator (X := X) β M U g =
      (intervalGroupAction (X := X) β M U).trivialActionOperator g := rfl
  have hfirst :
      intervalSourceRepresentation (X := X) β M π a *
          (intervalGroupAction (X := X) β M U).trivialActionOperator g =
        (intervalGroupAction (X := X) β M U).trivialActionOperator g *
          intervalSourceRepresentation (X := X) β M π (α.automorphism g⁻¹ a) :=
    (congrArg
      (fun d : A => intervalSourceRepresentation (X := X) β M π d *
        (intervalGroupAction (X := X) β M U).trivialActionOperator g)
      (α.apply_inv_apply g a)).symm.trans
      (covariantGenerator_covariance
        (Γ := Γ) (A := A) (C := C(X, ReducedCrossedProduct β))
        (H := IntervalModule (X := X) β M)
        (intervalGroupAction (X := X) β M U)
        (intervalSourceRepresentation (X := X) β M π) α
        (intervalSourceRepresentation_equivariant (X := X) β M α U π hπ)
        g (α.automorphism g⁻¹ a))
  have hlast :
      (intervalGroupAction (X := X) β M U).trivialActionOperator g *
          intervalSourceRepresentation (X := X) β M π (α.automorphism g⁻¹ a) =
        (intervalGroupAction (X := X) β M U).trivialActionOperator g *
          intervalOperatorHom (X := X) β M (π (α.automorphism g⁻¹ a)) := rfl
  exact hsingle.trans
    ((congrArg
      (fun Q : AdjointableMap C(X, ReducedCrossedProduct β)
        (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) =>
        intervalSourceRepresentation (X := X) β M π a * Q) hgroup).trans
      (hfirst.trans hlast))

omit [T2Space X] in
private theorem graded_interval_operator_mul_group_aux
    (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
    (g : Γ) (T : AdjointableMap C(X, B) M M) :
    intervalOperatorHom (X := X) β M T *
        (intervalGroupAction (X := X) β M U).trivialActionOperator g =
      (intervalGroupAction (X := X) β M U).trivialActionOperator g *
        intervalOperatorHom (X := X) β M (U.conjugateOperator g⁻¹ T) := by
  exact ((intervalGroupAction (X := X) β M U).trivialActionOperator_intertwine g
    (intervalOperatorHom (X := X) β M T)).trans
      (congrArg
        (fun Q : AdjointableMap C(X, ReducedCrossedProduct β)
          (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) =>
          (intervalGroupAction (X := X) β M U).trivialActionOperator g * Q)
        (intervalGroupAction_conjugateOperator (X := X) β M U g⁻¹ T))

theorem graded_interval_generator_commutator_compact
    (c : GradedKasparovCycle α (β.continuousSections (X := X))
      δA δB.continuousSections M) (a : A) (g : Γ) :
    IsModuleCompact (intervalOperatorHom β M c.operator *
        intervalReducedSourceRepresentation β M α c.groupAction c.representation c.representation_equivariant
          (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a)) -
      intervalReducedSourceRepresentation β M α c.groupAction c.representation c.representation_equivariant
          (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g (δA.automorphism a))) *
        intervalOperatorHom β M c.operator) := by
  let b : A := α.automorphism g⁻¹ a
  let V : AdjointableMap C(X, ReducedCrossedProduct β)
      (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) :=
    (intervalGroupAction (X := X) β M c.groupAction).trivialActionOperator g
  let H : AdjointableMap C(X, B) M M →⋆ₐ[ℂ]
      AdjointableMap C(X, ReducedCrossedProduct β)
        (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) :=
    intervalOperatorHom (X := X) β M
  let ρ : ReducedCrossedProduct α →⋆ₙₐ[ℂ]
      AdjointableMap C(X, ReducedCrossedProduct β)
        (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) :=
    intervalReducedSourceRepresentation (X := X) β M α c.groupAction c.representation
      c.representation_equivariant
  have hδ : α.automorphism g⁻¹ (δA.automorphism a) = δA.automorphism b :=
    c.sourceAction_preservesGrading g⁻¹ a
  have hsA : ρ (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a)) =
      V * H (c.representation b) :=
    graded_interval_single_group_first_aux (X := X) β M α c.groupAction c.representation
      c.representation_equivariant a g
  have hsδ : ρ (algebraicToReducedCrossed α
      (AlgebraicCrossedProduct.single α g (δA.automorphism a))) =
      V * H (c.representation (δA.automorphism b)) :=
    (graded_interval_single_group_first_aux (X := X) β M α c.groupAction c.representation
      c.representation_equivariant (δA.automorphism a) g).trans
      (congrArg (fun d : A => V * H (c.representation d)) hδ)
  have hsingle :
      H c.operator * ρ (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a)) -
          ρ (algebraicToReducedCrossed α
            (AlgebraicCrossedProduct.single α g (δA.automorphism a))) * H c.operator =
        H c.operator * (V * H (c.representation b)) -
          (V * H (c.representation (δA.automorphism b))) * H c.operator :=
    congrArg₂
      (fun P Q : AdjointableMap C(X, ReducedCrossedProduct β)
        (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) =>
        H c.operator * P - Q * H c.operator) hsA hsδ
  have hV : H c.operator * V =
      V * H (c.groupAction.conjugateOperator g⁻¹ c.operator) :=
    graded_interval_operator_mul_group_aux (X := X) β M c.groupAction g c.operator
  have hid : H c.operator * (V * H (c.representation b)) -
      (V * H (c.representation (δA.automorphism b))) * H c.operator =
      V * H ((c.groupAction.conjugateOperator g⁻¹ c.operator - c.operator) * c.representation b +
        (c.operator * c.representation b - c.representation (δA.automorphism b) * c.operator)) := by
    simp only [map_add, map_sub, map_mul]
    exact graded_interval_signed_generator_ring_identity (H c.operator)
      (H (c.groupAction.conjugateOperator g⁻¹ c.operator))
      (H (c.representation b)) (H (c.representation (δA.automorphism b))) V hV
  have hk : IsModuleCompact
      (V * H ((c.groupAction.conjugateOperator g⁻¹ c.operator - c.operator) * c.representation b +
        (c.operator * c.representation b - c.representation (δA.automorphism b) * c.operator))) :=
    mul_mem_moduleCompact_left V (intervalOperatorHom_compact (X := X) β M
      ((c.equivariance_mod_compact g⁻¹ b).add (c.commutator_compact b)))
  exact Eq.mpr
    (congrArg
      (fun Q : AdjointableMap C(X, ReducedCrossedProduct β)
        (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) =>
        IsModuleCompact Q) (hsingle.trans hid)) hk

theorem graded_interval_reduced_commutator_compact
    (c : GradedKasparovCycle α (β.continuousSections (X := X))
      δA δB.continuousSections M) (z : ReducedCrossedProduct α) :
    IsModuleCompact (intervalOperatorHom β M c.operator *
        intervalReducedSourceRepresentation β M α c.groupAction c.representation c.representation_equivariant z -
      intervalReducedSourceRepresentation β M α c.groupAction c.representation c.representation_equivariant
        ((reducedCrossedProductGrading α δA c.sourceAction_preservesGrading).automorphism z) *
          intervalOperatorHom β M c.operator) := by
  let ρ := intervalReducedSourceRepresentation β M α c.groupAction c.representation c.representation_equivariant
  let σ := (reducedCrossedProductGrading α δA c.sourceAction_preservesGrading).automorphism
  let T := intervalOperatorHom β M c.operator
  let L : ReducedCrossedProduct α →+
      AdjointableMap C(X, ReducedCrossedProduct β) (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) :=
    { toFun z := T * ρ z - ρ (σ z) * T
      map_zero' := by simp
      map_add' := by intro z w; simp only [map_add, mul_add, add_mul]; noncomm_ring }
  apply ReducedCrossedDefects.continuous_additive_compact_of_generators α L
    ((continuous_const.mul (map_continuous ρ)).sub
      (((map_continuous ρ).comp (NonUnitalStarAlgHom.isometry σ σ.injective).continuous).mul
        continuous_const)) _ z
  intro g a
  change IsModuleCompact (T * ρ (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a)) -
    ρ (σ (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a))) * T)
  simpa only [ρ, σ, T, crossedGrading_single] using
    graded_interval_generator_commutator_compact β M α c a g

omit [T2Space X] in
private theorem intervalGradedCycle_trivialDefect_compact (g : Unit)
    (T S : AdjointableMap C(X, ReducedCrossedProduct β)
      (IntervalModule (X := X) β M) (IntervalModule (X := X) β M)) :
    IsModuleCompact (((intervalTargetAction (X := X) β M).conjugateOperator g T - T) * S) := by
  have hz : ((intervalTargetAction (X := X) β M).conjugateOperator g T - T) * S = 0 :=
    (congrArg
      (fun Q : AdjointableMap C(X, ReducedCrossedProduct β)
        (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) => (Q - T) * S)
      (intervalTargetAction_conjugate (X := X) β M g T)).trans
        ((congrArg
          (fun Q : AdjointableMap C(X, ReducedCrossedProduct β)
            (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) => Q * S)
          (sub_self T)).trans (zero_mul S))
  exact Eq.mpr
    (congrArg
      (fun Q : AdjointableMap C(X, ReducedCrossedProduct β)
        (IntervalModule (X := X) β M) (IntervalModule (X := X) β M) => IsModuleCompact Q) hz)
    (IsModuleCompact.zero (B := C(X, ReducedCrossedProduct β))
      (E := IntervalModule (X := X) β M) (F := IntervalModule (X := X) β M))

variable [Countable Γ] [TopologicalSpace.SeparableSpace B]

/-- The actual fully graded interval cycle over continuous crossed coefficients. -/
def intervalGradedCycle (hβ : β.PreservesGrading δB)
    (c : GradedKasparovCycle α (β.continuousSections (X := X))
      δA δB.continuousSections M) :
    GradedKasparovCycle
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α))
      ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β)).continuousSections
        (X := X))
      (reducedCrossedProductGrading α δA c.sourceAction_preservesGrading)
      (reducedCrossedProductGrading β δB hβ).continuousSections (IntervalModule (X := X) β M) where
  sourceAction_preservesGrading := fun _ _ => rfl
  coefficientAction_preservesGrading := by intro g b; ext t; rfl
  countablyGenerated := interval_countablyGenerated β M c.countablyGenerated
  grading := gradedIntervalModuleGrading β M δB hβ c.grading
  groupAction := intervalTargetAction β M
  grading_preserved := fun _ _ => rfl
  representation := intervalReducedSourceRepresentation β M α c.groupAction c.representation
    c.representation_equivariant
  representation_graded := intervalReducedSourceRepresentation_graded β M α δA δB
    c.sourceAction_preservesGrading hβ c.groupAction c.representation c.representation_equivariant
    c.grading c.grading_preserved c.representation_graded
  representation_equivariant := by intro g z; exact intervalTargetAction_conjugate β M g _
  operator := intervalOperatorHom β M c.operator
  operator_odd := intervalOperatorHom_graded_odd β M δB hβ c.grading c.operator_odd
  selfadjoint_mod_compact z :=
    ReducedCrossedDefects.integrated_selfadjoint_compact_of_generators α _ _
      (fun g a => interval_generator_selfadjoint_compact β M α c.groupAction c.representation
        c.representation_equivariant c.operator c.selfadjoint_mod_compact a g) z
  square_mod_compact z :=
    ReducedCrossedDefects.integrated_square_compact_of_generators α _ _
      (fun g a => interval_generator_square_compact β M α c.groupAction c.representation
        c.representation_equivariant c.operator c.square_mod_compact a g) z
  commutator_compact := graded_interval_reduced_commutator_compact β M α c
  equivariance_mod_compact g z :=
    intervalGradedCycle_trivialDefect_compact (X := X) β M g
      (intervalOperatorHom (X := X) β M c.operator)
      (intervalReducedSourceRepresentation (X := X) β M α c.groupAction c.representation
        c.representation_equivariant z)

end BC4lean.KKTheory.KasparovDescent
