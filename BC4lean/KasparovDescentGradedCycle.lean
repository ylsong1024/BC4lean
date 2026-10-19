import BC4lean.KasparovDescentRawCycle
import BC4lean.ReducedCrossedCompactDefects
import BC4lean.GradedKasparovCycle

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Genuine fully graded raw reduced descent

This uses the concrete reduced representation and the actual induced
crossed-product gradings.
 The original source and coefficient gradings are
retained. No descended-cycle field, product law, or completed representation
is assumed as an input.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent CStarAlgebra

private theorem graded_generator_commutator_ring_identity {R : Type*} [Ring R]
    (t s k l v : R) (h : t * v = v * s) :
    t * (v * k) - (v * l) * t = v * ((s - t) * k + (t * k - l * t)) := by
  calc
    _ = (t * v) * k - v * (l * t) := by noncomm_ring
    _ = (v * s) * k - v * (l * t) :=
      congrArg (fun r : R => r * k - v * (l * t)) h
    _ = _ := by noncomm_ring

variable {Γ A B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- The actual left regular multiplier commutes with the induced coefficient grading. -/
theorem crossedGrading_leftRegular (β : CStarAlgebraAction Γ B) (δB : CStarGrading B)
    (hβ : β.PreservesGrading δB) (g : Γ) (c : ReducedCrossedProduct β) :
    (reducedCrossedProductGrading β δB hβ).automorphism (leftRegular β g c) =
      leftRegular β g ((reducedCrossedProductGrading β δB hβ).automorphism c) := by
  apply Subtype.ext
  simp only [reducedCrossedProductGrading_coe, leftRegular_coe, map_mul,
    reducedCrossedGrading_regular]

theorem leftRegularAction_preserves_crossedGrading (β : CStarAlgebraAction Γ B)
    (δB : CStarGrading B) (hβ : β.PreservesGrading δB) :
    (leftRegularAction β).PreservesGrading (crossedStandardGrading β δB hβ) := by
  intro g c
  change MulOpposite.op (leftRegular β g
      ((reducedCrossedProductGrading β δB hβ).automorphism (MulOpposite.unop c))) =
    MulOpposite.op ((reducedCrossedProductGrading β δB hβ).automorphism
      (leftRegular β g (MulOpposite.unop c)))
  exact congrArg MulOpposite.op (crossedGrading_leftRegular β δB hβ g (MulOpposite.unop c)).symm

theorem crossedGrading_single (α : CStarAlgebraAction Γ A) (δA : CStarGrading A)
    (hα : α.PreservesGrading δA) (g : Γ) (a : A) :
    (reducedCrossedProductGrading α δA hα).automorphism
        (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a)) =
      algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g (δA.automorphism a)) := by
  apply Subtype.ext
  simp only [reducedCrossedProductGrading_coe, algebraicToReducedCrossed_single]
  exact reducedCrossedGrading_generator α δA hα a g

variable (β : CStarAlgebraAction Γ B) (α : CStarAlgebraAction Γ A)
  {δA : CStarGrading A} {δB : CStarGrading B}

omit [PartialOrder A] [StarOrderedRing A] in
theorem sourceRepresentation_graded_tensor (hβ : β.PreservesGrading δB)
    (J : GradedHilbertModule δB E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (hπ : ∀ a x, J.grading (π a x) = π (δA.automorphism a) (J.grading x))
    (a : A) (u : Module β E) :
    (moduleGrading β δB hβ J).grading (sourceRepresentation β E π a u) =
      sourceRepresentation β E π (δA.automorphism a) ((moduleGrading β δB hβ J).grading u) := by
  let K : Module β E →L[ℂ] Module β E :=
    (moduleGrading β δB hβ J).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let L : Module β E →L[ℂ] Module β E := (sourceRepresentation β E π a).toCLM
  let R : Module β E →L[ℂ] Module β E :=
    (sourceRepresentation β E π (δA.automorphism a)).toCLM
  let G : (ReducedCrossedProduct β)ᵐᵒᵖ → (ReducedCrossedProduct β)ᵐᵒᵖ := fun c =>
    MulOpposite.op ((reducedCrossedProductGrading β δB hβ).automorphism (MulOpposite.unop c))
  have h : K.comp L = R.comp K := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      (B := B) (C := ReducedCrossedProduct β) (E := E)
      (F := (ReducedCrossedProduct β)ᵐᵒᵖ)
      (φ := coefficientRepresentation β) (P := Module β E)
      (f := K.comp L) (g := R.comp K)
    intro x c
    have hL (y : E) (d : (ReducedCrossedProduct β)ᵐᵒᵖ) :
        L (mk β E y d) = mk β E (π a y) d :=
      operatorHom_mk β E (π a) y d
    have hR (y : E) (d : (ReducedCrossedProduct β)ᵐᵒᵖ) :
        R (mk β E y d) = mk β E (π (δA.automorphism a) y) d :=
      operatorHom_mk β E (π (δA.automorphism a)) y d
    have hK (y : E) (d : (ReducedCrossedProduct β)ᵐᵒᵖ) :
        K (mk β E y d) = mk β E (J.grading y) (G d) :=
      moduleGrading_mk β δB hβ J y d
    change K (L (mk β E x c)) = R (K (mk β E x c))
    calc
      K (L (mk β E x c)) = K (mk β E (π a x) c) :=
        congrArg (fun v : Module β E => K v) (hL x c)
      _ = mk β E (J.grading (π a x)) (G c) := hK (π a x) c
      _ = mk β E (π (δA.automorphism a) (J.grading x)) (G c) :=
        congrArg (fun y : E => mk β E y (G c)) (hπ a x)
      _ = R (mk β E (J.grading x) (G c)) := (hR (J.grading x) (G c)).symm
      _ = R (K (mk β E x c)) :=
        congrArg (fun v : Module β E => R v) (hK x c).symm
  exact DFunLike.congr_fun h u

theorem groupOperator_graded_even (hβ : β.PreservesGrading δB)
    (J : GradedHilbertModule δB E) (U : EquivariantHilbertModule β E)
    (hU : U.PreservesGrading J) (g : Γ) :
    (moduleGrading β δB hβ J).IsEven (moduleGrading β δB hβ J) (groupOperator β E U g) := by
  have h := U.interiorTensor_preservesGrading (leftRegularAction β) J
    (crossedStandardGrading β δB hβ) hU (leftRegularAction_preserves_crossedGrading β δB hβ)
    (coefficientRepresentation_equivariant β) (coefficientRepresentation_graded β δB hβ)
  intro u
  exact (h g u).symm

omit [PartialOrder A] [StarOrderedRing A] in
theorem sourceGenerator_graded (hβ : β.PreservesGrading δB)
    (J : GradedHilbertModule δB E) (U : EquivariantHilbertModule β E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E) (hU : U.PreservesGrading J)
    (hπ : ∀ a x, J.grading (π a x) = π (δA.automorphism a) (J.grading x))
    (a : A) (g : Γ) (u : Module β E) :
    (moduleGrading β δB hβ J).grading (sourceGenerator β E U π a g u) =
      sourceGenerator β E U π (δA.automorphism a) g ((moduleGrading β δB hβ J).grading u) := by
  change (moduleGrading β δB hβ J).grading
    (sourceRepresentation β E π a (groupOperator β E U g u)) = _
  rw [sourceRepresentation_graded_tensor β hβ J π hπ,
    groupOperator_graded_even β hβ J U hU g u]
  rfl

theorem reducedSourceRepresentation_graded
    (c : GradedKasparovCycle α β δA δB E) (z : ReducedCrossedProduct α) (u : Module β E) :
    (moduleGrading β δB c.coefficientAction_preservesGrading c.grading).grading
        (reducedSourceRepresentation β E α c.groupAction c.representation c.representation_equivariant z u) =
      reducedSourceRepresentation β E α c.groupAction c.representation c.representation_equivariant
        ((reducedCrossedProductGrading α δA c.sourceAction_preservesGrading).automorphism z)
        ((moduleGrading β δB c.coefficientAction_preservesGrading c.grading).grading u) := by
  let ρ := reducedSourceRepresentation β E α c.groupAction c.representation c.representation_equivariant
  let J := moduleGrading β δB c.coefficientAction_preservesGrading c.grading
  let σ := (reducedCrossedProductGrading α δA c.sourceAction_preservesGrading).automorphism
  have heval (v : Module β E) : Continuous (fun w : ReducedCrossedProduct α => ρ w v) :=
    (AdjointableMap.toCLM_isometry.continuous.comp (map_continuous ρ)).clm_apply continuous_const
  refine (algebraicToReducedCrossed_denseRange α).induction_on z
    (isClosed_eq (J.grading.continuous.comp (heval u))
      ((heval (J.grading u)).comp (NonUnitalStarAlgHom.isometry σ σ.injective).continuous)) ?_
  intro f
  induction f using AlgebraicCrossedProduct.induction_on α with
  | zero => simp only [map_zero, AdjointableMap.coe_zero_apply]
  | single g a =>
    change J.grading (ρ (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a)) u) = _
    simp only [ρ, reducedSourceRepresentation_single, crossedGrading_single]
    exact sourceGenerator_graded β c.coefficientAction_preservesGrading c.grading
      c.groupAction c.representation c.grading_preserved c.representation_graded a g u
  | add f h ihf ihh =>
    simpa only [map_add, AdjointableMap.coe_add_apply] using congrArg₂ (· + ·) ihf ihh

omit [PartialOrder A] [StarOrderedRing A] in
/-- The signed generator commutator has exactly the original right-localized
equivariance defect and graded commutator as its compact summands. -/
theorem graded_sourceGenerator_commutator_compact
    (c : GradedKasparovCycle α β δA δB E) (a : A) (g : Γ) :
    IsModuleCompact (operatorHom β E c.operator * sourceGenerator β E c.groupAction c.representation a g -
      sourceGenerator β E c.groupAction c.representation (δA.automorphism a) g *
        operatorHom β E c.operator) := by
  let b := α.automorphism g⁻¹ a
  let V := groupOperator β E c.groupAction g
  let H := operatorHom β E
  have hδ : α.automorphism g⁻¹ (δA.automorphism a) = δA.automorphism b :=
    c.sourceAction_preservesGrading g⁻¹ a
  simp only [sourceGenerator_group_first β E α c.groupAction c.representation
    c.representation_equivariant, hδ]
  change IsModuleCompact (H c.operator * (V * H (c.representation b)) -
    (V * H (c.representation (δA.automorphism b))) * H c.operator)
  have hV : H c.operator * V = V * H (c.groupAction.conjugateOperator g⁻¹ c.operator) :=
    operatorHom_mul_groupOperator β E c.groupAction g c.operator
  have hid : H c.operator * (V * H (c.representation b)) -
      (V * H (c.representation (δA.automorphism b))) * H c.operator =
      V * H ((c.groupAction.conjugateOperator g⁻¹ c.operator - c.operator) * c.representation b +
        (c.operator * c.representation b - c.representation (δA.automorphism b) * c.operator)) := by
    simp only [map_add, map_sub, map_mul]
    exact graded_generator_commutator_ring_identity (H c.operator)
      (H (c.groupAction.conjugateOperator g⁻¹ c.operator))
      (H (c.representation b)) (H (c.representation (δA.automorphism b))) V hV
  have hk : IsModuleCompact
      (V * H ((c.groupAction.conjugateOperator g⁻¹ c.operator - c.operator) * c.representation b +
        (c.operator * c.representation b - c.representation (δA.automorphism b) * c.operator))) :=
    mul_mem_moduleCompact_left V (operatorHom_compact β E
      ((c.equivariance_mod_compact g⁻¹ b).add (c.commutator_compact b)))
  exact Eq.mpr
    (congrArg
      (fun T : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) =>
        IsModuleCompact T) hid) hk

theorem graded_reduced_commutator_compact
    (c : GradedKasparovCycle α β δA δB E) (z : ReducedCrossedProduct α) :
    IsModuleCompact (operatorHom β E c.operator *
        reducedSourceRepresentation β E α c.groupAction c.representation c.representation_equivariant z -
      reducedSourceRepresentation β E α c.groupAction c.representation c.representation_equivariant
        ((reducedCrossedProductGrading α δA c.sourceAction_preservesGrading).automorphism z) *
          operatorHom β E c.operator) := by
  let ρ := reducedSourceRepresentation β E α c.groupAction c.representation c.representation_equivariant
  let σ := (reducedCrossedProductGrading α δA c.sourceAction_preservesGrading).automorphism
  let T := operatorHom β E c.operator
  let L : ReducedCrossedProduct α →+ AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) :=
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
  simpa only [ρ, σ, T, crossedGrading_single, reducedSourceRepresentation_single] using
    graded_sourceGenerator_commutator_compact β α c a g

private theorem graded_reduced_selfadjoint_compact_aux
    (c : GradedKasparovCycle α β δA δB E) (z : ReducedCrossedProduct α) :
    IsModuleCompact ((operatorHom β E c.operator - star (operatorHom β E c.operator)) *
      reducedSourceRepresentation β E α c.groupAction c.representation c.representation_equivariant z) := by
  apply integrated_selfadjoint_compact_of_generators β α _ _ _ z
  intro g a
  rw [reducedSourceRepresentation_single]
  change IsModuleCompact ((operatorHom β E c.operator - star (operatorHom β E c.operator)) *
    (operatorHom β E (c.representation a) * groupOperator β E c.groupAction g))
  rw [← mul_assoc]
  exact mul_mem_moduleCompact_right
    (operatorHom_selfadjoint_defect β c.operator (c.representation a) (c.selfadjoint_mod_compact a)) _

private theorem graded_reduced_square_compact_aux
    (c : GradedKasparovCycle α β δA δB E) (z : ReducedCrossedProduct α) :
    IsModuleCompact ((operatorHom β E c.operator * operatorHom β E c.operator - 1) *
      reducedSourceRepresentation β E α c.groupAction c.representation c.representation_equivariant z) := by
  apply integrated_square_compact_of_generators β α _ _ _ z
  intro g a
  rw [reducedSourceRepresentation_single]
  change IsModuleCompact ((operatorHom β E c.operator * operatorHom β E c.operator - 1) *
    (operatorHom β E (c.representation a) * groupOperator β E c.groupAction g))
  rw [← mul_assoc]
  exact mul_mem_moduleCompact_right
    (operatorHom_square_defect β c.operator (c.representation a) (c.square_mod_compact a)) _

private theorem gradedCycle_trivialDefect_compact (g : Unit)
    (T S : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E)) :
    IsModuleCompact (((ordinaryTargetAction (E := E) β).conjugateOperator g T - T) * S) := by
  have hz : ((ordinaryTargetAction (E := E) β).conjugateOperator g T - T) * S = 0 :=
    (congrArg
      (fun Q : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) =>
        (Q - T) * S)
      (ordinaryTargetAction_conjugate (E := E) β g T)).trans
        ((congrArg
          (fun Q : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) =>
            Q * S)
          (sub_self T)).trans (zero_mul S))
  exact Eq.mpr
    (congrArg
      (fun Q : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) =>
        IsModuleCompact Q) hz)
    (IsModuleCompact.zero
      (B := ReducedCrossedProduct β) (E := Module β E) (F := Module β E))


variable [Countable Γ] [TopologicalSpace.SeparableSpace B]

/-- The actual fully graded raw cycle. Gamma is integrated into the genuine
source crossed action; the target equivariance group is Unit. -/
def gradedCycle (c : GradedKasparovCycle α β δA δB E) :
    GradedKasparovCycle
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α))
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β))
      (reducedCrossedProductGrading α δA c.sourceAction_preservesGrading)
      (reducedCrossedProductGrading β δB c.coefficientAction_preservesGrading) (Module β E) where
  sourceAction_preservesGrading := fun _ _ => rfl
  coefficientAction_preservesGrading := fun _ _ => rfl
  countablyGenerated := KasparovDescent.countablyGenerated β E c.countablyGenerated
  grading := moduleGrading β δB c.coefficientAction_preservesGrading c.grading
  groupAction := ordinaryTargetAction (E := E) β
  grading_preserved := fun _ _ => rfl
  representation := reducedSourceRepresentation β E α c.groupAction c.representation c.representation_equivariant
  representation_graded := reducedSourceRepresentation_graded β α c
  representation_equivariant := by intro g z; exact ordinaryTargetAction_conjugate (E := E) β g _
  operator := operatorHom β E c.operator
  operator_odd := operatorHom_odd β δB c.coefficientAction_preservesGrading c.grading c.operator_odd
  selfadjoint_mod_compact := graded_reduced_selfadjoint_compact_aux β α c
  square_mod_compact := graded_reduced_square_compact_aux β α c
  commutator_compact := graded_reduced_commutator_compact β α c
  equivariance_mod_compact g z :=
    gradedCycle_trivialDefect_compact (E := E) β g
      (operatorHom β E c.operator)
      (reducedSourceRepresentation β E α c.groupAction c.representation c.representation_equivariant z)

end BC4lean.KKTheory.KasparovDescent
