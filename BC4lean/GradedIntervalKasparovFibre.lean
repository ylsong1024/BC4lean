import BC4lean.GradedKasparovCycleIso
import BC4lean.IntervalKasparovFibre

/-! # Genuine graded cycles on arbitrary interval-module fibres

The coefficient grading acts pointwise on continuous coefficients. The module
grading preserves the evaluated form norm, so it descends through the actual
null quotient and completion. This works for nontrivial coefficient gradings;
the module grading is never treated as a coefficient-linear adjointable map.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace

variable {Γ A B X M : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

/-- Pointwise extension of an actual coefficient grading. -/
def CStarGrading.continuousSections (δ : CStarGrading B) : CStarGrading C(X, B) where
  automorphism := continuousCoefficientEquiv δ.automorphism
  involutive b := by ext t; exact δ.involutive (b t)

@[simp] theorem CStarGrading.continuousSections_apply (δ : CStarGrading B)
    (b : C(X, B)) (t : X) :
    (δ.continuousSections (X := X)).automorphism b t = δ.automorphism (b t) := rfl

theorem CStarAlgebraAction.preservesGrading_continuousSections
    {β : CStarAlgebraAction Γ B} {δ : CStarGrading B} (h : β.PreservesGrading δ) :
    (β.continuousSections (X := X)).PreservesGrading (δ.continuousSections (X := X)) := by
  intro g b
  ext t
  exact h g (b t)

/-- Evaluation at an actual parameter recovers the coefficient grading law. -/
theorem CStarAlgebraAction.preservesGrading_of_continuousSections
    {β : CStarAlgebraAction Γ B} {δ : CStarGrading B}
    (h : (β.continuousSections (X := X)).PreservesGrading
      (δ.continuousSections (X := X))) (t : X) :
    β.PreservesGrading δ := by
  intro g b
  exact congrArg (fun f : C(X, B) => f t) (h g (ContinuousMap.const X b))

namespace GradedHilbertModule

variable {δ : CStarGrading B}

omit [CompleteSpace M] in
/-- The evaluated length is invariant under the genuine semilinear grading. -/
theorem evaluated_formNorm_grading
    (γ : GradedHilbertModule (δ.continuousSections (X := X)) M)
    (t : X) (x : EvaluatedModuleSpace B M t) :
    PositiveModuleForm.formNorm (B := B) (E := EvaluatedModuleSpace B M t)
        (evaluatedModuleOfOriginal B t (γ.grading (evaluatedModuleToOriginal t x))) =
      PositiveModuleForm.formNorm (B := B) (E := EvaluatedModuleSpace B M t) x := by
  have hinner :
      ⟪evaluatedModuleOfOriginal B t (γ.grading (evaluatedModuleToOriginal t x)),
        evaluatedModuleOfOriginal B t (γ.grading (evaluatedModuleToOriginal t x))⟫_(Bᵐᵒᵖ) =
      opStarAlgEquiv δ.automorphism ⟪x, x⟫_(Bᵐᵒᵖ) := by
    simpa only [evaluatedModule_inner, evaluatedModule_to_of, opStarAlgEquiv_apply,
      CStarGrading.continuousSections_apply, MulOpposite.unop_op] using
      congrArg (fun b : C(X, B)ᵐᵒᵖ => MulOpposite.op (MulOpposite.unop b t))
        (γ.inner_grading (evaluatedModuleToOriginal t x) (evaluatedModuleToOriginal t x))
  simp only [PositiveModuleForm.formNorm, hinner, StarAlgEquiv.norm_map]

/-- The actual grading descends to the evaluated null quotient and completion. -/
def gradedFibre (γ : GradedHilbertModule (δ.continuousSections (X := X)) M) (t : X) :
    GradedHilbertModule δ (HilbertModuleFibre B M t) where
  grading := hilbertModuleFibreLinearIsometryEquiv (B := B) (M := M) t γ.grading.toLinearEquiv
    (γ.evaluated_formNorm_grading t)
  involutive z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := M) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) continuous_id
    · intro x
      simp only [hilbertModuleFibreLinearIsometryEquiv_mk,
        LinearIsometryEquiv.coe_toLinearEquiv, γ.grading_sq]
  inner_grading x y := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := M) t).induction_on₂
      (isClosed_eq (by fun_prop)
        ((StarAlgEquiv.isometry (opStarAlgEquiv δ.automorphism)).continuous.comp
          CStarModule.continuous_inner)) (fun ξ η => ?_) x y
    change ⟪hilbertModuleFibreLinearIsometryEquiv (B := B) t γ.grading.toLinearEquiv
        (γ.evaluated_formNorm_grading t) (hilbertModuleFibreMk (B := B) t ξ),
      hilbertModuleFibreLinearIsometryEquiv (B := B) t γ.grading.toLinearEquiv
        (γ.evaluated_formNorm_grading t) (hilbertModuleFibreMk (B := B) t η)⟫_(Bᵐᵒᵖ) = _
    simp only [hilbertModuleFibreLinearIsometryEquiv_mk, hilbertModuleFibre_inner_mk]
    simpa only [opStarAlgEquiv_apply, CStarGrading.continuousSections_apply,
      MulOpposite.unop_op, LinearIsometryEquiv.coe_toLinearEquiv] using
      congrArg (fun b : C(X, B)ᵐᵒᵖ => MulOpposite.op (MulOpposite.unop b t))
        (γ.inner_grading ξ η)

omit [CompleteSpace M] in
@[simp] theorem gradedFibre_grading_mk
    (γ : GradedHilbertModule (δ.continuousSections (X := X)) M) (t : X) (x : M) :
    (γ.gradedFibre t).grading (hilbertModuleFibreMk (B := B) t x) =
      hilbertModuleFibreMk (B := B) t (γ.grading x) :=
  hilbertModuleFibreLinearIsometryEquiv_mk (B := B) t γ.grading.toLinearEquiv
    (γ.evaluated_formNorm_grading t) x

/-- Exact grading intertwinings descend, including source-algebra grading. -/
theorem graded_intertwine_fibre
    (γ : GradedHilbertModule (δ.continuousSections (X := X)) M) (t : X)
    (S T : AdjointableMap C(X, B) M M)
    (h : ∀ x, γ.grading (S x) = T (γ.grading x)) :
    ∀ z, (γ.gradedFibre t).grading (hilbertModuleFibreOperator t S z) =
      hilbertModuleFibreOperator t T ((γ.gradedFibre t).grading z) := by
  intro z
  refine (hilbertModuleFibreMk_denseRange (B := B) (M := M) t).induction_on z ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro x
    simp only [hilbertModuleFibreOperator_mk, gradedFibre_grading_mk]
    exact congrArg (hilbertModuleFibreMk (B := B) t) (h x)

/-- Actual oddness descends, with its required minus sign. -/
theorem isOdd_gradedFibre
    (γ : GradedHilbertModule (δ.continuousSections (X := X)) M) (t : X)
    {T : AdjointableMap C(X, B) M M} (hT : γ.IsOdd γ T) :
    (γ.gradedFibre t).IsOdd (γ.gradedFibre t) (hilbertModuleFibreOperator t T) := by
  intro z
  refine (hilbertModuleFibreMk_denseRange (B := B) (M := M) t).induction_on z ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro x
    simp only [hilbertModuleFibreOperator_mk, gradedFibre_grading_mk]
    simpa only [map_neg] using congrArg (hilbertModuleFibreMk (B := B) t) (hT x)

end GradedHilbertModule

omit [CompleteSpace M] in
theorem EquivariantHilbertModule.preservesGrading_gradedFibre
    {β : CStarAlgebraAction Γ B} {δ : CStarGrading B}
    (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
    (γ : GradedHilbertModule (δ.continuousSections (X := X)) M)
    (h : U.PreservesGrading γ) (t : X) :
    (U.fibre t).PreservesGrading (γ.gradedFibre t) := by
  intro g z
  refine (hilbertModuleFibreMk_denseRange (B := B) (M := M) t).induction_on z ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro x
    simp only [EquivariantHilbertModule.fibre_action_mk,
      GradedHilbertModule.gradedFibre_grading_mk]
    exact congrArg (hilbertModuleFibreMk (B := B) t) (h g x)

namespace GradedKasparovCycle

variable {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

/-- An arbitrary genuine graded interval cycle has a genuine graded cycle
on each of its actual evaluated-inner-product fibres. -/
def fibre
    (c : GradedKasparovCycle α (β.continuousSections (X := X))
      δA (δB.continuousSections (X := X)) M) (t : X) :
    GradedKasparovCycle α β δA δB (HilbertModuleFibre B M t) where
  sourceAction_preservesGrading := c.sourceAction_preservesGrading
  coefficientAction_preservesGrading :=
    CStarAlgebraAction.preservesGrading_of_continuousSections c.coefficientAction_preservesGrading t
  countablyGenerated := c.countablyGenerated.fibre t
  grading := c.grading.gradedFibre t
  groupAction := c.groupAction.fibre t
  grading_preserved := c.groupAction.preservesGrading_gradedFibre c.grading c.grading_preserved t
  representation := (hilbertModuleFibreOperatorHom t).toNonUnitalStarAlgHom.comp c.representation
  representation_graded a := c.grading.graded_intertwine_fibre t _ _ (c.representation_graded a)
  representation_equivariant g a := by
    change (c.groupAction.fibre t).conjugateOperator g
      (hilbertModuleFibreOperator t (c.representation a)) =
        hilbertModuleFibreOperator t (c.representation (α.automorphism g a))
    rw [c.groupAction.fibre_conjugateOperator]
    exact congrArg (hilbertModuleFibreOperator (B := B) t) (c.representation_equivariant g a)
  operator := hilbertModuleFibreOperator t c.operator
  operator_odd := c.grading.isOdd_gradedFibre t c.operator_odd
  selfadjoint_mod_compact a := by
    change IsModuleCompact ((hilbertModuleFibreOperator t c.operator -
      star (hilbertModuleFibreOperator t c.operator)) *
        hilbertModuleFibreOperator t (c.representation a))
    have h := (c.selfadjoint_mod_compact a).fibre t
    simpa only [hilbertModuleFibreOperator_mul, hilbertModuleFibreOperator_sub,
      hilbertModuleFibreOperator_star] using h
  square_mod_compact a := by
    change IsModuleCompact ((hilbertModuleFibreOperator t c.operator *
      hilbertModuleFibreOperator t c.operator - 1) *
        hilbertModuleFibreOperator t (c.representation a))
    have h := (c.square_mod_compact a).fibre t
    simpa only [hilbertModuleFibreOperator_mul, hilbertModuleFibreOperator_sub,
      hilbertModuleFibreOperator_one] using h
  commutator_compact a := by
    change IsModuleCompact (hilbertModuleFibreOperator t c.operator *
      hilbertModuleFibreOperator t (c.representation a) -
        hilbertModuleFibreOperator t (c.representation (δA.automorphism a)) *
          hilbertModuleFibreOperator t c.operator)
    have h := (c.commutator_compact a).fibre t
    simpa only [hilbertModuleFibreOperator_mul, hilbertModuleFibreOperator_sub] using h
  equivariance_mod_compact g a := by
    change IsModuleCompact (((c.groupAction.fibre t).conjugateOperator g
      (hilbertModuleFibreOperator t c.operator) - hilbertModuleFibreOperator t c.operator) *
        hilbertModuleFibreOperator t (c.representation a))
    have h := (c.equivariance_mod_compact g a).fibre t
    simpa only [hilbertModuleFibreOperator_mul, hilbertModuleFibreOperator_sub,
      c.groupAction.fibre_conjugateOperator] using h

@[simp] theorem fibre_operator_mk
    (c : GradedKasparovCycle α (β.continuousSections (X := X))
      δA (δB.continuousSections (X := X)) M) (t : X) (x : M) :
    (c.fibre t).operator (hilbertModuleFibreMk (B := B) t x) =
      hilbertModuleFibreMk (B := B) t (c.operator x) :=
  hilbertModuleFibreOperator_mk t c.operator x

@[simp] theorem fibre_representation_mk
    (c : GradedKasparovCycle α (β.continuousSections (X := X))
      δA (δB.continuousSections (X := X)) M) (t : X) (a : A) (x : M) :
    (c.fibre t).representation a (hilbertModuleFibreMk (B := B) t x) =
      hilbertModuleFibreMk (B := B) t (c.representation a x) :=
  hilbertModuleFibreOperator_mk t (c.representation a) x

@[simp] theorem fibre_grading_mk
    (c : GradedKasparovCycle α (β.continuousSections (X := X))
      δA (δB.continuousSections (X := X)) M) (t : X) (x : M) :
    (c.fibre t).grading.grading (hilbertModuleFibreMk (B := B) t x) =
      hilbertModuleFibreMk (B := B) t (c.grading.grading x) :=
  c.grading.gradedFibre_grading_mk t x

@[simp] theorem fibre_action_mk
    (c : GradedKasparovCycle α (β.continuousSections (X := X))
      δA (δB.continuousSections (X := X)) M) (t : X) (g : Γ) (x : M) :
    (c.fibre t).groupAction.action g (hilbertModuleFibreMk (B := B) t x) =
      hilbertModuleFibreMk (B := B) t (c.groupAction.action g x) :=
  c.groupAction.fibre_action_mk t g x

end GradedKasparovCycle
end BC4lean.KKTheory
