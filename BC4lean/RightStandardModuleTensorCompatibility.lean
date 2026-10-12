import BC4lean.RightStandardModuleTensor
import BC4lean.GradedStandardIdentityCycle
import BC4lean.GradedKasparovCompactSecondProduct
import BC4lean.KasparovProductOperatorUniqueness
import BC4lean.HeterogeneousFullGradedKasparovHomotopy

/-! # Genuine graded right tensor unit and product unit witness

The actual evaluation x tensor b maps to xb and intertwines grading,
action, representation, and the first operator on the entire completed
tensor. The compact second identity cycle has an actual product operator.
Genuine product uniqueness then gives one full interval witness from any
product by the identity to the original cycle.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory

section StandardIntertwining
variable {Γ B E : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {δ : CStarGrading B} {β : CStarAlgebraAction Γ B}

theorem standardLeftMul_representationGraded (δ : CStarGrading B) :
    ModuleTensorRepresentationGraded (δB := δ) (standardLeftMul (B := B))
      (GradedHilbertModule.standard δ) := by
  intro b x
  change MulOpposite.op (δ.automorphism (b * MulOpposite.unop x)) =
    MulOpposite.op (δ.automorphism b * δ.automorphism (MulOpposite.unop x))
  rw [map_mul]

theorem standardLeftMul_representationEquivariant (β : CStarAlgebraAction Γ B) :
    ModuleTensorRepresentationEquivariant (standardLeftMul (B := B)) β
      (EquivariantHilbertModule.standard β) := by
  intro g b x
  change MulOpposite.op (β.automorphism g (b * MulOpposite.unop x)) =
    MulOpposite.op (β.automorphism g b * β.automorphism g (MulOpposite.unop x))
  rw [map_mul]

/-- The genuine coefficient-semilinear grading commutes with right
evaluation on the completed tensor, proved from the pure tensor formula. -/
theorem rightStandardInteriorModuleTensorHilbertEquiv_grading
    (J : GradedHilbertModule δ E)
    (u : InteriorModuleTensor (E := E) (standardLeftMul (B := B))) :
    rightStandardInteriorModuleTensorHilbertEquiv
      ((J.interiorTensor (GradedHilbertModule.standard δ)
        (standardLeftMul_representationGraded δ)).grading u) =
      J.grading (rightStandardInteriorModuleTensorHilbertEquiv u) := by
  have h : rightStandardInteriorModuleTensorEvaluationCLM.comp
      (J.interiorTensor (GradedHilbertModule.standard δ)
        (standardLeftMul_representationGraded δ)).grading.toContinuousLinearEquiv.toContinuousLinearMap =
      J.grading.toContinuousLinearEquiv.toContinuousLinearMap.comp
        rightStandardInteriorModuleTensorEvaluationCLM := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x b
    change rightStandardInteriorModuleTensorEvaluation
        ((J.interiorTensor (GradedHilbertModule.standard δ)
          (standardLeftMul_representationGraded δ)).grading
            (interiorModuleTensorMk standardLeftMul x b)) =
      J.grading (rightStandardInteriorModuleTensorEvaluation
        (interiorModuleTensorMk standardLeftMul x b))
    rw [GradedHilbertModule.interiorTensor_grading_mk,
      rightStandardInteriorModuleTensorEvaluation_mk,
      rightStandardInteriorModuleTensorEvaluation_mk,
      GradedHilbertModule.standard_grading_apply]
    change opStarAlgEquiv δ.automorphism b • J.grading x = J.grading (b • x)
    exact (J.map_op_smul b x).symm
  exact DFunLike.congr_fun h u

/-- The actual action obeys the same coefficient-semilinear pure formula
and extends to all completed tensors. -/
theorem rightStandardInteriorModuleTensorHilbertEquiv_action
    (U : EquivariantHilbertModule β E) (g : Γ)
    (u : InteriorModuleTensor (E := E) (standardLeftMul (B := B))) :
    rightStandardInteriorModuleTensorHilbertEquiv
      ((U.interiorTensor (EquivariantHilbertModule.standard β)
        (standardLeftMul_representationEquivariant β)).action g u) =
      U.action g (rightStandardInteriorModuleTensorHilbertEquiv u) := by
  have h : rightStandardInteriorModuleTensorEvaluationCLM.comp
      ((U.interiorTensor (EquivariantHilbertModule.standard β)
        (standardLeftMul_representationEquivariant β)).action g).toContinuousLinearEquiv.toContinuousLinearMap =
      (U.action g).toContinuousLinearEquiv.toContinuousLinearMap.comp
        rightStandardInteriorModuleTensorEvaluationCLM := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x b
    change rightStandardInteriorModuleTensorEvaluation
        ((U.interiorTensor (EquivariantHilbertModule.standard β)
          (standardLeftMul_representationEquivariant β)).action g
            (interiorModuleTensorMk standardLeftMul x b)) =
      U.action g (rightStandardInteriorModuleTensorEvaluation
        (interiorModuleTensorMk standardLeftMul x b))
    rw [EquivariantHilbertModule.interiorTensor_action_mk,
      rightStandardInteriorModuleTensorEvaluation_mk,
      rightStandardInteriorModuleTensorEvaluation_mk,
      EquivariantHilbertModule.standard_action_apply]
    change opStarAlgEquiv (β.automorphism g) b • U.action g x = U.action g (b • x)
    exact (U.map_op_smul g b x).symm
  exact DFunLike.congr_fun h u

end StandardIntertwining

section RightProductUnit
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {E : Type uE} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

variable (c : GradedKasparovCycle α β δA δB E)

/-- The actual compact-representation product with the standard identity. -/
def gradedRightIdentityProduct :
    GradedKasparovCycle α β δA δB
      (InteriorModuleTensor (E := E) (standardLeftMul (B := B))) :=
  gradedKasparovCompactSecondProduct c
    (gradedStandardIdentityCycle β δB c.coefficientAction_preservesGrading)
    standardLeftMul_mem_moduleCompact

theorem gradedRightIdentityProduct_isProduct :
    IsGradedKasparovProductOperator c
      (gradedStandardIdentityCycle β δB c.coefficientAction_preservesGrading)
      (gradedRightIdentityProduct c).operator :=
  gradedKasparovCompactSecondProduct_isProduct c _ rfl standardLeftMul_mem_moduleCompact

/-- The same actual tensor evaluation intertwines every part of the
genuine right-identity product with the original cycle. -/
def gradedRightIdentityProductIso : GradedKasparovCycleIso (gradedRightIdentityProduct c) c where
  moduleEquiv := rightStandardInteriorModuleTensorHilbertEquiv
  grading_intertwine := rightStandardInteriorModuleTensorHilbertEquiv_grading c.grading
  action_intertwine := rightStandardInteriorModuleTensorHilbertEquiv_action c.groupAction
  representation_intertwine a x := rightStandardInteriorModuleTensorEvaluation_intertwine
    (c.representation a) x
  operator_intertwine x := rightStandardInteriorModuleTensorEvaluation_intertwine c.operator x

/-- The right unit law is a genuine single full interval witness for any
actual product by the standard graded identity cycle. -/
theorem exists_fullGradedKasparovRightUnitHomotopy
    [TopologicalSpace.SeparableSpace A] [Countable Γ]
    {R : AdjointableMap B
      (InteriorModuleTensor (E := E) (standardLeftMul (B := B)))
      (InteriorModuleTensor (E := E) (standardLeftMul (B := B)))}
    (hR : IsGradedKasparovProductOperator c
      (gradedStandardIdentityCycle β δB c.coefficientAction_preservesGrading) R) :
    Nonempty (HeterogeneousFullGradedKasparovHomotopy.{uΓ, uA, uB,
      max uE uB, uE, max uE uB}
      (BundledGradedKasparovCycle.of (gradedKasparovTensorCycleOfConditions c
        (gradedStandardIdentityCycle β δB c.coefficientAction_preservesGrading) R hR.cycleConditions))
      (BundledGradedKasparovCycle.of c)) := by
  obtain ⟨h⟩ := exists_fullGradedKasparovProductOperatorHomotopy c
    (gradedStandardIdentityCycle β δB c.coefficientAction_preservesGrading)
    hR (gradedRightIdentityProduct_isProduct c)
  exact ⟨(HeterogeneousFullGradedKasparovHomotopy.ofFull h).changeEndpoints
    (GradedKasparovCycleIso.refl _) (gradedRightIdentityProductIso c)⟩

end RightProductUnit

section FixedUniverseRightUnit

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {E : Type (max uB uE)} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

variable (c : GradedKasparovCycle α β δA δB E)

/-- The right unit law is a genuine single full interval witness for any
actual product by the standard graded identity cycle. -/
theorem exists_fullGradedKasparovRightUnitHomotopy_of_full
    [TopologicalSpace.SeparableSpace A] [Countable Γ]
    {R : AdjointableMap B
      (InteriorModuleTensor (E := E) (standardLeftMul (B := B)))
      (InteriorModuleTensor (E := E) (standardLeftMul (B := B)))}
    (hR : IsGradedKasparovProductOperator c
      (gradedStandardIdentityCycle β δB c.coefficientAction_preservesGrading) R) :
    Nonempty (FullGradedKasparovHomotopy
      (BundledGradedKasparovCycle.of (gradedKasparovTensorCycleOfConditions c
        (gradedStandardIdentityCycle β δB c.coefficientAction_preservesGrading) R hR.cycleConditions))
      (BundledGradedKasparovCycle.of c)) := by
  obtain ⟨H⟩ := exists_fullGradedKasparovRightUnitHomotopy c hR
  exact ⟨H.toFull⟩

end FixedUniverseRightUnit
end BC4lean.KKTheory
