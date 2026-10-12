import BC4lean.ScalarKasparovSupport
import BC4lean.GradedHilbertModuleHomogeneousSplit
import BC4lean.GlobalFredholmScalarCycle

/-! # Actual rectangular Fredholm operators from scalar cycles

The original scalar cycle is first reduced to its actual support and then
symmetrized by its proved admissible affine homotopy. The actual homogeneous
range modules supply a rectangular operator. Both global Fredholm defects
derive from the original scalar cycle conditions, with no global Fredholm
assumption. In the ordinary, non-equivariant case the actual homogeneous
unitary intertwines the entire supported selfadjoint cycle with its rectangular
scalar cycle.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [scalarRectangularCompleteSpace : CompleteSpace E] {β : CStarAlgebraAction Γ B}

namespace KasparovCycle

variable (c : KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) β E)

/-- The genuine supported, symmetrized operator. -/
def scalarSupportSelfadjointOperator :=
  c.scalarSupportCycle.operator + c.scalarSupportCycle.symmetrizingPerturbation

theorem scalarSupportSelfadjointOperator_isSelfAdjoint :
    IsSelfAdjoint c.scalarSupportSelfadjointOperator :=
  c.scalarSupportCycle.symmetrizedOperator_selfadjoint

theorem scalarSupportSelfadjointOperator_isOdd :
    c.scalarSupportGrading.IsOdd c.scalarSupportGrading c.scalarSupportSelfadjointOperator :=
  c.scalarSupportCycle.operatorConditions_symmetrization.operator_odd

@[simp] theorem scalarSupportRepresentation_one : c.scalarSupportRepresentation 1 = 1 := by
  ext x
  simp only [c.scalarSupportRepresentation_apply, one_smul, AdjointableMap.one_apply]

/-- The original cycle at the scalar unit gives a globally compact square
defect for the supported selfadjoint representative. -/
theorem scalarSupportSelfadjointOperator_square_isModuleCompact :
    IsModuleCompact (c.scalarSupportSelfadjointOperator * c.scalarSupportSelfadjointOperator - 1) := by
  have hh := c.scalarSupportCycle.operatorConditions_symmetrization.square_mod_compact 1
  change IsModuleCompact ((c.scalarSupportSelfadjointOperator * c.scalarSupportSelfadjointOperator - 1) *
    c.scalarSupportRepresentation 1) at hh
  rwa [c.scalarSupportRepresentation_one, mul_one] at hh

/-- The actual supported selfadjoint cycle. -/
def scalarSupportSelfadjointCycle :=
  c.scalarSupportCycle.withOperator c.scalarSupportSelfadjointOperator
    c.scalarSupportCycle.operatorConditions_symmetrization

/-- The actual affine homotopy to the selfadjoint supported endpoint. -/
def scalarSupportSymmetrizationHomotopy :
    KasparovOperatorHomotopy c.scalarSupportCycle c.scalarSupportCycle.operator
      c.scalarSupportSelfadjointOperator := c.scalarSupportCycle.symmetrizationHomotopy

/-- The actual even-to-odd rectangular block. -/
def scalarRectangularFredholm :
    AdjointableMap B c.scalarSupportGrading.EvenModule c.scalarSupportGrading.OddModule :=
  c.scalarSupportGrading.homogeneousOddMap c.scalarSupportSelfadjointOperator

theorem scalarRectangularFredholm_source_defect :
    IsModuleCompact (1 - c.scalarRectangularFredholm.adjoint.comp c.scalarRectangularFredholm) :=
  c.scalarSupportGrading.homogeneousOddMap_source_defect_isModuleCompact
    c.scalarSupportSelfadjointOperator c.scalarSupportSelfadjointOperator_isOdd
    c.scalarSupportSelfadjointOperator_isSelfAdjoint c.scalarSupportSelfadjointOperator_square_isModuleCompact

theorem scalarRectangularFredholm_target_defect :
    IsModuleCompact (c.scalarRectangularFredholm.comp c.scalarRectangularFredholm.adjoint - 1) :=
  c.scalarSupportGrading.homogeneousOddMap_target_defect_isModuleCompact
    c.scalarSupportSelfadjointOperator c.scalarSupportSelfadjointOperator_isOdd
    c.scalarSupportSelfadjointOperator_isSelfAdjoint c.scalarSupportSelfadjointOperator_square_isModuleCompact

theorem scalarRectangularEvenModule_isCountablyGenerated :
    IsCountablyGeneratedModule B c.scalarSupportGrading.EvenModule :=
  c.scalarSupportGrading.evenModule_isCountablyGenerated c.scalarSupportModule_isCountablyGenerated

theorem scalarRectangularOddModule_isCountablyGenerated :
    IsCountablyGeneratedModule B c.scalarSupportGrading.OddModule :=
  c.scalarSupportGrading.oddModule_isCountablyGenerated c.scalarSupportModule_isCountablyGenerated

end KasparovCycle

namespace GradedHilbertModule

variable (γ : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E)
  (T : AdjointableMap B E E) (hOdd : γ.IsOdd γ T) (hSelf : IsSelfAdjoint T)

omit scalarRectangularCompleteSpace in
include hOdd hSelf in
/-- The actual homogeneous unitary turns a selfadjoint odd operator into its
rectangular off-diagonal operator, intertwining both blocks exactly. -/
theorem homogeneousSplitEquiv_operator_intertwine [CompleteSpace E] (x : E) :
    γ.homogeneousSplitEquiv (T x) =
      offDiagonalAdjointable (γ.homogeneousOddMap T) (γ.homogeneousSplitEquiv x) := by
  simp only [homogeneousSplitEquiv, offDiagonalAdjointable_apply]
  apply Prod.ext <;> apply Subtype.ext
  · change γ.evenProjection (T x) =
      ((γ.homogeneousOddMap T).adjoint (projectionCorestrict γ.oddProjection γ.oddProjection_isStarProjection x) : E)
    rw [γ.homogeneousOddMap_adjoint_coe T hOdd hSelf]
    rw [projectionCorestrict_coe, γ.evenProjection_apply, γ.oddProjection_apply]
    have hanti : γ.grading (T.toCLM x) = -T.toCLM (γ.grading x) := hOdd x
    change (2 : ℂ)⁻¹ • (T.toCLM x + γ.grading (T.toCLM x)) =
      T.toCLM ((2 : ℂ)⁻¹ • (x - γ.grading x))
    rw [T.toCLM.map_smul, T.toCLM.map_sub, hanti]
    simp only [sub_eq_add_neg]
  · change γ.oddProjection (T x) =
      (γ.homogeneousOddMap T (projectionCorestrict γ.evenProjection γ.evenProjection_isStarProjection x) : E)
    rw [γ.homogeneousOddMap_coe T hOdd]
    rw [projectionCorestrict_coe, γ.oddProjection_apply, γ.evenProjection_apply]
    have hanti : γ.grading (T.toCLM x) = -T.toCLM (γ.grading x) := hOdd x
    change (2 : ℂ)⁻¹ • (T.toCLM x - γ.grading (T.toCLM x)) =
      T.toCLM ((2 : ℂ)⁻¹ • (x + γ.grading x))
    rw [T.toCLM.map_smul, T.toCLM.map_add, hanti]
    simp only [sub_neg_eq_add]

end GradedHilbertModule

namespace KasparovCycle

variable (c : KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
  (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B) E)

/-- In ordinary KK-theory, the actual homogeneous unitary intertwines every
piece of the supported selfadjoint cycle with the constructed rectangular
scalar cycle. The Fredholm data are derived above from the original cycle. -/
def scalarRectangularFredholmCycleIso :
    KasparovCycleIso c.scalarSupportSelfadjointCycle
      (globalFredholmScalarCycle (Γ := PUnit) c.scalarRectangularFredholm
        c.scalarRectangularFredholm_source_defect c.scalarRectangularFredholm_target_defect
        c.scalarRectangularEvenModule_isCountablyGenerated c.scalarRectangularOddModule_isCountablyGenerated) where
  moduleEquiv := c.scalarSupportGrading.homogeneousSplitEquiv
  grading_intertwine := c.scalarSupportGrading.homogeneousSplitEquiv_grading_intertwine
  action_intertwine g x := by
    cases g
    change c.scalarSupportGrading.homogeneousSplitEquiv
      (c.scalarSupportGroupAction.action 1 x) = c.scalarSupportGrading.homogeneousSplitEquiv x
    rw [c.scalarSupportGroupAction.one_apply]
  representation_intertwine z x := by
    change c.scalarSupportGrading.homogeneousSplitEquiv (c.scalarSupportRepresentation z x) =
      scalarModuleRepresentation z (c.scalarSupportGrading.homogeneousSplitEquiv x)
    rw [c.scalarSupportRepresentation_apply, scalarModuleRepresentation_apply,
      HilbertModuleEquiv.map_smul]
  operator_intertwine := c.scalarSupportGrading.homogeneousSplitEquiv_operator_intertwine
    c.scalarSupportSelfadjointOperator c.scalarSupportSelfadjointOperator_isOdd
    c.scalarSupportSelfadjointOperator_isSelfAdjoint

end KasparovCycle
end BC4lean.KKTheory
