import BC4lean.ScalarKasparovK0ComparisonAddEquiv
import BC4lean.NonunitalProjectionK0
import BC4lean.GroupUniverseParityUnits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! The scalar identity and the actual nonunital unit projection.
An explicit whole-cycle isomorphism computes the scalar KK-to-K0 comparison. -/

noncomputable section
namespace BC4lean.KKTheory.ScalarUnitProjection
open BC4lean.OperatorKTheory
open scoped InnerProductSpace ComplexOrder

abbrev scalarIdentityAction : CStarAlgebraAction Unit ℂ := CStarAlgebraAction.trivial
abbrev UnitFiniteModule := FiniteStandardModule ℂ PUnit.{1}
local instance completeV : CompleteSpace UnitFiniteModule := finiteStandardModule_complete

def scalarUnitProjection : MatrixProjection (Unitization ℂ ℂ) PUnit.{1} :=
  ⟨nonunitalProjectionMatrix (1 : ℂ),
    nonunitalProjectionMatrix_isStarProjection (1 : ℂ) (by
      apply isStarProjection_iff'.mpr
      exact ⟨one_mul 1, star_one _⟩)⟩

abbrev unitProjectionOperator : AdjointableMap ℂ UnitFiniteModule UnitFiniteModule :=
  unitizedProjectionOperator scalarUnitProjection
abbrev scalarShadowOperator : AdjointableMap ℂ UnitFiniteModule UnitFiniteModule :=
  unitizedProjectionOperator (unitizationScalarShadowProjection scalarUnitProjection)

theorem unitProjectionOperator_eq_one : unitProjectionOperator = 1 := by
  ext x i
  simp only [unitizedProjectionOperator, unitizedModuleMatrixRepresentation_apply,
    scalarUnitProjection, nonunitalProjectionMatrix_apply, Fintype.sum_unique,
    unitizedStandardLeftMul_apply]
  change (0 : ℂ) • x default + MulOpposite.op ((1 : ℂ) * MulOpposite.unop (x default)) = x i
  simp only [zero_smul, one_mul, MulOpposite.op_unop, zero_add]

theorem scalarShadowOperator_eq_zero : scalarShadowOperator = 0 := by
  ext x i
  simp only [unitizedProjectionOperator, unitizedModuleMatrixRepresentation_apply,
    Fintype.sum_unique]
  change unitizedStandardLeftMul (0 : Unitization ℂ ℂ) (x default) = 0
  rw [map_zero]
  rfl

abbrev RelativeModule := HilbertModuleSum ℂ (ProjectionModule unitProjectionOperator) (ProjectionModule scalarShadowOperator)

private theorem oddComponent_eq_zero (x : RelativeModule) : x.snd = 0 := by
  apply Subtype.ext
  have h := x.snd.property
  have hz : scalarShadowOperator (x.snd : UnitFiniteModule) = 0 :=
    congrArg (fun T : AdjointableMap ℂ UnitFiniteModule UnitFiniteModule =>
      T (x.snd : UnitFiniteModule)) scalarShadowOperator_eq_zero
  exact h.symm.trans hz

private def unitRangeVector (b : ℂᵐᵒᵖ) : ProjectionModule unitProjectionOperator :=
  ⟨finiteStandardSingle default b, by
    change unitProjectionOperator (finiteStandardSingle default b) = finiteStandardSingle default b
    rw [unitProjectionOperator_eq_one]
    rfl⟩

private theorem relativeEvaluation_inner (x y : RelativeModule) :
    ⟪(x.fst : UnitFiniteModule) default, (y.fst : UnitFiniteModule) default⟫_(ℂᵐᵒᵖ) = ⟪x, y⟫_(ℂᵐᵒᵖ) := by
  rw [inner_sum, oddComponent_eq_zero x, oddComponent_eq_zero y]
  simp only [CStarModule.inner_zero_left, add_zero, projectionModule_inner,
    WithCStarModule.pi_inner, Fintype.sum_unique]

def unitRelativeModuleEquiv : HilbertModuleEquiv ℂ RelativeModule ℂᵐᵒᵖ where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun x := (x.fst : UnitFiniteModule) default
          invFun b := sumMk (unitRangeVector b) 0
          left_inv x := by
            apply Prod.ext
            · apply Subtype.ext
              apply WithCStarModule.ext
              intro i
              simp only [sumMk_fst, unitRangeVector, finiteStandardSingle_apply,
                Pi.single_apply, Subsingleton.elim i default, if_true]
            · exact (oddComponent_eq_zero x).symm
          right_inv b := by
            change finiteStandardSingle default b default = b
            simp only [finiteStandardSingle_apply, Pi.single_eq_same]
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      norm_map' x := by
        change ‖((x.fst : UnitFiniteModule) default)‖ = ‖x‖
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := ℂᵐᵒᵖ),
          relativeEvaluation_inner, ← CStarModule.norm_eq_sqrt_norm_inner_self (A := ℂᵐᵒᵖ)] }
  inner_map := relativeEvaluation_inner

def scalarIdentityCycle : KasparovCycle scalarIdentityAction scalarIdentityAction ℂᵐᵒᵖ :=
  (gradedStandardIdentityCycle scalarIdentityAction CStarGrading.trivial
    (CStarAlgebraAction.preservesGrading_trivial scalarIdentityAction)).toKasparovCycle

/-- The odd summand is literally the zero range, while the even summand is
one copy of the scalar standard module. Every item of cycle data is preserved. -/
def unitRelativeCycleIso : KasparovCycleIso
    (unitizedRelativeProjectionCycle (Γ := Unit) scalarUnitProjection
      (unitizationScalarShadowProjection scalarUnitProjection)
      (unitizationScalarShadowProjection_scalar scalarUnitProjection))
    scalarIdentityCycle where
  moduleEquiv := unitRelativeModuleEquiv
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine a x := by
    change (a • (x.fst : UnitFiniteModule)) default = MulOpposite.op (a * MulOpposite.unop ((x.fst : UnitFiniteModule) default))
    rfl
  operator_intertwine x := by
    let T : AdjointableMap ℂ (ProjectionModule unitProjectionOperator) (ProjectionModule scalarShadowOperator) :=
      projectionCrossMap unitProjectionOperator scalarShadowOperator
        (unitizedProjectionOperator_isStarProjection scalarUnitProjection)
        (unitizedProjectionOperator_isStarProjection
          (unitizationScalarShadowProjection scalarUnitProjection))
    change unitRelativeModuleEquiv (offDiagonalAdjointable T x) = 0
    rw [offDiagonalAdjointable_apply]
    change (T.adjoint x.snd : UnitFiniteModule) default = 0
    rw [oddComponent_eq_zero x]
    simp only [map_zero, Submodule.coe_zero, WithCStarModule.zero_apply]

/-- The existing relative-projection map sends the genuine singleton unit
projection to the independently constructed standard identity cycle. -/
theorem relativeMap_nonunitalUnitProjection :
    nonunitalRelativeK0KasparovMap
      (nonunitalProjectionK0 (1 : ℂ) (by
        apply isStarProjection_iff'.mpr
        exact ⟨one_mul 1, star_one _⟩)) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of scalarIdentityCycle) := by
  change unitizationK0RelativeKKMap
      (k0Projection (nonunitalFiniteProjection (1 : ℂ) _)) = _
  rw [unitizationK0RelativeKKMap_projection]
  exact KasparovHomotopyClass.mk_eq_of_iso unitRelativeCycleIso

/-- The actual Julia comparison therefore sends the actual native identity
to the actual projection class of one. -/
theorem scalarKKOperatorK0AddEquiv_identity :
    scalarKKOperatorK0AddEquiv
      (GroupUniverseParityUnits.identity.{0,0,0} scalarIdentityAction) =
        nonunitalProjectionK0 (1 : ℂ) (by
          apply isStarProjection_iff'.mpr
          exact ⟨one_mul 1, star_one _⟩) := by
  have hi : GroupUniverseParityUnits.identity.{0,0,0} scalarIdentityAction =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of scalarIdentityCycle) := by
    unfold GroupUniverseParityUnits.identity
    rw [GradedKasparovHomotopyClass.ulift_eq_self]
    rfl
  rw [hi, ← relativeMap_nonunitalUnitProjection]
  exact scalarKKOperatorK0Index_nonunitalRelativeK0KasparovMap_leftInverse _

end BC4lean.KKTheory.ScalarUnitProjection
