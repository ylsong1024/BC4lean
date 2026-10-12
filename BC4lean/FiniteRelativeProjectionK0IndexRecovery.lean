import BC4lean.FiniteJuliaProjectionIndexRecovery
import BC4lean.GlobalFredholmScalarCycleK0Index
import BC4lean.RelativeProjectionCocycleOperators

/-! # The independently constructed Julia index recovers finite relative pairs

The actual range cross map has the two compact Fredholm defects derived
from the equal-scalar matrix difference. Absorption independence permits
the two genuine aligned projective stabilizations. The whole finite Julia
calculation therefore computes the raw supported-cycle index as [p]-[q].
-/

noncomputable section
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory

variable {B : Type*} {ι : Type} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B] [Fintype ι] [DecidableEq ι]
local notation "FinMod" => FiniteStandardModule B ι
local instance standardFiniteRelativeProjectionK0IndexRecoveryLocalInstance01 : CompleteSpace FinMod := finiteStandardModule_complete
local instance standardFiniteRelativeProjectionK0IndexRecoveryLocalInstance02 (A : Type*) [CStarAlgebra A] : PartialOrder A := CStarAlgebra.spectralOrder A
local instance standardFiniteRelativeProjectionK0IndexRecoveryLocalInstance03 (A : Type*) [CStarAlgebra A] : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

/-- Genuine finite-pair recovery of the raw rectangular index. -/
theorem unitizedRelativeProjectionCycle_operatorK0Index
    (p q : MatrixProjection (Unitization ℂ B) ι)
    (h : ∀ i j, (p.val i j).fst = (q.val i j).fst) :
    (unitizedRelativeProjectionCycle (Γ := PUnit) p q h).operatorK0Index =
      equalScalarProjectionDifference p q h := by
  let P : AdjointableMap B FinMod FinMod := unitizedProjectionOperator p
  let Q : AdjointableMap B FinMod FinMod := unitizedProjectionOperator q
  have hP : IsStarProjection P := unitizedProjectionOperator_isStarProjection p
  have hQ : IsStarProjection Q := unitizedProjectionOperator_isStarProjection q
  have hc : IsModuleCompact (P - Q) := unitizedModuleMatrixRepresentation_sub_isModuleCompact p q h
  let T := projectionCrossMap P Q hP hQ
  have hs : IsModuleCompact (1 - T.adjoint.comp T) :=
    projectionCrossMap_source_defect_isModuleCompact P Q hP hQ hc
  have ht : IsModuleCompact (T.comp T.adjoint - 1) :=
    projectionCrossMap_target_defect_isModuleCompact P Q hP hQ hc
  have he : IsCountablyGeneratedModule B (ProjectionModule P) :=
    projectionModule_isCountablyGenerated P hP finiteStandardModule_isCountablyGenerated_nonunital
  have hf : IsCountablyGeneratedModule B (ProjectionModule Q) :=
    projectionModule_isCountablyGenerated Q hQ finiteStandardModule_isCountablyGenerated_nonunital
  have hRaw : (unitizedRelativeProjectionCycle (Γ := PUnit) p q h).operatorK0Index =
      rectangularFredholmIndex T he hf hs ht :=
    relativeProjectionCycle_operatorK0Index P Q hP hQ hc finiteStandardModule_isCountablyGenerated_nonunital
  rw [hRaw, rectangularFredholmIndex_absorption_independent T he hf hs ht
    (finiteProjectionAlignedAbsorption P hP) (finiteProjectionAlignedAbsorption Q hQ)]
  change standardNormalizedRectangularFredholmIndex (finiteAlignedUnitizationFredholm p q) _ _ = _
  have hScalar : unitizationScalarMatrix (p : CStarMatrix ι ι (Unitization ℂ B)) =
      unitizationScalarMatrix (q : CStarMatrix ι ι (Unitization ℂ B)) := by
    apply CStarMatrix.ext
    intro i j
    exact h i j
  have hClass : unitizationRelativeProjectionK0 p q p.property q.property hScalar =
      equalScalarProjectionDifference p q h := by
    apply operatorK0Inclusion_injective B
    rw [operatorK0Inclusion_unitizationRelativeProjectionK0,
      equalScalarProjectionDifference_inclusion]
    simp only [k0Projection_finiteProjectionOfMatrix, unitizationFiniteProjection]
  rw [← hClass]
  exact finiteAlignedUnitizationFredholm_index_recovery p q hScalar _ _

end BC4lean.KKTheory
