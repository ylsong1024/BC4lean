import BC4lean.ScalarKasparovRectangularFredholm
import BC4lean.RectangularFredholmProjectionIndex
import BC4lean.ProjectionIntertwiningHilbertModuleEquiv

/-! # The actual raw scalar-cycle K₀ index and whole-cycle isomorphism invariance

The original cycle supplies its true scalar support, supported selfadjoint
operator, homogeneous modules, and both Fredholm defects. Its actual
absorption-independent Julia index is therefore defined without extra
Fredholm or representation-unitality hypotheses. Whole cycle unitaries
restrict to support and homogeneous ranges and intertwine the whole
rectangular map, giving equality of the genuine index values.
-/

noncomputable section
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]
  {β : CStarAlgebraAction PUnit B}

namespace KasparovCycle

/-- The genuine K₀ index defined directly from the original scalar-cycle data. -/
def operatorK0Index
    (c : KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ) β E) : OperatorK0 B :=
  rectangularFredholmIndex c.scalarRectangularFredholm
    c.scalarRectangularEvenModule_isCountablyGenerated c.scalarRectangularOddModule_isCountablyGenerated
    c.scalarRectangularFredholm_source_defect c.scalarRectangularFredholm_target_defect

end KasparovCycle

variable {c : KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ) β E}
  {d : KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ) β F}

/-- The whole cycle unitary restricts to the true scalar-support module. -/
def scalarSupportIsoEquiv (e : KasparovCycleIso c d) :
    HilbertModuleEquiv B (ProjectionModule c.scalarSupportProjection) (ProjectionModule d.scalarSupportProjection) :=
  projectionIntertwiningHilbertModuleEquiv e.moduleEquiv c.scalarSupportProjection d.scalarSupportProjection
    (fun x => e.representation_intertwine 1 x)

theorem scalarSupportIso_block (e : KasparovCycleIso c d) (x : E) :
    e.moduleEquiv (c.scalarSupportBlockOperator x) =
      d.scalarSupportBlockOperator (e.moduleEquiv x) := by
  simp only [KasparovCycle.scalarSupportBlockOperator, AdjointableMap.coe_add_apply,
    AdjointableMap.mul_apply, AdjointableMap.coe_sub_apply, AdjointableMap.one_apply,
    e.moduleEquiv.map_add, e.moduleEquiv.map_sub]
  simp only [KasparovCycle.scalarSupportProjection, e.representation_intertwine,
    e.operator_intertwine, e.moduleEquiv.map_sub]

/-- The actual compressed support operator is transported exactly. -/
theorem scalarSupportIso_compression (e : KasparovCycleIso c d) :
    (scalarSupportIsoEquiv e).transport c.scalarSupportCompression = d.scalarSupportCompression := by
  apply AdjointableMap.ext
  intro x
  apply Subtype.ext
  change e.moduleEquiv (c.scalarSupportCompression ((scalarSupportIsoEquiv e).symm x) : E) =
    (d.scalarSupportCompression x : F)
  rw [c.scalarSupportCompression_coe, d.scalarSupportCompression_coe, scalarSupportIso_block]
  have hx : e.moduleEquiv ((scalarSupportIsoEquiv e).symm x : E) = (x : F) := by
    change ((scalarSupportIsoEquiv e ((scalarSupportIsoEquiv e).symm x) :
      ProjectionModule d.scalarSupportProjection) : F) = (x : F)
    rw [HilbertModuleEquiv.apply_symm_apply]
  rw [hx]

/-- Both symmetrized support operators intertwine, including their adjoints. -/
theorem scalarSupportIso_selfadjoint (e : KasparovCycleIso c d) :
    (scalarSupportIsoEquiv e).transport c.scalarSupportSelfadjointOperator =
      d.scalarSupportSelfadjointOperator := by
  change (scalarSupportIsoEquiv e).transport
    (c.scalarSupportCompression + (2 : ℂ)⁻¹ • (star c.scalarSupportCompression - c.scalarSupportCompression)) =
      d.scalarSupportCompression + (2 : ℂ)⁻¹ • (star d.scalarSupportCompression - d.scalarSupportCompression)
  rw [HilbertModuleEquiv.transport_add, HilbertModuleEquiv.transport_smul,
    HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_star, scalarSupportIso_compression]

/-- The true support-range unitary intertwines the two restricted gradings. -/
theorem scalarSupportIso_grading (e : KasparovCycleIso c d)
    (x : ProjectionModule c.scalarSupportProjection) :
    scalarSupportIsoEquiv e (c.scalarSupportGrading.grading x) =
      d.scalarSupportGrading.grading (scalarSupportIsoEquiv e x) := by
  apply Subtype.ext
  exact e.grading_intertwine (x : E)

def scalarRectangularEvenIsoEquiv (e : KasparovCycleIso c d) :
    HilbertModuleEquiv B c.scalarSupportGrading.EvenModule d.scalarSupportGrading.EvenModule :=
  c.scalarSupportGrading.evenModuleEquiv d.scalarSupportGrading (scalarSupportIsoEquiv e)
    (scalarSupportIso_grading e)

def scalarRectangularOddIsoEquiv (e : KasparovCycleIso c d) :
    HilbertModuleEquiv B c.scalarSupportGrading.OddModule d.scalarSupportGrading.OddModule :=
  c.scalarSupportGrading.oddModuleEquiv d.scalarSupportGrading (scalarSupportIsoEquiv e)
    (scalarSupportIso_grading e)

/-- Both genuine homogeneous range maps transport the actual rectangular block. -/
theorem scalarRectangularIso_operator (e : KasparovCycleIso c d) :
    (scalarRectangularEvenIsoEquiv e).transportMap (scalarRectangularOddIsoEquiv e)
      c.scalarRectangularFredholm = d.scalarRectangularFredholm := by
  exact GradedHilbertModule.homogeneousOddMap_intertwine
    c.scalarSupportGrading d.scalarSupportGrading (scalarSupportIsoEquiv e)
    (scalarSupportIso_grading e) c.scalarSupportSelfadjointOperator d.scalarSupportSelfadjointOperator
    c.scalarSupportSelfadjointOperator_isOdd d.scalarSupportSelfadjointOperator_isOdd (by
      intro x
      have h := congrArg
        (fun T : AdjointableMap B (ProjectionModule d.scalarSupportProjection)
          (ProjectionModule d.scalarSupportProjection) => T (scalarSupportIsoEquiv e x))
        (scalarSupportIso_selfadjoint e)
      simpa only [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply] using h)

/-- Every genuine whole-cycle isomorphism preserves the actual scalar K₀ index. -/
theorem scalarKasparovOperatorK0Index_iso (e : KasparovCycleIso c d) : c.operatorK0Index = d.operatorK0Index := by
  have h := rectangularFredholmIndex_transport (scalarRectangularEvenIsoEquiv e)
    (scalarRectangularOddIsoEquiv e) c.scalarRectangularFredholm
    c.scalarRectangularEvenModule_isCountablyGenerated c.scalarRectangularOddModule_isCountablyGenerated
    d.scalarRectangularEvenModule_isCountablyGenerated d.scalarRectangularOddModule_isCountablyGenerated
    c.scalarRectangularFredholm_source_defect c.scalarRectangularFredholm_target_defect
    (by rw [scalarRectangularIso_operator]; exact d.scalarRectangularFredholm_source_defect)
    (by rw [scalarRectangularIso_operator]; exact d.scalarRectangularFredholm_target_defect)
  simpa only [KasparovCycle.operatorK0Index, scalarRectangularIso_operator] using h

end BC4lean.KKTheory
