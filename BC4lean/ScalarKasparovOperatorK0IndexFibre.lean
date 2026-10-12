import BC4lean.ScalarKasparovOperatorK0Index
import BC4lean.RectangularFredholmFullIntervalIndex
import BC4lean.GradedHomogeneousModuleFibreEquiv

/-! # Genuine scalar K₀ index on arbitrary interval-cycle fibres

Support compression and its selfadjoint symmetrization evaluate under the
actual support-range fibre unitary. The genuine homogeneous range-fibre
unitaries transport the entire rectangular block. Arbitrary-module interval
index invariance then proves endpoint equality of the original scalar-cycle
indices, including degenerate scalar representations.
-/

noncomputable section
namespace BC4lean.KKTheory
open unitInterval
open scoped CStarAlgebra

variable {B M : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(I, B)ᵐᵒᵖ M]
  [CStarModule C(I, B)ᵐᵒᵖ M] [CompleteSpace M]
  {β : CStarAlgebraAction PUnit B}
variable (c : KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
  (β.continuousSections (X := I)) M)

/-- The true scalar-support fibre unitary, derived from actual projection ranges. -/
def scalarSupportFibreEquiv (t : I) :
    HilbertModuleEquiv B (HilbertModuleFibre B (ProjectionModule c.scalarSupportProjection) t)
      (ProjectionModule (c.fibre t).scalarSupportProjection) :=
  oddFredholmProjectionFibreEquiv c.scalarSupportProjection c.scalarSupportProjection_isStarProjection t

theorem scalarSupportBlock_fibre (t : I) :
    hilbertModuleFibreOperator (B := B) t c.scalarSupportBlockOperator =
      (c.fibre t).scalarSupportBlockOperator := by
  simp only [KasparovCycle.scalarSupportBlockOperator, KasparovCycle.scalarSupportProjection,
    KasparovCycle.fibre, hilbertModuleFibreOperator_add, hilbertModuleFibreOperator_mul,
    hilbertModuleFibreOperator_sub, hilbertModuleFibreOperator_one]
  rfl

set_option maxHeartbeats 2000000 in
theorem scalarSupportFibreEquiv_compression_intertwine (t : I)
    (z : HilbertModuleFibre B (ProjectionModule c.scalarSupportProjection) t) :
    scalarSupportFibreEquiv c t (hilbertModuleFibreOperator t c.scalarSupportCompression z) =
      (c.fibre t).scalarSupportCompression (scalarSupportFibreEquiv c t z) := by
  let U := scalarSupportFibreEquiv c t
  have hmk (x : ProjectionModule c.scalarSupportProjection) :
      ((U (hilbertModuleFibreMk (B := B) t x) :
        ProjectionModule (c.fibre t).scalarSupportProjection) : HilbertModuleFibre B M t) =
      hilbertModuleFibreMk (B := B) t (x : M) :=
    oddFredholmProjectionFibreEquiv_mk c.scalarSupportProjection
      c.scalarSupportProjection_isStarProjection t x
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B)
    (M := ProjectionModule c.scalarSupportProjection) t z
  apply Subtype.ext
  calc
    ((U (hilbertModuleFibreOperator (B := B) t c.scalarSupportCompression
        (hilbertModuleFibreMk (B := B) t x)) :
      ProjectionModule (c.fibre t).scalarSupportProjection) : HilbertModuleFibre B M t) =
        ((U (hilbertModuleFibreMk (B := B) t (c.scalarSupportCompression x)) :
          ProjectionModule (c.fibre t).scalarSupportProjection) : HilbertModuleFibre B M t) :=
      congrArg (fun y : HilbertModuleFibre B (ProjectionModule c.scalarSupportProjection) t =>
        ((U y : ProjectionModule (c.fibre t).scalarSupportProjection) : HilbertModuleFibre B M t))
        (hilbertModuleFibreOperator_mk (B := B) t c.scalarSupportCompression x)
    _ = hilbertModuleFibreMk (B := B) t (c.scalarSupportCompression x : M) := hmk _
    _ = hilbertModuleFibreMk (B := B) t (c.scalarSupportBlockOperator (x : M)) :=
      congrArg (fun y : M => hilbertModuleFibreMk (B := B) t y) (c.scalarSupportCompression_coe x)
    _ = hilbertModuleFibreOperator (B := B) t c.scalarSupportBlockOperator
        (hilbertModuleFibreMk (B := B) t (x : M)) :=
      (hilbertModuleFibreOperator_mk (B := B) t c.scalarSupportBlockOperator (x : M)).symm
    _ = (c.fibre t).scalarSupportBlockOperator (hilbertModuleFibreMk (B := B) t (x : M)) :=
      congrArg (fun S : AdjointableMap B (HilbertModuleFibre B M t)
        (HilbertModuleFibre B M t) => S (hilbertModuleFibreMk (B := B) t (x : M)))
        (scalarSupportBlock_fibre c t)
    _ = (c.fibre t).scalarSupportBlockOperator
        ((U (hilbertModuleFibreMk (B := B) t x) :
          ProjectionModule (c.fibre t).scalarSupportProjection) : HilbertModuleFibre B M t) :=
      congrArg (fun y : HilbertModuleFibre B M t => (c.fibre t).scalarSupportBlockOperator y)
        (hmk x).symm
    _ = ((c.fibre t).scalarSupportCompression (U (hilbertModuleFibreMk (B := B) t x)) :
        HilbertModuleFibre B M t) :=
      ((c.fibre t).scalarSupportCompression_coe (U (hilbertModuleFibreMk (B := B) t x))).symm

/-- The actual unital hom from global support operators to native fibre support operators. -/
def scalarSupportFibreOperatorHom (t : I) :
    AdjointableMap C(I, B) (ProjectionModule c.scalarSupportProjection) (ProjectionModule c.scalarSupportProjection)
      →⋆ₐ[ℂ] AdjointableMap B (ProjectionModule (c.fibre t).scalarSupportProjection)
        (ProjectionModule (c.fibre t).scalarSupportProjection) :=
  (scalarSupportFibreEquiv c t).transportStarAlgEquiv.toStarAlgHom.comp
    (hilbertModuleFibreOperatorHom (B := B) t)

set_option maxHeartbeats 2000000 in
theorem scalarSupportFibreOperatorHom_compression (t : I) :
    scalarSupportFibreOperatorHom c t c.scalarSupportCompression = (c.fibre t).scalarSupportCompression := by
  let U := scalarSupportFibreEquiv c t
  have hhom : scalarSupportFibreOperatorHom c t c.scalarSupportCompression =
      U.transport (hilbertModuleFibreOperator (B := B) t c.scalarSupportCompression) := rfl
  refine hhom.trans ?_
  apply AdjointableMap.ext
  intro x
  exact (HilbertModuleEquiv.transport_apply U
    (hilbertModuleFibreOperator (B := B) t c.scalarSupportCompression) x).trans
    ((scalarSupportFibreEquiv_compression_intertwine c t (U.symm x)).trans
      (congrArg (fun y : ProjectionModule (c.fibre t).scalarSupportProjection =>
        (c.fibre t).scalarSupportCompression y) (U.apply_symm_apply x)))

/-- Genuine symmetrization evaluates exactly, including the whole adjoint. -/
theorem scalarSupportFibreOperatorHom_selfadjoint (t : I) :
    scalarSupportFibreOperatorHom c t c.scalarSupportSelfadjointOperator =
      (c.fibre t).scalarSupportSelfadjointOperator := by
  change scalarSupportFibreOperatorHom c t
    (c.scalarSupportCompression + (2 : ℂ)⁻¹ • (star c.scalarSupportCompression - c.scalarSupportCompression)) =
      (c.fibre t).scalarSupportCompression +
        (2 : ℂ)⁻¹ • (star (c.fibre t).scalarSupportCompression - (c.fibre t).scalarSupportCompression)
  rw [map_add, map_smul, map_sub, map_star, scalarSupportFibreOperatorHom_compression]

set_option maxHeartbeats 2000000 in
/-- The actual support unitary intertwines the evaluated and native gradings. -/
theorem scalarSupportFibreEquiv_grading (t : I)
    (x : HilbertModuleFibre B (ProjectionModule c.scalarSupportProjection) t) :
    scalarSupportFibreEquiv c t ((c.scalarSupportGrading.fibre t).grading x) =
      (c.fibre t).scalarSupportGrading.grading (scalarSupportFibreEquiv c t x) := by
  let U := scalarSupportFibreEquiv c t
  have hmk (v : ProjectionModule c.scalarSupportProjection) :
      ((U (hilbertModuleFibreMk (B := B) t v) :
        ProjectionModule (c.fibre t).scalarSupportProjection) : HilbertModuleFibre B M t) =
      hilbertModuleFibreMk (B := B) t (v : M) :=
    oddFredholmProjectionFibreEquiv_mk c.scalarSupportProjection
      c.scalarSupportProjection_isStarProjection t v
  obtain ⟨v, rfl⟩ := hilbertModuleFibreMk_surjective (B := B)
    (M := ProjectionModule c.scalarSupportProjection) t x
  apply Subtype.ext
  calc
    ((U ((c.scalarSupportGrading.fibre t).grading (hilbertModuleFibreMk (B := B) t v)) :
      ProjectionModule (c.fibre t).scalarSupportProjection) : HilbertModuleFibre B M t) =
      ((U (hilbertModuleFibreMk (B := B) t (c.scalarSupportGrading.grading v)) :
        ProjectionModule (c.fibre t).scalarSupportProjection) : HilbertModuleFibre B M t) :=
      congrArg (fun y : HilbertModuleFibre B (ProjectionModule c.scalarSupportProjection) t =>
        ((U y : ProjectionModule (c.fibre t).scalarSupportProjection) : HilbertModuleFibre B M t))
        (GradedHilbertModule.fibre_grading_mk c.scalarSupportGrading t v)
    _ = hilbertModuleFibreMk (B := B) t (c.scalarSupportGrading.grading v : M) := hmk _
    _ = hilbertModuleFibreMk (B := B) t (c.grading.grading (v : M)) :=
      congrArg (fun y : M => hilbertModuleFibreMk (B := B) t y) (c.scalarSupportGrading_coe v)
    _ = (c.fibre t).grading.grading (hilbertModuleFibreMk (B := B) t (v : M)) :=
      (c.fibre_grading_mk t (v : M)).symm
    _ = (c.fibre t).grading.grading
      ((U (hilbertModuleFibreMk (B := B) t v) :
        ProjectionModule (c.fibre t).scalarSupportProjection) : HilbertModuleFibre B M t) :=
      congrArg (fun y : HilbertModuleFibre B M t => (c.fibre t).grading.grading y) (hmk v).symm
    _ = ((c.fibre t).scalarSupportGrading.grading (U (hilbertModuleFibreMk (B := B) t v)) :
        HilbertModuleFibre B M t) :=
      ((c.fibre t).scalarSupportGrading_coe (U (hilbertModuleFibreMk (B := B) t v))).symm

/-- The whole true fibre equivalence of the even homogeneous support module. -/
def scalarRectangularEvenFibreEquiv (t : I) :
    HilbertModuleEquiv B (HilbertModuleFibre B c.scalarSupportGrading.EvenModule t)
      (c.fibre t).scalarSupportGrading.EvenModule :=
  (c.scalarSupportGrading.evenModuleFibreEquiv t).trans
    ((c.scalarSupportGrading.fibre t).evenModuleEquiv (c.fibre t).scalarSupportGrading
      (scalarSupportFibreEquiv c t) (scalarSupportFibreEquiv_grading c t))

/-- The whole true fibre equivalence of the odd homogeneous support module. -/
def scalarRectangularOddFibreEquiv (t : I) :
    HilbertModuleEquiv B (HilbertModuleFibre B c.scalarSupportGrading.OddModule t)
      (c.fibre t).scalarSupportGrading.OddModule :=
  (c.scalarSupportGrading.oddModuleFibreEquiv t).trans
    ((c.scalarSupportGrading.fibre t).oddModuleEquiv (c.fibre t).scalarSupportGrading
      (scalarSupportFibreEquiv c t) (scalarSupportFibreEquiv_grading c t))

set_option maxHeartbeats 2000000 in
/-- Both actual homogeneous fibres intertwine the whole native rectangular operator. -/
theorem scalarRectangularFibre_operator (t : I) :
    (scalarRectangularEvenFibreEquiv c t).transportMap (scalarRectangularOddFibreEquiv c t)
      (rectangularFredholmFibre t c.scalarRectangularFredholm) =
        (c.fibre t).scalarRectangularFredholm := by
  rw [scalarRectangularEvenFibreEquiv, scalarRectangularOddFibreEquiv,
    rectangularFredholmTransportMap_trans]
  simp only [rectangularFredholmFibre, KasparovCycle.scalarRectangularFredholm]
  rw [GradedHilbertModule.homogeneousOddMap_fibre _ t c.scalarSupportSelfadjointOperator
    c.scalarSupportSelfadjointOperator_isOdd]
  apply GradedHilbertModule.homogeneousOddMap_intertwine
  · exact c.scalarSupportGrading.isOdd_fibre t c.scalarSupportSelfadjointOperator_isOdd
  · exact (c.fibre t).scalarSupportSelfadjointOperator_isOdd
  · intro x
    let U := scalarSupportFibreEquiv c t
    let S := hilbertModuleFibreOperator (B := B) t c.scalarSupportSelfadjointOperator
    have hhom : scalarSupportFibreOperatorHom c t c.scalarSupportSelfadjointOperator =
        U.transport S := rfl
    have hop : U.transport S = (c.fibre t).scalarSupportSelfadjointOperator :=
      hhom.symm.trans (scalarSupportFibreOperatorHom_selfadjoint c t)
    have heval : U.transport S (U x) = U (S x) :=
      (HilbertModuleEquiv.transport_apply U S (U x)).trans
        (congrArg (fun y : HilbertModuleFibre B (ProjectionModule c.scalarSupportProjection) t =>
          U (S y)) (U.symm_apply_apply x))
    exact heval.symm.trans
      (congrArg (fun R : AdjointableMap B (ProjectionModule (c.fibre t).scalarSupportProjection)
        (ProjectionModule (c.fibre t).scalarSupportProjection) => R (U x)) hop)

set_option maxHeartbeats 2000000 in
/-- The raw native fibre-cycle index is the actual globally constructed rectangular fibre index. -/
theorem scalarKasparovOperatorK0Index_fibre (t : I) :
    (c.fibre t).operatorK0Index =
      rectangularFredholmIndex (rectangularFredholmFibre t c.scalarRectangularFredholm)
        (c.scalarRectangularEvenModule_isCountablyGenerated.fibre t)
        (c.scalarRectangularOddModule_isCountablyGenerated.fibre t)
        (rectangularFredholmFibre_source_defect t _ c.scalarRectangularFredholm_source_defect)
        (rectangularFredholmFibre_target_defect t _ c.scalarRectangularFredholm_target_defect) := by
  symm
  have h := rectangularFredholmIndex_transport (scalarRectangularEvenFibreEquiv c t)
    (scalarRectangularOddFibreEquiv c t) (rectangularFredholmFibre t c.scalarRectangularFredholm)
    (c.scalarRectangularEvenModule_isCountablyGenerated.fibre t)
    (c.scalarRectangularOddModule_isCountablyGenerated.fibre t)
    (c.fibre t).scalarRectangularEvenModule_isCountablyGenerated
    (c.fibre t).scalarRectangularOddModule_isCountablyGenerated
    (rectangularFredholmFibre_source_defect t _ c.scalarRectangularFredholm_source_defect)
    (rectangularFredholmFibre_target_defect t _ c.scalarRectangularFredholm_target_defect)
    (by rw [scalarRectangularFibre_operator]; exact (c.fibre t).scalarRectangularFredholm_source_defect)
    (by rw [scalarRectangularFibre_operator]; exact (c.fibre t).scalarRectangularFredholm_target_defect)
  simpa only [KasparovCycle.operatorK0Index, scalarRectangularFibre_operator] using h

set_option maxHeartbeats 2000000 in
/-- Every actual arbitrary scalar interval cycle has equal genuine endpoint K₀ indices. -/
theorem scalarKasparovOperatorK0Index_fibre_endpoints :
    (c.fibre 0).operatorK0Index = (c.fibre 1).operatorK0Index := by
  rw [scalarKasparovOperatorK0Index_fibre, scalarKasparovOperatorK0Index_fibre]
  exact rectangularFredholmFullIntervalIndex_endpoints
    c.scalarRectangularEvenModule_isCountablyGenerated
    c.scalarRectangularOddModule_isCountablyGenerated
    c.scalarRectangularFredholm
    c.scalarRectangularFredholm_source_defect c.scalarRectangularFredholm_target_defect

end BC4lean.KKTheory
