import BC4lean.ScalarKasparovOperatorK0Index
import BC4lean.CanonicalGradedSumHomogeneousEquiv

/-! # Recovering the rectangular index of the actual rectangular scalar cycle

The scalar support is the actual identity for these cycles. Its whole range
unitary removes only that redundant support presentation; selfadjointness
makes the defined symmetrization vanish. Genuine homogeneous coordinate
unitaries then recover the original rectangular operator and its index.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

local instance standardGlobalFredholmScalarCycleK0IndexLocalInstance01 {M N : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Bᵐᵒᵖ M]
    [CStarModule Bᵐᵒᵖ M] [CompleteSpace M] [NormedAddCommGroup N] [NormedSpace ℂ N]
    [SMul Bᵐᵒᵖ N] [CStarModule Bᵐᵒᵖ N] [CompleteSpace N] :
    CompleteSpace (HilbertModuleSum B M N) := hilbertModuleSum_complete

section Support
variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Bᵐᵒᵖ M]
  [CStarModule Bᵐᵒᵖ M] [CompleteSpace M]
  (c : KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
    (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B) M)
  (hUnit : c.representation 1 = 1)

def scalarUnitalSupportEquiv : HilbertModuleEquiv B (ProjectionModule c.scalarSupportProjection) M where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun x := (x : M)
          invFun x := ⟨x, by change c.representation 1 x = x; rw [hUnit]; rfl⟩
          left_inv _ := rfl
          right_inv _ := rfl
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      norm_map' _ := rfl }
  inner_map _ _ := rfl

theorem scalarUnitalSupportEquiv_grading (x : ProjectionModule c.scalarSupportProjection) :
    scalarUnitalSupportEquiv c hUnit (c.scalarSupportGrading.grading x) =
      c.grading.grading (scalarUnitalSupportEquiv c hUnit x) := rfl

theorem scalarUnitalSupportEquiv_compression :
    (scalarUnitalSupportEquiv c hUnit).transport c.scalarSupportCompression = c.operator := by
  ext x
  change (c.scalarSupportCompression ((scalarUnitalSupportEquiv c hUnit).symm x) : M) = c.operator x
  rw [c.scalarSupportCompression_coe]
  change c.scalarSupportBlockOperator x = c.operator x
  simp only [KasparovCycle.scalarSupportBlockOperator, KasparovCycle.scalarSupportProjection,
    hUnit, one_mul, mul_one, sub_self, zero_mul, mul_zero, add_zero]

theorem scalarUnitalSupportEquiv_selfadjoint (hSelf : IsSelfAdjoint c.operator) :
    (scalarUnitalSupportEquiv c hUnit).transport c.scalarSupportSelfadjointOperator = c.operator := by
  change (scalarUnitalSupportEquiv c hUnit).transport
    (c.scalarSupportCompression + (2 : ℂ)⁻¹ • (star c.scalarSupportCompression - c.scalarSupportCompression)) = _
  rw [HilbertModuleEquiv.transport_add, HilbertModuleEquiv.transport_smul,
    HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_star,
    scalarUnitalSupportEquiv_compression, hSelf.star_eq, sub_self, smul_zero, add_zero]

def scalarUnitalEvenEquiv : HilbertModuleEquiv B c.scalarSupportGrading.EvenModule c.grading.EvenModule :=
  c.scalarSupportGrading.evenModuleEquiv c.grading (scalarUnitalSupportEquiv c hUnit)
    (scalarUnitalSupportEquiv_grading c hUnit)

def scalarUnitalOddEquiv : HilbertModuleEquiv B c.scalarSupportGrading.OddModule c.grading.OddModule :=
  c.scalarSupportGrading.oddModuleEquiv c.grading (scalarUnitalSupportEquiv c hUnit)
    (scalarUnitalSupportEquiv_grading c hUnit)

theorem scalarUnitalHomogeneousOperator (hSelf : IsSelfAdjoint c.operator) :
    (scalarUnitalEvenEquiv c hUnit).transportMap (scalarUnitalOddEquiv c hUnit)
      c.scalarRectangularFredholm = c.grading.homogeneousOddMap c.operator := by
  apply c.scalarSupportGrading.homogeneousOddMap_intertwine c.grading
    (scalarUnitalSupportEquiv c hUnit) (scalarUnitalSupportEquiv_grading c hUnit)
    c.scalarSupportSelfadjointOperator c.operator c.scalarSupportSelfadjointOperator_isOdd c.operator_odd
  intro x
  have h := congrArg (fun T => T (scalarUnitalSupportEquiv c hUnit x))
    (scalarUnitalSupportEquiv_selfadjoint c hUnit hSelf)
  simpa only [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply] using h

end Support

theorem globalFredholmScalarCycle_operatorK0Index (T : AdjointableMap B E F)
    (hs : IsModuleCompact (1 - T.adjoint.comp T))
    (ht : IsModuleCompact (T.comp T.adjoint - 1))
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F) :
    (globalFredholmScalarCycle (Γ := PUnit) T hs ht hE hF).operatorK0Index =
      rectangularFredholmIndex T hE hF hs ht := by
  let c := globalFredholmScalarCycle (Γ := PUnit) T hs ht hE hF
  have hUnit : c.representation 1 = 1 := by ext x; exact one_smul ℂ x
  have hSelf : IsSelfAdjoint c.operator := offDiagonalAdjointable_star T
  let u := (scalarUnitalEvenEquiv c hUnit).trans
    (canonicalGradedSumEvenEmbeddingEquiv (B := B) (E := E) (F := F)).symm
  let v := (scalarUnitalOddEquiv c hUnit).trans
    (canonicalGradedSumOddEmbeddingEquiv (B := B) (E := E) (F := F)).symm
  have hOp : u.transportMap v c.scalarRectangularFredholm = T := by
    have he : u.transportMap v c.scalarRectangularFredholm =
        (canonicalGradedSumEvenEmbeddingEquiv (B := B) (E := E) (F := F)).symm.transportMap
          (canonicalGradedSumOddEmbeddingEquiv (B := B) (E := E) (F := F)).symm
          ((scalarUnitalEvenEquiv c hUnit).transportMap (scalarUnitalOddEquiv c hUnit)
            c.scalarRectangularFredholm) := by
      ext x
      rfl
    rw [he]
    have hHom := scalarUnitalHomogeneousOperator c hUnit hSelf
    exact (congrArg
      (fun S : AdjointableMap B c.grading.EvenModule c.grading.OddModule =>
        (canonicalGradedSumEvenEmbeddingEquiv (B := B) (E := E) (F := F)).symm.transportMap
          (canonicalGradedSumOddEmbeddingEquiv (B := B) (E := E) (F := F)).symm S)
      hHom).trans (canonicalGradedSum_homogeneousOddMap T)
  have h := rectangularFredholmIndex_transport u v c.scalarRectangularFredholm
    c.scalarRectangularEvenModule_isCountablyGenerated c.scalarRectangularOddModule_isCountablyGenerated
    hE hF c.scalarRectangularFredholm_source_defect c.scalarRectangularFredholm_target_defect
    (by rw [hOp]; exact hs) (by rw [hOp]; exact ht)
  simpa only [KasparovCycle.operatorK0Index, hOp] using h

theorem relativeProjectionCycle_operatorK0Index (P Q : AdjointableMap B E E)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hc : IsModuleCompact (P - Q)) (hE : IsCountablyGeneratedModule B E) :
    (relativeProjectionCycle (Γ := PUnit) P Q hP hQ hc hE).operatorK0Index =
      rectangularFredholmIndex (projectionCrossMap P Q hP hQ)
        (projectionModule_isCountablyGenerated P hP hE) (projectionModule_isCountablyGenerated Q hQ hE)
        (by
          have hh := (hc.comp_left (projectionCorestrict P hP)).comp_right (projectionInclusion P hP)
          convert hh using 1
          ext x
          rw [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, Submodule.coe_sub]
          change (x : E) - P (Q (x : E)) = P ((P - Q) (x : E))
          have hx : P (x : E) = (x : E) := x.property
          simp only [AdjointableMap.coe_sub_apply, P.toCLM.map_sub, hx])
        (by
          have hh := (hc.comp_left (projectionCorestrict Q hQ)).comp_right (projectionInclusion Q hQ)
          convert hh using 1
          ext x
          rw [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, Submodule.coe_sub]
          change Q (P (x : E)) - (x : E) = Q ((P - Q) (x : E))
          have hx : Q (x : E) = (x : E) := x.property
          simp only [AdjointableMap.coe_sub_apply, Q.toCLM.map_sub, hx]) := by
  exact globalFredholmScalarCycle_operatorK0Index (projectionCrossMap P Q hP hQ) _ _ _ _

end BC4lean.KKTheory
