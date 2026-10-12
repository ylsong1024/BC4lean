import BC4lean.CliffordEvenOddSourceHilbert

/-! # The actual product criterion for external even followed by signed odd

All four homogeneous creators follow from the true all-vector extracted
signed errors through the complete Pauli/balanced tensor unitary. Both
original localized positive lifts form the actual Hilbert-sum lift. The
operator is the transported entire signed corner cycle, so its localized
Fredholm conditions are retained rather than assumed.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordEvenOddSource

variable {Γ A B C H F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace H] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C}
  (c : GradedKasparovCycle α β CStarGrading.trivial CStarGrading.trivial H)
  (d : OddKasparovCycle β γ F)

local instance criterionSecondSumComplete : CompleteSpace (HilbertModuleSum C F F) := hilbertModuleSum_complete
local instance criterionTargetSumComplete : CompleteSpace (Target (H := H) d) := hilbertModuleSum_complete

set_option maxHeartbeats 1200000 in
/-- The exact compact signed creator law is returned to the original
completed tensor using the actual onto coefficient-form unitary. -/
theorem creator_error_compact
    (P : AdjointableMap C (Source (H := H) d) (Source d))
    (G : AdjointableMap C (Base (H := H) d) (Base d)) (D : AdjointableMap C F F)
    (hP : (distribution d).transport P = CliffordOddConditionalConnection.candidate
      d.representation c.grading G)
    (hG : ∀ x : H, IsModuleCompact (G.comp (moduleCreationMap d.representation x) -
      (moduleCreationMap d.representation (c.grading.grading x)).comp D))
    (x : CliffordPairModule B H) :
    IsModuleCompact (P.comp (moduleCreationMap (CliffordOddSourceCycle.cycle d).representation x) -
      (moduleCreationMap (CliffordOddSourceCycle.cycle d).representation
        ((CliffordExternalEvenCycle.cycle c).grading.grading x)).comp
          (CliffordOddSourceCycle.operator D)) := by
  have h := CliffordOddConditionalConnection.compact_creation_defect
    d.representation c.grading G D hG x
  have hs := h.comp_left (distribution d).symm.toAdjointable
  have hcreation (z : CliffordPairModule B H) (y : HilbertModuleSum C F F) :
      distribution d (moduleCreationMap (CliffordOddSourceCycle.cycle d).representation z y) =
        CliffordOddBalancedTensor.coordinateCreation d.representation z y := by
    change distribution d
      (interiorModuleTensorMk (CliffordOddSourceCycle.cycle d).representation z y) = _
    rw [distribution_mk, CliffordOddBalancedTensor.coordinateCreation_apply]
  have hgrading : (CliffordExternalEvenCycle.cycle c).grading.grading x =
      cliffordPairMk (B := B) (c.grading.grading x.2) (c.grading.grading x.1) := rfl
  convert hs using 1
  ext y
  apply (distribution d).injective
  simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
    HilbertModuleEquiv.toAdjointable_apply]
  change distribution d
      (P (moduleCreationMap (CliffordOddSourceCycle.cycle d).representation x y) -
        moduleCreationMap (CliffordOddSourceCycle.cycle d).representation
          ((CliffordExternalEvenCycle.cycle c).grading.grading x) (CliffordOddSourceCycle.operator D y)) =
    distribution d ((distribution d).symm
      (CliffordOddConditionalConnection.candidate d.representation c.grading G
          (CliffordOddBalancedTensor.coordinateCreation d.representation x y) -
        CliffordOddBalancedTensor.coordinateCreation d.representation
          (cliffordPairMk (B := B) (c.grading.grading x.2) (c.grading.grading x.1))
          (CliffordOddSourceCycle.operator D y)))
  rw [HilbertModuleEquiv.map_sub, HilbertModuleEquiv.apply_symm_apply]
  have hPy := congrArg (fun Q : AdjointableMap C (Target d) (Target d) => Q
    (distribution d (moduleCreationMap (CliffordOddSourceCycle.cycle d).representation x y))) hP
  simp only [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply] at hPy
  rw [hPy, hcreation, hgrading, hcreation]

variable (R : AdjointableMap (C × C) (CliffordEvenOddCorner.Source d) (CliffordEvenOddCorner.Source d))
  (hR : IsGradedKasparovProductOperator c d.cliffordExpansion R)

theorem connection : GradedKasparovConnection (CliffordExternalEvenCycle.cycle c)
    (CliffordOddSourceCycle.cycle d) (productOperator c d R hR.cycleConditions) where
  even x hx := by
    have hD : (CliffordOddSourceCycle.cycle d).operator =
        CliffordOddSourceCycle.operator d.operator := rfl
    rw [hD]
    have h := creator_error_compact c d (productOperator c d R hR.cycleConditions)
      (cornerCycle c d R hR.cycleConditions).operator d.operator
      (distribution_productOperator c d R hR.cycleConditions)
      (fun x => CliffordPairSecondTensor.extracted_creation_defect c d R hR x) x
    rw [hx] at h
    simpa only [neg_sub] using h.neg
  even_adjoint x hx := by
    have hD : (CliffordOddSourceCycle.cycle d).operator =
        CliffordOddSourceCycle.operator d.operator := rfl
    rw [hD, CliffordOddSourceCycle.operator_star]
    have hP : (distribution d).transport (star (productOperator c d R hR.cycleConditions)) =
        CliffordOddConditionalConnection.candidate d.representation c.grading
          (star (cornerCycle c d R hR.cycleConditions).operator) := by
      rw [HilbertModuleEquiv.transport_star, distribution_productOperator,
        CliffordOddConditionalConnection.candidate_star]
    have h := creator_error_compact c d (star (productOperator c d R hR.cycleConditions))
      (star (cornerCycle c d R hR.cycleConditions).operator) (star d.operator) hP
      (fun x => CliffordPairSecondTensor.extracted_adjoint_creation_defect c d R hR x) x
    rw [hx] at h
    simpa only [neg_sub] using h.neg
  odd x hx := by
    have hD : (CliffordOddSourceCycle.cycle d).operator =
        CliffordOddSourceCycle.operator d.operator := rfl
    rw [hD]
    have h := creator_error_compact c d (productOperator c d R hR.cycleConditions)
      (cornerCycle c d R hR.cycleConditions).operator d.operator
      (distribution_productOperator c d R hR.cycleConditions)
      (fun x => CliffordPairSecondTensor.extracted_creation_defect c d R hR x) x
    rw [hx, moduleCreationMap_neg] at h
    have heq : (productOperator c d R hR.cycleConditions).comp
        (moduleCreationMap (CliffordOddSourceCycle.cycle d).representation x) -
          (-moduleCreationMap (CliffordOddSourceCycle.cycle d).representation x).comp
            (CliffordOddSourceCycle.operator d.operator) =
        (moduleCreationMap (CliffordOddSourceCycle.cycle d).representation x).comp
          (CliffordOddSourceCycle.operator d.operator) +
            (productOperator c d R hR.cycleConditions).comp
              (moduleCreationMap (CliffordOddSourceCycle.cycle d).representation x) := by
      ext y
      simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
        AdjointableMap.coe_add_apply, AdjointableMap.coe_neg_apply]
      abel
    rwa [heq] at h
  odd_adjoint x hx := by
    have hD : (CliffordOddSourceCycle.cycle d).operator =
        CliffordOddSourceCycle.operator d.operator := rfl
    rw [hD, CliffordOddSourceCycle.operator_star]
    have hP : (distribution d).transport (star (productOperator c d R hR.cycleConditions)) =
        CliffordOddConditionalConnection.candidate d.representation c.grading
          (star (cornerCycle c d R hR.cycleConditions).operator) := by
      rw [HilbertModuleEquiv.transport_star, distribution_productOperator,
        CliffordOddConditionalConnection.candidate_star]
    have h := creator_error_compact c d (star (productOperator c d R hR.cycleConditions))
      (star (cornerCycle c d R hR.cycleConditions).operator) (star d.operator) hP
      (fun x => CliffordPairSecondTensor.extracted_adjoint_creation_defect c d R hR x) x
    rw [hx, moduleCreationMap_neg] at h
    have heq : (star (productOperator c d R hR.cycleConditions)).comp
        (moduleCreationMap (CliffordOddSourceCycle.cycle d).representation x) -
          (-moduleCreationMap (CliffordOddSourceCycle.cycle d).representation x).comp
            (CliffordOddSourceCycle.operator (star d.operator)) =
        (moduleCreationMap (CliffordOddSourceCycle.cycle d).representation x).comp
          (CliffordOddSourceCycle.operator (star d.operator)) +
            (star (productOperator c d R hR.cycleConditions)).comp
              (moduleCreationMap (CliffordOddSourceCycle.cycle d).representation x) := by
      ext y
      simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
        AdjointableMap.coe_add_apply, AdjointableMap.coe_neg_apply]
      abel
    rwa [heq] at h

theorem positivity (a : A × A) :
    IsPositiveModuloModuleCompact (gradedKasparovProductPositivityOperator
      (CliffordExternalEvenCycle.cycle c) (CliffordOddSourceCycle.cycle d)
      (productOperator c d R hR.cycleConditions) a) := by
  let Aop := interiorModuleTensorOperator d.representation c.operator
  let G := (cornerCycle c d R hR.cycleConditions).operator
  have hp := CliffordOddConditionalPauli.localized_positive (baseGrading c d)
    (representation c d) (representation_even c d) Aop G (firstOperator_odd c d) a
    (CliffordPairSecondTensor.extracted_positivity c d R hR a.1)
    (CliffordPairSecondTensor.extracted_positivity c d R hR a.2)
  have hrep : (distribution d).transport
      (gradedKasparovTensorRepresentation (CliffordExternalEvenCycle.cycle c)
        (CliffordOddSourceCycle.cycle d) a) =
      sumMap (CliffordExternalEvenRepresentation.halfRepresentation (representation c d)
        (baseGrading c d) (representation_even c d) a)
        (CliffordExternalEvenRepresentation.halfRepresentation (representation c d)
          (baseGrading c d) (representation_even c d) (cliffordCoefficientGrading.automorphism a)) := by
    ext z
    obtain ⟨w, rfl⟩ := (distribution d).surjective z
    rw [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply]
    exact distribution_representation c d a w
  have hfirst : (distribution d).transport (interiorModuleTensorOperator
      (CliffordOddSourceCycle.cycle d).representation (CliffordExternalEvenCycle.cycle c).operator) =
      sumMap Aop Aop := by
    ext z
    obtain ⟨w, rfl⟩ := (distribution d).surjective z
    rw [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply]
    exact distribution_firstOperator c d w
  let P := CliffordExternalEvenRepresentation.halfRepresentation (representation c d)
    (baseGrading c d) (representation_even c d) a
  let Q := CliffordExternalEvenRepresentation.halfRepresentation (representation c d)
    (baseGrading c d) (representation_even c d) (cliffordCoefficientGrading.automorphism a)
  let Y := CliffordOddConditionalConnection.candidate d.representation c.grading G
  change IsPositiveModuloModuleCompact
    (sumMap P Q * (sumMap Aop Aop * Y + Y * sumMap Aop Aop) * star (sumMap P Q)) at hp
  have heq : (distribution d).transport (gradedKasparovProductPositivityOperator
      (CliffordExternalEvenCycle.cycle c) (CliffordOddSourceCycle.cycle d)
      (productOperator c d R hR.cycleConditions) a) =
    sumMap P Q * (sumMap Aop Aop * Y + Y * sumMap Aop Aop) * star (sumMap P Q) := by
    simp only [gradedKasparovProductPositivityOperator, HilbertModuleEquiv.transport_mul,
      HilbertModuleEquiv.transport_add, HilbertModuleEquiv.transport_star,
      hrep, hfirst, distribution_productOperator, CliffordOddConditionalConnection.candidate,
      CliffordOddConditionalConnection.K, baseGrading, G, P, Q, Y]
  have h := hp.transport (distribution d).symm
  rw [← heq, HilbertModuleEquiv.transport_symm] at h
  exact h

theorem isProduct : IsGradedKasparovProductOperator (CliffordExternalEvenCycle.cycle c)
    (CliffordOddSourceCycle.cycle d) (productOperator c d R hR.cycleConditions) where
  cycleConditions := productConditions c d R hR.cycleConditions
  connection := connection c d R hR
  positivity := positivity c d R hR

end BC4lean.KKTheory.CliffordEvenOddSource
