import BC4lean.CliffordOddSourceEvenHilbert

/-! # The actual product criterion for signed odd source followed by even

All four homogeneous creator laws follow from the original product's
actual extracted ordinary errors and the exact quarter-phase column
formula. The original AK-localized positive lifts give both source
coordinates after phase conjugation and completed tensor transport.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordOddSourceEven
open CliffordExternalEvenBalancedTensor CliffordQuarterPhase

variable {Γ A B C H F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace H] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C}
  (c : OddKasparovCycle α β H)
  (d : GradedKasparovCycle β γ CStarGrading.trivial CStarGrading.trivial F)

local instance cliffordOddSourceEvenCriterionSourceSumComplete : CompleteSpace (HilbertModuleSum B H H) := hilbertModuleSum_complete
local instance cliffordOddSourceEvenCriterionTargetSumComplete : CompleteSpace (Target (H := H) d) := hilbertModuleSum_complete

theorem creator_error_compact
    (P : AdjointableMap C (Source d) (Source d)) (G : AdjointableMap C (Base d) (Base d))
    (D : AdjointableMap C F F)
    (hP : (distribution d).transport P = phasedOperator (baseGrading d) G)
    (hD : d.grading.IsOdd d.grading D)
    (hG : ∀ x : H, IsModuleCompact (G.comp (moduleCreationMap d.representation x) -
      (moduleCreationMap d.representation x).comp D))
    (x : HilbertModuleSum B H H) :
    IsModuleCompact ((moduleCreationMap d.representation (sumSwap x)).comp D -
      P.comp (moduleCreationMap d.representation x)) := by
  have h := (connection_compact (baseGrading d) d.grading G D hD
    (moduleCreationMap d.representation x.fst) (moduleCreationMap d.representation x.snd)
    (baseGrading_creator d x.fst) (baseGrading_creator d x.snd)
    (hG x.fst) (hG x.snd)).neg
  have hout := h.comp_left (distribution d).symm.toAdjointable
  convert hout using 1
  ext y
  apply (distribution d).injective
  have hPy := congrArg (fun Q : AdjointableMap C (Target d) (Target d) => Q
    (distribution d (moduleCreationMap d.representation x y))) hP
  simp only [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply] at hPy
  have hcreation (z : HilbertModuleSum B H H) (w : F) :
      distribution d (moduleCreationMap d.representation z w) =
        column (moduleCreationMap d.representation z.fst)
          (moduleCreationMap d.representation z.snd) w :=
    congrArg (fun T : AdjointableMap C F (Target (H := H) d) => T w)
      (distribution_creator d z)
  simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
    AdjointableMap.coe_neg_apply, HilbertModuleEquiv.toAdjointable_apply,
    HilbertModuleEquiv.apply_symm_apply, map_sub, map_neg]
  rw [hPy, hcreation, hcreation]
  simp only [sumSwap_apply, sumMk_fst, sumMk_snd, neg_sub]

variable (R : AdjointableMap (C × C) (CliffordOddEvenCorner.Source d) (CliffordOddEvenCorner.Source d))
  (hR : IsGradedKasparovProductOperator c.cliffordExpansion (CliffordExternalEvenCycle.cycle d) R)

theorem connection : GradedKasparovConnection (CliffordOddSourceCycle.cycle c) d
    (productOperator c d R hR.cycleConditions) where
  even x hx := by
    have h := creator_error_compact d (productOperator c d R hR.cycleConditions)
      (cornerCycle c d R hR.cycleConditions).operator d.operator
      (distribution_productOperator c d R hR.cycleConditions) d.operator_odd
      (fun x => by
        rw [CliffordOddEvenCorner.cycle_operator c d R hR.cycleConditions]
        change IsModuleCompact
          ((cliffordPairFirstCorner ((hilbertEquiv (H := H) d.representation d.grading
              (CliffordExternalEvenCycle.representation_commutes_grading d)).transport R)).comp
            (moduleCreationMap d.representation x) -
            (moduleCreationMap d.representation x).comp d.operator)
        simpa only [neg_sub] using (extracted_product_connection c d R hR x).neg) x
    change sumSwap x = x at hx
    simpa only [hx] using h
  even_adjoint x hx := by
    have hP : (distribution d).transport (star (productOperator c d R hR.cycleConditions)) =
        phasedOperator (baseGrading d) (star (cornerCycle c d R hR.cycleConditions).operator) := by
      rw [HilbertModuleEquiv.transport_star, distribution_productOperator, phasedOperator_star]
    have h := creator_error_compact d (star (productOperator c d R hR.cycleConditions))
      (star (cornerCycle c d R hR.cycleConditions).operator) (star d.operator) hP
      d.operator_odd.adjoint
      (fun x => by
        rw [CliffordOddEvenCorner.cycle_operator c d R hR.cycleConditions]
        change IsModuleCompact
          ((star (cliffordPairFirstCorner ((hilbertEquiv (H := H) d.representation d.grading
              (CliffordExternalEvenCycle.representation_commutes_grading d)).transport R))).comp
            (moduleCreationMap d.representation x) -
            (moduleCreationMap d.representation x).comp (star d.operator))
        simpa only [neg_sub] using (extracted_product_adjoint_connection c d R hR x).neg) x
    change sumSwap x = x at hx
    simpa only [hx] using h
  odd x hx := by
    have h := creator_error_compact d (productOperator c d R hR.cycleConditions)
      (cornerCycle c d R hR.cycleConditions).operator d.operator
      (distribution_productOperator c d R hR.cycleConditions) d.operator_odd
      (fun x => by
        rw [CliffordOddEvenCorner.cycle_operator c d R hR.cycleConditions]
        change IsModuleCompact
          ((cliffordPairFirstCorner ((hilbertEquiv (H := H) d.representation d.grading
              (CliffordExternalEvenCycle.representation_commutes_grading d)).transport R)).comp
            (moduleCreationMap d.representation x) -
            (moduleCreationMap d.representation x).comp d.operator)
        simpa only [neg_sub] using (extracted_product_connection c d R hR x).neg) x
    change sumSwap x = -x at hx
    rw [hx, moduleCreationMap_neg] at h
    convert h.neg using 1
    ext y
    simp only [AdjointableMap.comp_apply, AdjointableMap.coe_add_apply,
      AdjointableMap.coe_sub_apply, AdjointableMap.coe_neg_apply]
    abel
  odd_adjoint x hx := by
    have hP : (distribution d).transport (star (productOperator c d R hR.cycleConditions)) =
        phasedOperator (baseGrading d) (star (cornerCycle c d R hR.cycleConditions).operator) := by
      rw [HilbertModuleEquiv.transport_star, distribution_productOperator, phasedOperator_star]
    have h := creator_error_compact d (star (productOperator c d R hR.cycleConditions))
      (star (cornerCycle c d R hR.cycleConditions).operator) (star d.operator) hP
      d.operator_odd.adjoint
      (fun x => by
        rw [CliffordOddEvenCorner.cycle_operator c d R hR.cycleConditions]
        change IsModuleCompact
          ((star (cliffordPairFirstCorner ((hilbertEquiv (H := H) d.representation d.grading
              (CliffordExternalEvenCycle.representation_commutes_grading d)).transport R))).comp
            (moduleCreationMap d.representation x) -
            (moduleCreationMap d.representation x).comp (star d.operator))
        simpa only [neg_sub] using (extracted_product_adjoint_connection c d R hR x).neg) x
    change sumSwap x = -x at hx
    rw [hx, moduleCreationMap_neg] at h
    convert h.neg using 1
    ext y
    simp only [AdjointableMap.comp_apply, AdjointableMap.coe_add_apply,
      AdjointableMap.coe_sub_apply, AdjointableMap.coe_neg_apply]
    abel

theorem positivity (a : A × A) :
    IsPositiveModuloModuleCompact (gradedKasparovProductPositivityOperator
      (CliffordOddSourceCycle.cycle c) d (productOperator c d R hR.cycleConditions) a) := by
  let Aop := interiorModuleTensorOperator d.representation c.operator
  let G := (cornerCycle c d R hR.cycleConditions).operator
  let P := interiorModuleTensorOperator d.representation (c.representation a.1)
  let Q := interiorModuleTensorOperator d.representation (c.representation a.2)
  have hpositive := localized_positive (baseGrading d) Aop G P Q
    (baseGrading_firstOperator d c.operator)
    (baseGrading_firstOperator d (c.representation a.1))
    (baseGrading_firstOperator d (c.representation a.2))
    (extracted_product_positivity c d R hR a.1) (extracted_product_positivity c d R hR a.2)
  have hrep : (distribution d).transport
      (gradedKasparovTensorRepresentation (CliffordOddSourceCycle.cycle c) d a) = sumMap P Q := by
    ext z
    obtain ⟨w, rfl⟩ := (distribution d).surjective z
    rw [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply]
    exact distribution_representation c d a w
  have hfirst : (distribution d).transport
      (interiorModuleTensorOperator d.representation (CliffordOddSourceCycle.cycle c).operator) =
      CliffordOddSourceCycle.operator Aop := by
    ext z
    obtain ⟨w, rfl⟩ := (distribution d).surjective z
    rw [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply]
    exact distribution_firstOperator c d w
  have htransport : (distribution d).transport
      (gradedKasparovProductPositivityOperator (CliffordOddSourceCycle.cycle c) d
        (productOperator c d R hR.cycleConditions) a) =
      sumMap P Q * (CliffordOddSourceCycle.operator Aop * phasedOperator (baseGrading d) G +
        phasedOperator (baseGrading d) G * CliffordOddSourceCycle.operator Aop) * star (sumMap P Q) := by
    simp only [gradedKasparovProductPositivityOperator, HilbertModuleEquiv.transport_mul,
      HilbertModuleEquiv.transport_add, HilbertModuleEquiv.transport_star,
      hrep, hfirst, distribution_productOperator, G]
  have h := hpositive.transport (distribution d).symm
  rw [← htransport, HilbertModuleEquiv.transport_symm] at h
  exact h

theorem isProduct : IsGradedKasparovProductOperator (CliffordOddSourceCycle.cycle c) d
    (productOperator c d R hR.cycleConditions) where
  cycleConditions := productConditions c d R hR.cycleConditions
  connection := connection c d R hR
  positivity := positivity c d R hR

end BC4lean.KKTheory.CliffordOddSourceEven
