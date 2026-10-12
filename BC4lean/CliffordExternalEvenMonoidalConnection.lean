import BC4lean.CliffordExternalEvenMonoidalHilbert
import BC4lean.GradedConnectionDefectAlgebra

/-! # All four genuine connections under external even Clifford extension

The arbitrary-vector signed defect is a pair of sums of original signed
defects composed with the actual grading projections. Oddness of the
second operator exchanges those projections. The whole balanced unitary
then transfers the compact errors back to the completed source tensor.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordExternalEvenMonoidal
open CliffordExternalEvenRepresentation CliffordExternalEvenBalancedTensor

variable {Γ A B C H F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace H] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C}
  (c : GradedKasparovCycle α β CStarGrading.trivial CStarGrading.trivial H)
  (d : GradedKasparovCycle β γ CStarGrading.trivial CStarGrading.trivial F)

variable
  (R : AdjointableMap C (InteriorModuleTensor (E := H) d.representation)
    (InteriorModuleTensor (E := H) d.representation))
  (S : AdjointableMap C F F) (hS : d.grading.IsOdd d.grading S)

include hS in
theorem plus_odd_apply (y : F) : plus d.grading (S y) = S (minus d.grading y) := by
  let _retainedOriginalOrder : PartialOrder B := inferInstance
  let _retainedOriginalStarOrder : StarOrderedRing B := inferInstance
  exact congrArg (fun T : AdjointableMap C F F => T y) (odd_mul_minus d.grading S hS).symm

include hS in
theorem minus_odd_apply (y : F) : minus d.grading (S y) = S (plus d.grading y) := by
  let _retainedOriginalOrder : PartialOrder B := inferInstance
  let _retainedOriginalStarOrder : StarOrderedRing B := inferInstance
  exact congrArg (fun T : AdjointableMap C F F => T y) (odd_mul_plus d.grading S hS).symm

def signedCreationDefect (x : H) :
    AdjointableMap C F (InteriorModuleTensor (E := H) d.representation) :=
  R.comp (moduleCreationMap d.representation x) -
    (moduleCreationMap d.representation (c.grading.grading x)).comp S

include hS in
/-- No homogeneity is required for this exact whole creator equality. -/
theorem coordinate_creation_defect (x : CliffordPairModule B H) :
    (cliffordPairMap R R).comp (coordinateCreation d.representation d.grading x) -
      (coordinateCreation d.representation d.grading
        ((CliffordExternalEvenCycle.cycle c).grading.grading x)).comp (cliffordPairMap S S) =
    cliffordPairMap
      ((signedCreationDefect c d R S x.1).comp (plus d.grading) +
        (signedCreationDefect c d R S x.2).comp (minus d.grading))
      ((signedCreationDefect c d R S x.1).comp (minus d.grading) +
        (signedCreationDefect c d R S x.2).comp (plus d.grading)) := by
  ext y
  simp only [coordinateCreation, signedCreationDefect, AdjointableMap.comp_apply,
    AdjointableMap.coe_sub_apply, AdjointableMap.coe_add_apply, cliffordPairMap_apply, cliffordPairMk]
  apply Prod.ext
  · change R (moduleCreationMap d.representation x.1 (plus d.grading y.1) +
        moduleCreationMap d.representation x.2 (minus d.grading y.1)) -
      (moduleCreationMap d.representation (c.grading.grading x.2) (plus d.grading (S y.1)) +
        moduleCreationMap d.representation (c.grading.grading x.1) (minus d.grading (S y.1))) =
      (R (moduleCreationMap d.representation x.1 (plus d.grading y.1)) -
        moduleCreationMap d.representation (c.grading.grading x.1) (S (plus d.grading y.1))) +
      (R (moduleCreationMap d.representation x.2 (minus d.grading y.1)) -
        moduleCreationMap d.representation (c.grading.grading x.2) (S (minus d.grading y.1)))
    rw [plus_odd_apply d S hS, minus_odd_apply d S hS, R.toCLM.map_add]
    abel
  · change R (moduleCreationMap d.representation x.1 (minus d.grading y.2) +
        moduleCreationMap d.representation x.2 (plus d.grading y.2)) -
      (moduleCreationMap d.representation (c.grading.grading x.2) (minus d.grading (S y.2)) +
        moduleCreationMap d.representation (c.grading.grading x.1) (plus d.grading (S y.2))) =
      (R (moduleCreationMap d.representation x.1 (minus d.grading y.2)) -
        moduleCreationMap d.representation (c.grading.grading x.1) (S (minus d.grading y.2))) +
      (R (moduleCreationMap d.representation x.2 (plus d.grading y.2)) -
        moduleCreationMap d.representation (c.grading.grading x.2) (S (plus d.grading y.2)))
    rw [minus_odd_apply d S hS, plus_odd_apply d S hS, R.toCLM.map_add]
    abel

theorem source_creation_defect (x : CliffordPairModule B H) :
    (productOperator d R).comp (moduleCreationMap (CliffordExternalEvenCycle.cycle d).representation x) -
      (moduleCreationMap (CliffordExternalEvenCycle.cycle d).representation
        ((CliffordExternalEvenCycle.cycle c).grading.grading x)).comp (cliffordPairMap S S) =
    (hilbertEquiv (H := H) d).symm.toAdjointable.comp
      ((cliffordPairMap R R).comp (coordinateCreation d.representation d.grading x) -
        (coordinateCreation d.representation d.grading
          ((CliffordExternalEvenCycle.cycle c).grading.grading x)).comp (cliffordPairMap S S)) := by
  let U := hilbertEquiv (H := H) d
  have hcreation (u : CliffordPairModule B H) (v : CliffordPairModule C F) :
      U (moduleCreationMap (CliffordExternalEvenCycle.cycle d).representation u v) =
        coordinateCreation d.representation d.grading u v := by
    change (CliffordExternalEvenBalancedTensor.hilbertEquiv (H := H) d.representation d.grading
      (CliffordExternalEvenCycle.representation_commutes_grading d))
        (moduleCreationMap (CliffordExternalEvenRepresentation.representation d.representation d.grading
          (CliffordExternalEvenCycle.representation_commutes_grading d)) u v) =
      coordinateCreation d.representation d.grading u v
    exact CliffordExternalEvenBalancedTensor.creation_apply d.representation d.grading
      (CliffordExternalEvenCycle.representation_commutes_grading d) u v
  have hinv (z : Target (H := H) d) : U (U.symm z) = z := U.apply_symm_apply z
  have hproduct (z : Source (H := H) d) :
      U (productOperator d R z) = cliffordPairMap R R (U z) := by
    change U (U.symm (cliffordPairMap R R (U.symm.symm z))) = cliffordPairMap R R (U z)
    rw [HilbertModuleEquiv.symm_symm, hinv]
  ext y
  simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
    HilbertModuleEquiv.toAdjointable_apply]
  apply U.injective
  change U (productOperator d R
      (moduleCreationMap (CliffordExternalEvenCycle.cycle d).representation x y) -
    moduleCreationMap (CliffordExternalEvenCycle.cycle d).representation
      ((CliffordExternalEvenCycle.cycle c).grading.grading x) (cliffordPairMap S S y)) =
    U (U.symm (cliffordPairMap R R (coordinateCreation d.representation d.grading x y) -
      coordinateCreation d.representation d.grading
        ((CliffordExternalEvenCycle.cycle c).grading.grading x) (cliffordPairMap S S y)))
  rw [HilbertModuleEquiv.map_sub, hproduct, hcreation, hcreation, hinv]

include hS in
theorem compact_source_creation_defect
    (h : ∀ x : H, IsModuleCompact (signedCreationDefect c d R S x))
    (x : CliffordPairModule B H) :
    IsModuleCompact ((productOperator d R).comp
      (moduleCreationMap (CliffordExternalEvenCycle.cycle d).representation x) -
        (moduleCreationMap (CliffordExternalEvenCycle.cycle d).representation
          ((CliffordExternalEvenCycle.cycle c).grading.grading x)).comp (cliffordPairMap S S)) := by
  rw [source_creation_defect, coordinate_creation_defect c d R S hS]
  have hpair := (((h x.1).comp_right (plus d.grading)).add
    ((h x.2).comp_right (minus d.grading))).cliffordPairMap
      (((h x.1).comp_right (minus d.grading)).add
        ((h x.2).comp_right (plus d.grading)))
  exact hpair.comp_left _

theorem productOperator_star : star (productOperator d R) = productOperator d (star R) := by
  simp only [productOperator, ← HilbertModuleEquiv.transport_star, cliffordPairMap_star]

theorem productConnection (hR : GradedKasparovConnection c d R) :
    GradedKasparovConnection (CliffordExternalEvenCycle.cycle c)
      (CliffordExternalEvenCycle.cycle d) (productOperator d R) where
  even x hx := by
    have hD : (CliffordExternalEvenCycle.cycle d).operator = cliffordPairMap d.operator d.operator := rfl
    rw [hD]
    have h := compact_source_creation_defect c d R d.operator d.operator_odd
      (fun z => hR.creation_defect z) x
    rw [hx] at h
    simpa only [neg_sub] using h.neg
  even_adjoint x hx := by
    have hD : (CliffordExternalEvenCycle.cycle d).operator = cliffordPairMap d.operator d.operator := rfl
    rw [hD]
    have h := compact_source_creation_defect c d (star R) (star d.operator)
      d.operator_odd.adjoint (fun z => hR.creation_adjoint_defect z) x
    rw [hx] at h
    simpa only [neg_sub, ← productOperator_star, cliffordPairMap_star] using h.neg
  odd x hx := by
    have h := compact_source_creation_defect c d R d.operator d.operator_odd
      (fun z => hR.creation_defect z) x
    rw [hx, moduleCreationMap_neg] at h
    have heq : (productOperator d R).comp
        (moduleCreationMap (CliffordExternalEvenCycle.cycle d).representation x) -
          (-moduleCreationMap (CliffordExternalEvenCycle.cycle d).representation x).comp
            (cliffordPairMap d.operator d.operator) =
        (moduleCreationMap (CliffordExternalEvenCycle.cycle d).representation x).comp
          (cliffordPairMap d.operator d.operator) +
            (productOperator d R).comp
              (moduleCreationMap (CliffordExternalEvenCycle.cycle d).representation x) := by
      ext y
      simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
        AdjointableMap.coe_add_apply, AdjointableMap.coe_neg_apply]
      abel
    rwa [heq] at h
  odd_adjoint x hx := by
    have hD : (CliffordExternalEvenCycle.cycle d).operator = cliffordPairMap d.operator d.operator := rfl
    rw [hD]
    have h := compact_source_creation_defect c d (star R) (star d.operator)
      d.operator_odd.adjoint (fun z => hR.creation_adjoint_defect z) x
    rw [hx, moduleCreationMap_neg] at h
    have heq : (productOperator d (star R)).comp
        (moduleCreationMap (CliffordExternalEvenCycle.cycle d).representation x) -
          (-moduleCreationMap (CliffordExternalEvenCycle.cycle d).representation x).comp
            (cliffordPairMap (star d.operator) (star d.operator)) =
        (moduleCreationMap (CliffordExternalEvenCycle.cycle d).representation x).comp
          (cliffordPairMap (star d.operator) (star d.operator)) +
            (productOperator d (star R)).comp
              (moduleCreationMap (CliffordExternalEvenCycle.cycle d).representation x) := by
      ext y
      simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
        AdjointableMap.coe_add_apply, AdjointableMap.coe_neg_apply]
      abel
    rw [heq] at h
    simpa only [← productOperator_star, cliffordPairMap_star] using h

end BC4lean.KKTheory.CliffordExternalEvenMonoidal
