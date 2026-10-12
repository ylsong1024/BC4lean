import BC4lean.CliffordEvenOddCornerCycle
import BC4lean.CliffordOddConditionalPositivity
import BC4lean.GradedKasparovTensorCycleTransport
import BC4lean.CliffordExternalEvenBalancedCompatibility

/-! # The whole signed source comparison for even followed by odd

The genuine pair-to-sum balance and grading-controlled Pauli unitary carry
the signed cycle of the actual odd product corner to the canonical tensor
of the actual external even cycle and the original signed odd cycle.
Representation, grading and group action are intertwined on the complete
carrier, and actual cycle transport supplies all Fredholm conditions.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordEvenOddSource
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
  (d : OddKasparovCycle β γ F)

local instance secondSumComplete : CompleteSpace (HilbertModuleSum C F F) := hilbertModuleSum_complete

abbrev Base := InteriorModuleTensor (E := H) d.representation
abbrev Source := InteriorModuleTensor (E := CliffordPairModule B H)
  (CliffordOddSourceCycle.cycle d).representation
abbrev Target := HilbertModuleSum C (Base (H := H) d) (Base (H := H) d)
local instance targetSumComplete : CompleteSpace (Target (H := H) d) := hilbertModuleSum_complete

def baseGrading := CliffordPairSecondTensor.baseGrading d.representation c.grading

def distribution : HilbertModuleEquiv C (Source (H := H) d) (Target (H := H) d) :=
  CliffordOddBalancedTensor.hilbertEquiv (E := H) d.representation

def wholeEquiv : HilbertModuleEquiv C (Target (H := H) d) (Source (H := H) d) :=
  (CliffordOddConditionalPauli.hilbertEquiv (baseGrading c d)).trans (distribution (H := H) d).symm

@[simp] theorem wholeEquiv_apply (z : Target (H := H) d) :
    wholeEquiv c d z = (distribution (H := H) d).symm
      (CliffordOddConditionalPauli.hilbertEquiv (baseGrading c d) z) := rfl

@[simp] theorem wholeEquiv_symm_apply (z : Source (H := H) d) :
    (wholeEquiv c d).symm z = (CliffordOddConditionalPauli.hilbertEquiv (baseGrading c d)).symm
      (distribution (H := H) d z) := rfl

@[simp] theorem distribution_mk (x : CliffordPairModule B H) (y : HilbertModuleSum C F F) :
    distribution (H := H) d (interiorModuleTensorMk (CliffordOddSourceCycle.cycle d).representation x y) =
      sumMk (interiorModuleTensorMk d.representation x.1 y.fst)
        (interiorModuleTensorMk d.representation x.2 y.snd) :=
  CliffordOddBalancedTensor.hilbertEquiv_mk (E := H) d.representation x y

theorem baseGrading_firstOperator :
    (baseGrading c d).toAdjointable =
      interiorModuleTensorOperator d.representation c.grading.toAdjointable := by
  apply AdjointableMap.ext
  have h : (baseGrading c d).toAdjointable.toCLM =
      (interiorModuleTensorOperator d.representation c.grading.toAdjointable).toCLM := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change (baseGrading c d).grading (interiorModuleTensorMk d.representation x y) =
      interiorModuleTensorOperator d.representation c.grading.toAdjointable
        (interiorModuleTensorMk d.representation x y)
    rw [baseGrading, CliffordPairSecondTensor.baseGrading_mk, interiorModuleTensorOperator_mk]
    rfl
  exact fun z => DFunLike.congr_fun h z

def representation : A →⋆ₙₐ[ℂ] AdjointableMap C (Base (H := H) d) (Base (H := H) d) :=
  (interiorModuleTensorOperatorHom d.representation).toNonUnitalStarAlgHom.comp c.representation

theorem representation_even (a : A) :
    (baseGrading c d).toAdjointable * BC4lean.KKTheory.CliffordEvenOddSource.representation c d a =
      BC4lean.KKTheory.CliffordEvenOddSource.representation c d a * (baseGrading c d).toAdjointable := by
  have h : c.grading.IsEven c.grading (c.representation a) := c.representation_graded a
  have ht := GradedHilbertModule.IsEven.interiorModuleTensorOperator (φ := d.representation)
    (GradedHilbertModule.trivial (B := C) (E := F)) (fun _ _ => rfl) h
  ext z
  exact ht z

theorem firstOperator_odd : (baseGrading c d).IsOdd (baseGrading c d)
    (interiorModuleTensorOperator d.representation c.operator) :=
  GradedHilbertModule.IsOdd.interiorModuleTensorOperator
    (GradedHilbertModule.trivial (B := C) (E := F)) (fun _ _ => rfl) c.operator_odd

theorem tensor_half (a : A × A) :
    interiorModuleTensorOperator d.representation (CliffordExternalEvenCycle.half c a) =
      halfRepresentation (BC4lean.KKTheory.CliffordEvenOddSource.representation c d) (baseGrading c d) (representation_even c d) a := by
  simp only [CliffordExternalEvenCycle.half, halfRepresentation_eq,
    CliffordOne.plusProjection, CliffordOne.minusProjection,
    ← interiorModuleTensorOperatorHom_apply, map_add, map_sub, map_smul, map_mul,
    map_one, BC4lean.KKTheory.CliffordEvenOddSource.representation, NonUnitalStarAlgHom.comp_apply,
    StarAlgHom.toNonUnitalStarAlgHom, baseGrading_firstOperator]
  rfl

theorem distribution_grading (z : Source (H := H) d) :
    distribution (H := H) d ((gradedKasparovTensorGrading (CliffordExternalEvenCycle.cycle c)
      (CliffordOddSourceCycle.cycle d)).grading z) =
      sumMap (baseGrading c d).toAdjointable (baseGrading c d).toAdjointable
        (sumSwap (distribution (H := H) d z)) := by
  let W := (distribution (H := H) d).toAdjointable.toCLM
  let L := (gradedKasparovTensorGrading (CliffordExternalEvenCycle.cycle c)
    (CliffordOddSourceCycle.cycle d)).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let K := (sumMap (baseGrading c d).toAdjointable (baseGrading c d).toAdjointable).toCLM.comp
    sumSwap.toContinuousLinearEquiv.toContinuousLinearMap
  have h : W.comp L = K.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    have hφ : ModuleTensorRepresentationGraded (δB := cliffordCoefficientGrading)
        (CliffordOddSourceCycle.representation d.representation)
        (CliffordOddSourceCycle.grading (C := C) (H := F)) := by
      intro b v
      exact (CliffordOddSourceCycle.cycle d).representation_graded b v
    change CliffordOddBalancedTensor.hilbertEquiv (E := H) d.representation
        (((cliffordExternalEvenGrading c.grading).interiorTensor
          (φ := CliffordOddSourceCycle.representation d.representation)
          (CliffordOddSourceCycle.grading (C := C) (H := F)) hφ).grading
          (interiorModuleTensorMk (CliffordOddSourceCycle.representation d.representation) x y)) =
      sumMap (baseGrading c d).toAdjointable (baseGrading c d).toAdjointable
        (sumSwap (CliffordOddBalancedTensor.hilbertEquiv (E := H) d.representation
          (interiorModuleTensorMk (CliffordOddSourceCycle.representation d.representation) x y)))
    rw [GradedHilbertModule.interiorTensor_grading_mk,
      CliffordOddBalancedTensor.hilbertEquiv_mk, CliffordOddBalancedTensor.hilbertEquiv_mk]
    change sumMk (interiorModuleTensorMk d.representation (c.grading.grading x.2) y.snd)
        (interiorModuleTensorMk d.representation (c.grading.grading x.1) y.fst) =
      sumMap (baseGrading c d).toAdjointable (baseGrading c d).toAdjointable
        (sumSwap (sumMk (interiorModuleTensorMk d.representation x.1 y.fst)
          (interiorModuleTensorMk d.representation x.2 y.snd)))
    simp only [sumSwap_apply, sumMap_apply, sumMk_fst, sumMk_snd, baseGrading,
      GradedHilbertModule.toAdjointable_apply, CliffordPairSecondTensor.baseGrading_mk]
  exact DFunLike.congr_fun h z

theorem distribution_representation (a : A × A) (z : Source (H := H) d) :
    distribution (H := H) d (gradedKasparovTensorRepresentation (CliffordExternalEvenCycle.cycle c)
      (CliffordOddSourceCycle.cycle d) a z) =
      sumMap (halfRepresentation (BC4lean.KKTheory.CliffordEvenOddSource.representation c d) (baseGrading c d) (representation_even c d) a)
        (halfRepresentation (BC4lean.KKTheory.CliffordEvenOddSource.representation c d) (baseGrading c d) (representation_even c d)
          (cliffordCoefficientGrading.automorphism a)) (distribution (H := H) d z) := by
  have h := CliffordOddBalancedTensor.hilbertEquiv_firstFactor d.representation
    (CliffordExternalEvenCycle.half c a)
    (CliffordExternalEvenCycle.half c (cliffordCoefficientGrading.automorphism a)) z
  change CliffordOddBalancedTensor.hilbertEquiv (E := H) d.representation
      (interiorModuleTensorOperator (CliffordOddSourceCycle.representation d.representation)
        (cliffordPairMap (CliffordExternalEvenCycle.half c a)
          (CliffordExternalEvenCycle.half c (cliffordCoefficientGrading.automorphism a))) z) =
    sumMap
      (halfRepresentation (BC4lean.KKTheory.CliffordEvenOddSource.representation c d)
        (baseGrading c d) (representation_even c d) a)
      (halfRepresentation (BC4lean.KKTheory.CliffordEvenOddSource.representation c d)
        (baseGrading c d) (representation_even c d) (cliffordCoefficientGrading.automorphism a))
      (CliffordOddBalancedTensor.hilbertEquiv (E := H) d.representation z)
  simpa only [tensor_half] using h

theorem distribution_firstOperator (z : Source (H := H) d) :
    distribution (H := H) d (interiorModuleTensorOperator (CliffordOddSourceCycle.cycle d).representation
      (CliffordExternalEvenCycle.cycle c).operator z) =
      sumMap (interiorModuleTensorOperator d.representation c.operator)
        (interiorModuleTensorOperator d.representation c.operator) (distribution (H := H) d z) :=
  CliffordOddBalancedTensor.hilbertEquiv_firstFactor _ _ _ z

def baseAction := c.groupAction.interiorTensor d.groupAction
  (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)

theorem distribution_action (g : Γ) (z : Source (H := H) d) :
    distribution (H := H) d ((gradedKasparovTensorAction (CliffordExternalEvenCycle.cycle c)
      (CliffordOddSourceCycle.cycle d)).action g z) =
      ((baseAction c d).sum (baseAction c d)).action g (distribution (H := H) d z) := by
  let W := (distribution (H := H) d).toAdjointable.toCLM
  let L := (gradedKasparovTensorAction (CliffordExternalEvenCycle.cycle c)
    (CliffordOddSourceCycle.cycle d)).action g
  let K := ((baseAction c d).sum (baseAction c d)).action g
  have h : W.comp L.toContinuousLinearEquiv.toContinuousLinearMap =
      K.toContinuousLinearEquiv.toContinuousLinearMap.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    have hφ : ModuleTensorRepresentationEquivariant
        (CliffordOddSourceCycle.representation d.representation) (cliffordCoefficientAction β)
        (d.groupAction.sum d.groupAction) :=
      (CliffordOddSourceCycle.cycle d).groupAction.representationEquivariant_of_conjugate
        (CliffordOddSourceCycle.cycle d).representation_equivariant
    change CliffordOddBalancedTensor.hilbertEquiv (E := H) d.representation
        (((cliffordPairAction c.groupAction).interiorTensor
          (φ := CliffordOddSourceCycle.representation d.representation)
          (d.groupAction.sum d.groupAction) hφ).action g
          (interiorModuleTensorMk (CliffordOddSourceCycle.representation d.representation) x y)) =
      ((baseAction c d).sum (baseAction c d)).action g
        (CliffordOddBalancedTensor.hilbertEquiv (E := H) d.representation
          (interiorModuleTensorMk (CliffordOddSourceCycle.representation d.representation) x y))
    rw [EquivariantHilbertModule.interiorTensor_action_mk,
      CliffordOddBalancedTensor.hilbertEquiv_mk, CliffordOddBalancedTensor.hilbertEquiv_mk]
    have hbase : ModuleTensorRepresentationEquivariant d.representation β d.groupAction :=
      d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant
    change sumMk
        (interiorModuleTensorMk d.representation (c.groupAction.action g x.1)
          (d.groupAction.action g y.fst))
        (interiorModuleTensorMk d.representation (c.groupAction.action g x.2)
          (d.groupAction.action g y.snd)) =
      sumMk ((c.groupAction.interiorTensor d.groupAction hbase).action g
          (interiorModuleTensorMk d.representation x.1 y.fst))
        ((c.groupAction.interiorTensor d.groupAction hbase).action g
          (interiorModuleTensorMk d.representation x.2 y.snd))
    rw [EquivariantHilbertModule.interiorTensor_action_mk,
      EquivariantHilbertModule.interiorTensor_action_mk]
  exact DFunLike.congr_fun h z

theorem baseAction_preservesGrading : (baseAction c d).PreservesGrading (baseGrading c d) :=
  c.groupAction.interiorTensor_preservesGrading d.groupAction c.grading GradedHilbertModule.trivial
    c.grading_preserved (fun _ _ => rfl)
    (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)
    (fun _ _ => rfl)

theorem pauli_action (g : Γ) (z : Target (H := H) d) :
    CliffordOddConditionalPauli.operator (baseGrading c d)
      (((baseAction c d).sum (baseAction c d)).action g z) =
    ((baseAction c d).sum (baseAction c d)).action g
      (CliffordOddConditionalPauli.operator (baseGrading c d) z) := by
  apply Prod.ext <;>
    simp only [CliffordOddConditionalPauli.operator_apply,
      EquivariantHilbertModule.sum_action_apply, sumMk_fst, sumMk_snd, map_add, map_smul,
      plus_action _ _ (baseAction_preservesGrading c d),
      minus_action _ _ (baseAction_preservesGrading c d)]

variable (R : AdjointableMap (C × C) (CliffordEvenOddCorner.Source (H := H) d) (CliffordEvenOddCorner.Source (H := H) d))
  (hR : GradedKasparovTensorOperatorConditions c d.cliffordExpansion R)

abbrev cornerCycle := CliffordEvenOddCorner.cycle c d R hR

theorem whole_grading (z : Target (H := H) d) :
    wholeEquiv c d ((CliffordOddSourceCycle.cycle (cornerCycle c d R hR)).grading.grading z) =
      (gradedKasparovTensorGrading (CliffordExternalEvenCycle.cycle c)
        (CliffordOddSourceCycle.cycle d)).grading (wholeEquiv c d z) := by
  apply (distribution (H := H) d).injective
  rw [distribution_grading c d]
  simp only [wholeEquiv, HilbertModuleEquiv.trans_apply, HilbertModuleEquiv.apply_symm_apply,
    CliffordOddConditionalPauli.hilbertEquiv_apply, CliffordOddSourceCycle.cycle]
  exact CliffordOddConditionalPauli.operator_swap (baseGrading c d) z

theorem whole_action (g : Γ) (z : Target (H := H) d) :
    wholeEquiv c d ((CliffordOddSourceCycle.cycle (cornerCycle c d R hR)).groupAction.action g z) =
      (gradedKasparovTensorAction (CliffordExternalEvenCycle.cycle c)
        (CliffordOddSourceCycle.cycle d)).action g (wholeEquiv c d z) := by
  apply (distribution (H := H) d).injective
  rw [distribution_action c d]
  simp only [wholeEquiv, HilbertModuleEquiv.trans_apply, HilbertModuleEquiv.apply_symm_apply,
    CliffordOddConditionalPauli.hilbertEquiv_apply, CliffordOddSourceCycle.cycle,
    EquivariantHilbertModule.sum_action_apply, CliffordEvenOddCorner.cycle_action]
  exact pauli_action c d g z

theorem whole_representation (a : A × A) (z : Target (H := H) d) :
    wholeEquiv c d ((CliffordOddSourceCycle.cycle (cornerCycle c d R hR)).representation a z) =
      gradedKasparovTensorRepresentation (CliffordExternalEvenCycle.cycle c)
        (CliffordOddSourceCycle.cycle d) a (wholeEquiv c d z) := by
  apply (distribution (H := H) d).injective
  rw [distribution_representation c d]
  simp only [wholeEquiv, HilbertModuleEquiv.trans_apply, HilbertModuleEquiv.apply_symm_apply,
    CliffordOddConditionalPauli.hilbertEquiv_apply, CliffordOddSourceCycle.cycle,
    CliffordOddSourceCycle.representation, CliffordEvenOddCorner.cycle_representation]
  exact CliffordOddConditionalPauli.operator_representation (baseGrading c d)
    (BC4lean.KKTheory.CliffordEvenOddSource.representation c d) (representation_even c d) a z

def productOperator : AdjointableMap C (Source (H := H) d) (Source (H := H) d) :=
  (wholeEquiv c d).transport (CliffordOddSourceCycle.cycle (cornerCycle c d R hR)).operator

theorem productConditions : GradedKasparovTensorOperatorConditions
    (CliffordExternalEvenCycle.cycle c) (CliffordOddSourceCycle.cycle d)
    (productOperator c d R hR) :=
  transportedCycle_tensorConditions (CliffordExternalEvenCycle.cycle c) (CliffordOddSourceCycle.cycle d)
    (CliffordOddSourceCycle.cycle (cornerCycle c d R hR)) (wholeEquiv c d)
    (whole_grading c d R hR) (whole_action c d R hR) (whole_representation c d R hR)

def cycleIso : GradedKasparovCycleIso (CliffordOddSourceCycle.cycle (cornerCycle c d R hR))
    (gradedKasparovTensorCycleOfConditions (CliffordExternalEvenCycle.cycle c)
      (CliffordOddSourceCycle.cycle d) (productOperator c d R hR) (productConditions c d R hR)) :=
  transportedCycle_tensorIso (CliffordExternalEvenCycle.cycle c) (CliffordOddSourceCycle.cycle d)
    (CliffordOddSourceCycle.cycle (cornerCycle c d R hR)) (wholeEquiv c d)
    (whole_grading c d R hR) (whole_action c d R hR) (whole_representation c d R hR)

@[simp] theorem distribution_productOperator :
    (distribution (H := H) d).transport (productOperator c d R hR) =
      CliffordOddConditionalConnection.candidate d.representation c.grading (cornerCycle c d R hR).operator := by
  ext z
  simp only [productOperator, CliffordOddConditionalConnection.candidate,
    HilbertModuleEquiv.transport_apply, wholeEquiv_apply, wholeEquiv_symm_apply,
    HilbertModuleEquiv.apply_symm_apply,
    CliffordOddSourceCycle.cycle, baseGrading]

end BC4lean.KKTheory.CliffordEvenOddSource
