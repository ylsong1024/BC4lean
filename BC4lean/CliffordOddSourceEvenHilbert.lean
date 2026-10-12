import BC4lean.CliffordOddEvenCornerCycle
import BC4lean.CliffordQuarterPhasePositivity
import BC4lean.GradedMatrixMoritaTensorDirectSumCycle
import BC4lean.GradedKasparovTensorCycleTransport

/-! # The whole signed-source tensor unitary for an odd and an even cycle

The actual tensor of a Hilbert sum is distributed using the completed
coefficient-form unitary. The quarter-phase unitary then matches the
canonical signed-source grading to swap(1⊗J). The original odd-by-even
product's genuine coefficient corner supplies the reference entire cycle.
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

local instance sourceSumComplete : CompleteSpace (HilbertModuleSum B H H) := hilbertModuleSum_complete
local instance targetSumComplete : CompleteSpace
    (HilbertModuleSum C (CliffordOddEvenCorner.Base (H := H) d) (CliffordOddEvenCorner.Base (H := H) d)) :=
  hilbertModuleSum_complete

abbrev Base := InteriorModuleTensor (E := H) d.representation
abbrev Source := InteriorModuleTensor (E := HilbertModuleSum B H H) d.representation
abbrev Target := HilbertModuleSum C (Base (H := H) d) (Base (H := H) d)

def baseGrading := tensorGrading (H := H) d.representation d.grading
  (CliffordExternalEvenCycle.representation_commutes_grading d)

def distribution : HilbertModuleEquiv C (Source (H := H) d) (Target (H := H) d) :=
  GradedMatrixMoritaTensorDirectSum.hilbertEquiv (E := H) (G := H) d.representation

def wholeEquiv : HilbertModuleEquiv C (Target (H := H) d) (Source (H := H) d) :=
  (sumEquiv (baseGrading (H := H) d)).trans (distribution (H := H) d).symm

@[simp] theorem wholeEquiv_apply (z : Target (H := H) d) :
    wholeEquiv (H := H) d z = (distribution (H := H) d).symm (sumEquiv (baseGrading (H := H) d) z) := rfl

@[simp] theorem wholeEquiv_symm_apply (z : Source (H := H) d) :
    (wholeEquiv (H := H) d).symm z = (sumEquiv (baseGrading (H := H) d)).symm (distribution (H := H) d z) := rfl

@[simp] theorem distribution_mk (x : HilbertModuleSum B H H) (y : F) :
    distribution (H := H) d (interiorModuleTensorMk d.representation x y) =
      sumMk (B := C) (interiorModuleTensorMk d.representation x.fst y)
        (interiorModuleTensorMk d.representation x.snd y) :=
  GradedMatrixMoritaTensorDirectSum.hilbertEquiv_mk _ x y

theorem distribution_grading (z : Source (H := H) d) :
    distribution (H := H) d ((gradedKasparovTensorGrading (CliffordOddSourceCycle.cycle c) d).grading z) =
      sumMk ((baseGrading (H := H) d).grading (distribution (H := H) d z).snd)
        ((baseGrading (H := H) d).grading (distribution (H := H) d z).fst) := by
  let L := (distribution (H := H) d).toAdjointable.toCLM
  let J := (gradedKasparovTensorGrading (CliffordOddSourceCycle.cycle c) d).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let S := sumSwap.toContinuousLinearEquiv.toContinuousLinearMap.comp (sumMap (baseGrading (H := H) d).toAdjointable (baseGrading (H := H) d).toAdjointable).toCLM
  have h : L.comp J = S.comp L := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    have hφ : ModuleTensorRepresentationGraded (δB := CStarGrading.trivial)
        d.representation d.grading := by
      intro b y
      exact d.representation_graded b y
    change distribution (H := H) d
        (((CliffordOddSourceCycle.grading (C := B) (H := H)).interiorTensor
          d.grading hφ).grading
          (interiorModuleTensorMk d.representation x y)) =
      sumSwap (sumMap (baseGrading (H := H) d).toAdjointable
        (baseGrading (H := H) d).toAdjointable
        (distribution (H := H) d (interiorModuleTensorMk d.representation x y)))
    have hx : (CliffordOddSourceCycle.grading (C := B) (H := H)).grading x =
        sumMk x.snd x.fst := rfl
    rw [GradedHilbertModule.interiorTensor_grading_mk _ _ hφ, hx,
      distribution_mk, distribution_mk]
    simp only [sumMk_fst, sumMk_snd, sumMap_apply, sumSwap_apply,
      GradedHilbertModule.toAdjointable_apply, baseGrading, tensorGrading_mk]
  have hz := DFunLike.congr_fun h z
  change distribution (H := H) d
      ((gradedKasparovTensorGrading (CliffordOddSourceCycle.cycle c) d).grading z) =
    sumSwap (sumMap (baseGrading (H := H) d).toAdjointable
      (baseGrading (H := H) d).toAdjointable (distribution (H := H) d z)) at hz
  simpa only [sumSwap_apply, sumMap_apply, GradedHilbertModule.toAdjointable_apply,
    sumMk_fst, sumMk_snd] using hz

theorem distribution_representation (a : A × A) (z : Source (H := H) d) :
    distribution (H := H) d (gradedKasparovTensorRepresentation (CliffordOddSourceCycle.cycle c) d a z) =
      sumMap (interiorModuleTensorOperator d.representation (c.representation a.1))
        (interiorModuleTensorOperator d.representation (c.representation a.2)) (distribution (H := H) d z) :=
  GradedMatrixMoritaTensorDirectSum.hilbertEquiv_operator _ _ _ z

theorem distribution_firstOperator (z : Source (H := H) d) :
    distribution (H := H) d (interiorModuleTensorOperator d.representation
      (CliffordOddSourceCycle.cycle c).operator z) =
      CliffordOddSourceCycle.operator (interiorModuleTensorOperator d.representation c.operator)
        (distribution (H := H) d z) := by
  let L := (distribution (H := H) d).toAdjointable.toCLM
  have h : L.comp (interiorModuleTensorOperator d.representation
      (CliffordOddSourceCycle.cycle c).operator).toCLM =
      (CliffordOddSourceCycle.operator (interiorModuleTensorOperator d.representation c.operator)).toCLM.comp L := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    simp only [ContinuousLinearMap.comp_apply, L, HilbertModuleEquiv.toAdjointable_apply,
      interiorModuleTensorOperator_mk, distribution_mk, CliffordOddSourceCycle.cycle,
      CliffordOddSourceCycle.operator_apply, sumMk_fst, sumMk_snd, map_smul,
      LinearMap.smul_apply]
  exact DFunLike.congr_fun h z

theorem distribution_creator (x : HilbertModuleSum B H H) :
    (distribution (H := H) d).toAdjointable.comp (moduleCreationMap d.representation x) =
      column (moduleCreationMap d.representation x.fst) (moduleCreationMap d.representation x.snd) := by
  ext y
  simp only [AdjointableMap.comp_apply, HilbertModuleEquiv.toAdjointable_apply,
    column_apply]
  change distribution (H := H) d (interiorModuleTensorMk d.representation x y) =
    sumMk (interiorModuleTensorMk d.representation x.fst y)
      (interiorModuleTensorMk d.representation x.snd y)
  exact distribution_mk d x y

def baseAction := c.groupAction.interiorTensor d.groupAction
  (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)

theorem distribution_action (g : Γ) (z : Source (H := H) d) :
    distribution (H := H) d ((gradedKasparovTensorAction (CliffordOddSourceCycle.cycle c) d).action g z) =
      ((baseAction c d).sum (baseAction c d)).action g (distribution (H := H) d z) :=
  GradedMatrixMoritaTensorDirectSum.hilbertEquiv_action _ c.groupAction c.groupAction d.groupAction
    (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant) g z

theorem baseAction_preservesGrading : (baseAction c d).PreservesGrading (baseGrading (H := H) d) :=
  c.groupAction.interiorTensor_preservesGrading d.groupAction GradedHilbertModule.trivial d.grading
    (by intro g x; rfl) d.grading_preserved
    (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)
    d.representation_graded

theorem phase_action (g : Γ) (z : Target (H := H) d) :
    sumEquiv (baseGrading (H := H) d) (((baseAction c d).sum (baseAction c d)).action g z) =
      ((baseAction c d).sum (baseAction c d)).action g (sumEquiv (baseGrading (H := H) d) z) := by
  apply Prod.ext <;>
    simp only [sumEquiv_apply, EquivariantHilbertModule.sum_action_apply,
      sumMk_fst, sumMk_snd, upper, lower, map_add, map_sub, map_smul,
      plus_action _ _ (baseAction_preservesGrading c d),
      minus_action _ _ (baseAction_preservesGrading c d),
      AdjointableMap.coe_add_apply, AdjointableMap.coe_sub_apply, AdjointableMap.coe_smul_apply]

theorem baseGrading_firstOperator (T : AdjointableMap B H H) :
    (baseGrading (H := H) d).toAdjointable * interiorModuleTensorOperator d.representation T =
      interiorModuleTensorOperator d.representation T * (baseGrading (H := H) d).toAdjointable := by
  have h : (GradedHilbertModule.trivial : GradedHilbertModule CStarGrading.trivial H).IsEven
      GradedHilbertModule.trivial T := by intro x; rfl
  have ht := GradedHilbertModule.IsEven.interiorModuleTensorOperator d.grading d.representation_graded h
  ext z
  exact ht z

theorem baseGrading_creator (x : H) :
    (baseGrading (H := H) d).toAdjointable.comp (moduleCreationMap d.representation x) =
      (moduleCreationMap d.representation x).comp d.grading.toAdjointable := by
  ext y
  change (tensorGrading (H := H) d.representation d.grading
    (CliffordExternalEvenCycle.representation_commutes_grading d)).grading
      (interiorModuleTensorMk d.representation x y) =
    interiorModuleTensorMk d.representation x (d.grading.grading y)
  exact tensorGrading_mk d.representation d.grading
    (CliffordExternalEvenCycle.representation_commutes_grading d) x y

variable (R : AdjointableMap (C × C) (CliffordOddEvenCorner.Source (H := H) d) (CliffordOddEvenCorner.Source (H := H) d))
  (hR : GradedKasparovTensorOperatorConditions c.cliffordExpansion (CliffordExternalEvenCycle.cycle d) R)

abbrev cornerCycle := CliffordOddEvenCorner.cycle c d R hR

theorem whole_grading (z : Target (H := H) d) :
    wholeEquiv (H := H) d ((CliffordOddSourceCycle.cycle (cornerCycle c d R hR)).grading.grading z) =
      (gradedKasparovTensorGrading (CliffordOddSourceCycle.cycle c) d).grading (wholeEquiv (H := H) d z) := by
  apply (distribution (H := H) d).injective
  simp only [wholeEquiv, HilbertModuleEquiv.trans_apply, HilbertModuleEquiv.apply_symm_apply]
  rw [distribution_grading c d]
  simp only [HilbertModuleEquiv.apply_symm_apply]
  exact sumEquiv_grading (baseGrading (H := H) d) z

theorem whole_action (g : Γ) (z : Target (H := H) d) :
    wholeEquiv (H := H) d ((CliffordOddSourceCycle.cycle (cornerCycle c d R hR)).groupAction.action g z) =
      (gradedKasparovTensorAction (CliffordOddSourceCycle.cycle c) d).action g (wholeEquiv (H := H) d z) := by
  apply (distribution (H := H) d).injective
  rw [distribution_action c d]
  simp only [wholeEquiv, HilbertModuleEquiv.trans_apply, HilbertModuleEquiv.apply_symm_apply,
    CliffordOddSourceCycle.cycle, EquivariantHilbertModule.sum_action_apply,
    CliffordOddEvenCorner.cycle_action]
  exact phase_action c d g z

theorem whole_representation (a : A × A) (z : Target (H := H) d) :
    wholeEquiv (H := H) d ((CliffordOddSourceCycle.cycle (cornerCycle c d R hR)).representation a z) =
      gradedKasparovTensorRepresentation (CliffordOddSourceCycle.cycle c) d a (wholeEquiv (H := H) d z) := by
  apply (distribution (H := H) d).injective
  rw [distribution_representation c d]
  simp only [wholeEquiv, HilbertModuleEquiv.trans_apply, HilbertModuleEquiv.apply_symm_apply,
    CliffordOddSourceCycle.cycle, CliffordOddSourceCycle.representation,
    CliffordOddEvenCorner.cycle_representation]
  change sumEquiv (baseGrading (H := H) d)
      (sumMap (interiorModuleTensorOperator d.representation (c.representation a.1))
        (interiorModuleTensorOperator d.representation (c.representation a.2)) z) =
    sumMap (interiorModuleTensorOperator d.representation (c.representation a.1))
      (interiorModuleTensorOperator d.representation (c.representation a.2))
      (sumEquiv (baseGrading (H := H) d) z)
  have h := congrArg (fun T : AdjointableMap C (Target (H := H) d) (Target (H := H) d) => T (sumEquiv (baseGrading (H := H) d) z))
    (sumEquiv_transport_diagonal (baseGrading (H := H) d)
      (interiorModuleTensorOperator d.representation (c.representation a.1))
      (interiorModuleTensorOperator d.representation (c.representation a.2))
      (baseGrading_firstOperator d _) (baseGrading_firstOperator d _))
  simpa only [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply] using h

def productOperator : AdjointableMap C (Source (H := H) d) (Source (H := H) d) :=
  (wholeEquiv (H := H) d).transport (CliffordOddSourceCycle.cycle (cornerCycle c d R hR)).operator

theorem productConditions : GradedKasparovTensorOperatorConditions (CliffordOddSourceCycle.cycle c) d
    (productOperator c d R hR) :=
  transportedCycle_tensorConditions (CliffordOddSourceCycle.cycle c) d
    (CliffordOddSourceCycle.cycle (cornerCycle c d R hR)) (wholeEquiv (H := H) d)
    (whole_grading c d R hR) (whole_action c d R hR) (whole_representation c d R hR)

def cycleIso : GradedKasparovCycleIso (CliffordOddSourceCycle.cycle (cornerCycle c d R hR))
    (gradedKasparovTensorCycleOfConditions (CliffordOddSourceCycle.cycle c) d
      (productOperator c d R hR) (productConditions c d R hR)) :=
  transportedCycle_tensorIso (CliffordOddSourceCycle.cycle c) d
    (CliffordOddSourceCycle.cycle (cornerCycle c d R hR)) (wholeEquiv (H := H) d)
    (whole_grading c d R hR) (whole_action c d R hR) (whole_representation c d R hR)

@[simp] theorem distribution_productOperator :
    (distribution (H := H) d).transport (productOperator c d R hR) =
      phasedOperator (baseGrading (H := H) d) (cornerCycle c d R hR).operator := by
  ext z
  simp only [productOperator, phasedOperator, HilbertModuleEquiv.transport_apply,
    wholeEquiv_apply, wholeEquiv_symm_apply, HilbertModuleEquiv.apply_symm_apply,
    CliffordOddSourceCycle.cycle]

end BC4lean.KKTheory.CliffordOddSourceEven
