import BC4lean.CliffordOddBalancedTensorPositivity
import BC4lean.GradedKasparovCycleTransport
import BC4lean.CliffordOddOddFourierCompatibility

/-! # The entire genuine coordinate odd-by-odd product cycle

The original arbitrary chosen graded product is transported through the
true matching-coordinate balanced unitary. Its swap grading, source
representation and diagonal tensor action are computed on the whole
completed module. Its original product operator and positive lifts remain
those of the actual raw product.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordOddOddCoordinate

variable {Γ A B C H F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace H] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C}
  (c : OddKasparovCycle α β H) (d : OddKasparovCycle β γ F)

abbrev Base := InteriorModuleTensor (E := H) d.representation
abbrev Sum := HilbertModuleSum C (Base (H := H) d) (Base (H := H) d)
abbrev Source := CliffordOddBalancedTensor.Source (E := H) d.representation

local instance cliffordOddOddCoordinateCycleLocalInstance1 : CompleteSpace (HilbertModuleSum C F F) := hilbertModuleSum_complete
local instance cliffordOddOddCoordinateCycleLocalInstance2 : CompleteSpace (Sum (H := H) d) := hilbertModuleSum_complete

def balancedEquiv : HilbertModuleEquiv C (Source (H := H) d) (Sum (H := H) d) :=
  CliffordOddBalancedTensor.hilbertEquiv d.representation

def baseAction := c.groupAction.interiorTensor d.groupAction
  (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)

def baseRepresentation := (interiorModuleTensorOperatorHom d.representation).toNonUnitalStarAlgHom.comp c.representation

theorem balancedEquiv_action (g : Γ) (z : Source (H := H) d) :
    balancedEquiv d ((gradedKasparovTensorAction c.cliffordExpansion (CliffordOddSourceCycle.cycle d)).action g z) =
      ((baseAction c d).sum (baseAction c d)).action g (balancedEquiv d z) := by
  have hactPair : ModuleTensorRepresentationEquivariant
      (CliffordOddSourceCycle.representation d.representation)
      (cliffordCoefficientAction β) (d.groupAction.sum d.groupAction) :=
    (CliffordOddSourceCycle.cycle d).groupAction.representationEquivariant_of_conjugate
      (CliffordOddSourceCycle.cycle d).representation_equivariant
  let W := (balancedEquiv (H := H) d).toAdjointable.toCLM
  let U := (gradedKasparovTensorAction c.cliffordExpansion (CliffordOddSourceCycle.cycle d)).action g
  let V := ((baseAction c d).sum (baseAction c d)).action g
  have h : W.comp U.toContinuousLinearEquiv.toContinuousLinearMap =
      V.toContinuousLinearEquiv.toContinuousLinearMap.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change CliffordOddBalancedTensor.hilbertEquiv d.representation
        ((((cliffordPairAction c.groupAction).interiorTensor
          (d.groupAction.sum d.groupAction) hactPair).action g)
          (interiorModuleTensorMk (CliffordOddSourceCycle.representation d.representation) x y)) =
      ((baseAction c d).sum (baseAction c d)).action g
        (CliffordOddBalancedTensor.hilbertEquiv d.representation
          (interiorModuleTensorMk (CliffordOddSourceCycle.representation d.representation) x y))
    rw [EquivariantHilbertModule.interiorTensor_action_mk,
      CliffordOddBalancedTensor.hilbertEquiv_mk, CliffordOddBalancedTensor.hilbertEquiv_mk]
    apply Prod.ext
    · change interiorModuleTensorMk d.representation (c.groupAction.action g x.1)
          (d.groupAction.action g y.fst) =
        (baseAction c d).action g (interiorModuleTensorMk d.representation x.1 y.fst)
      exact (EquivariantHilbertModule.interiorTensor_action_mk c.groupAction d.groupAction
        (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)
        g x.1 y.fst).symm
    · change interiorModuleTensorMk d.representation (c.groupAction.action g x.2)
          (d.groupAction.action g y.snd) =
        (baseAction c d).action g (interiorModuleTensorMk d.representation x.2 y.snd)
      exact (EquivariantHilbertModule.interiorTensor_action_mk c.groupAction d.groupAction
        (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)
        g x.2 y.snd).symm
  exact DFunLike.congr_fun h z

variable (R : AdjointableMap C (Source (H := H) d) (Source (H := H) d))
  (hR : GradedKasparovTensorOperatorConditions c.cliffordExpansion (CliffordOddSourceCycle.cycle d) R)

def rawCycle := gradedKasparovTensorCycleOfConditions c.cliffordExpansion (CliffordOddSourceCycle.cycle d) R hR

def cycle : GradedKasparovCycle α γ CStarGrading.trivial CStarGrading.trivial (Sum (H := H) d) :=
  (rawCycle c d R hR).transport (balancedEquiv d)

@[simp] theorem cycle_operator :
    (cycle c d R hR).operator = CliffordOddBalancedTensor.coordinateOperator d.representation R := rfl

@[simp] theorem cycle_grading (z : Sum (H := H) d) : (cycle c d R hR).grading.grading z = sumSwap z := by
  change CliffordOddBalancedTensor.hilbertEquiv d.representation
      ((CliffordOddBalancedTensor.sourceGrading d.representation).grading
        ((CliffordOddBalancedTensor.hilbertEquiv d.representation).symm z)) = sumSwap z
  rw [CliffordOddBalancedTensor.hilbertEquiv_grading, HilbertModuleEquiv.apply_symm_apply]

@[simp] theorem cycle_representation (a : A) :
    (cycle c d R hR).representation a = sumMap (baseRepresentation c d a) (baseRepresentation c d a) :=
  CliffordOddBalancedTensor.transport_representation c d a

@[simp] theorem cycle_action (g : Γ) (z : Sum (H := H) d) :
    (cycle c d R hR).groupAction.action g z =
      ((baseAction c d).sum (baseAction c d)).action g z := by
  change balancedEquiv d ((gradedKasparovTensorAction c.cliffordExpansion
    (CliffordOddSourceCycle.cycle d)).action g ((balancedEquiv d).symm z)) = _
  rw [balancedEquiv_action, HilbertModuleEquiv.apply_symm_apply]

def cycleIso : GradedKasparovCycleIso (rawCycle c d R hR) (cycle c d R hR) :=
  (rawCycle c d R hR).transportIso (balancedEquiv d)

end BC4lean.KKTheory.CliffordOddOddCoordinate
