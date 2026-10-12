import BC4lean.CliffordPairSecondConnectionExtraction
import BC4lean.GradedKasparovCycleTransport
import BC4lean.OddKasparovCycleTransport

/-! # The whole odd corner of the genuine even-by-odd product

The actual product cycle is transported through the true second-pair
unitary. Its actual positive coefficient range then passes through the
first-coordinate range unitary, retaining representation, action and every
Fredholm condition. The entire extraction is linked by a cycle isomorphism.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordEvenOddCorner
open CliffordPairSecondTensor

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

abbrev Source := InteriorModuleTensor (E := H) d.cliffordExpansion.representation
abbrev Base := InteriorModuleTensor (E := H) d.representation

def balancedEquiv : HilbertModuleEquiv (C × C) (Source (H := H) d) (CliffordPairModule C (Base (H := H) d)) :=
  hilbertEquiv (E := H) d.representation

variable (R : AdjointableMap (C × C) (Source (H := H) d) (Source (H := H) d))
  (hR : GradedKasparovTensorOperatorConditions c d.cliffordExpansion R)

def rawCycle := gradedKasparovTensorCycleOfConditions c d.cliffordExpansion R hR

def coordinateCycle := (rawCycle c d R hR).transport (balancedEquiv (H := H) d)

def cycle : OddKasparovCycle α γ (Base (H := H) d) :=
  (cliffordExtractOddCycle true (coordinateCycle c d R hR)).transport (cliffordPairFirstRangeEquiv (B := C) (E := Base (H := H) d))

@[simp] theorem cycle_operator :
    (cycle c d R hR).operator = cliffordPairFirstCorner ((balancedEquiv (H := H) d).transport R) := rfl

@[simp] theorem cycle_representation (a : A) :
    (cycle c d R hR).representation a = interiorModuleTensorOperator d.representation (c.representation a) := by
  change cliffordPairFirstCorner ((hilbertEquiv (E := H) d.representation).transport
    (interiorModuleTensorOperator (representation d.representation) (c.representation a))) =
      interiorModuleTensorOperator d.representation (c.representation a)
  rw [transport_firstFactor (E := H) d.representation (c.representation a),
    cliffordPairFirstCorner_pair]

@[simp] theorem cycle_action (g : Γ) (z : Base (H := H) d) :
    (cycle c d R hR).groupAction.action g z =
      (c.groupAction.interiorTensor d.groupAction
        (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)).action g z := by
  let hφ := d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant
  change ((hilbertEquiv (E := H) d.representation)
    ((c.groupAction.interiorTensor (cliffordPairAction d.groupAction)
      (representation_equivariant d.representation d.groupAction hφ)).action g
        ((hilbertEquiv (E := H) d.representation).symm (cliffordPairMk (B := C) z 0)))).1 =
      (c.groupAction.interiorTensor d.groupAction hφ).action g z
  have h := hilbertEquiv_action (E := H) d.representation c.groupAction d.groupAction hφ g
    ((hilbertEquiv (E := H) d.representation).symm (cliffordPairMk (B := C) z 0))
  rw [HilbertModuleEquiv.apply_symm_apply] at h
  exact congrArg Prod.fst h

def extractionIso : OddKasparovCycleIso
    (cliffordExtractOddCycle true (rawCycle c d R hR)) (cycle c d R hR) :=
  ((rawCycle c d R hR).transportIso (balancedEquiv (H := H) d)).cliffordExtraction true |>.trans
    ((cliffordExtractOddCycle true (coordinateCycle c d R hR)).transportIso (cliffordPairFirstRangeEquiv (B := C) (E := Base (H := H) d)))

end BC4lean.KKTheory.CliffordEvenOddCorner
