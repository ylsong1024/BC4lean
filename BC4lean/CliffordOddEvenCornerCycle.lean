import BC4lean.CliffordExternalEvenConnectionExtraction
import BC4lean.GradedKasparovCycleTransport
import BC4lean.OddKasparovCycleTransport

/-! # The genuine odd corner of the odd-by-even product tensor

The actual graded tensor cycle is first transported through the completed
balanced coefficient-form unitary. Its true positive coefficient range
is then transported by first-coordinate evaluation. This constructs an
entire odd cycle, not only its Fredholm operator, and gives an actual
whole-cycle isomorphism from the original product extraction.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordOddEvenCorner
open CliffordExternalEvenBalancedTensor

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

abbrev Source := InteriorModuleTensor (E := CliffordPairModule B H)
  (CliffordExternalEvenCycle.cycle d).representation
abbrev Base := InteriorModuleTensor (E := H) d.representation

def balancedEquiv : HilbertModuleEquiv (C × C) (Source (H := H) d) (CliffordPairModule C (Base (H := H) d)) :=
  hilbertEquiv (H := H) d.representation d.grading (CliffordExternalEvenCycle.representation_commutes_grading d)

variable (R : AdjointableMap (C × C) (Source (H := H) d) (Source (H := H) d))
  (hR : GradedKasparovTensorOperatorConditions c.cliffordExpansion (CliffordExternalEvenCycle.cycle d) R)

def rawCycle := gradedKasparovTensorCycleOfConditions c.cliffordExpansion
  (CliffordExternalEvenCycle.cycle d) R hR

def coordinateCycle := (rawCycle c d R hR).transport (balancedEquiv (H := H) d)

def cycle : OddKasparovCycle α γ (Base (H := H) d) :=
  (cliffordExtractOddCycle true (coordinateCycle c d R hR)).transport (cliffordPairFirstRangeEquiv (B := C) (E := Base (H := H) d))

@[simp] theorem cycle_operator :
    (cycle c d R hR).operator = cliffordPairFirstCorner ((balancedEquiv (H := H) d).transport R) := rfl

@[simp] theorem cycle_representation (a : A) :
    (cycle c d R hR).representation a = interiorModuleTensorOperator d.representation (c.representation a) := by
  change cliffordPairFirstCorner ((hilbertEquiv (H := H) d.representation d.grading
      (CliffordExternalEvenCycle.representation_commutes_grading d)).transport
    (interiorModuleTensorOperator (CliffordExternalEvenRepresentation.representation
      d.representation d.grading (CliffordExternalEvenCycle.representation_commutes_grading d))
      (cliffordPairMap (c.representation a) (c.representation a)))) =
    interiorModuleTensorOperator d.representation (c.representation a)
  rw [transport_diagonal_operator, cliffordPairFirstCorner_pair]

@[simp] theorem cycle_action (g : Γ) (z : Base (H := H) d) :
    (cycle c d R hR).groupAction.action g z =
      (c.groupAction.interiorTensor d.groupAction
        (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)).action g z := by
  change ((hilbertEquiv (H := H) d.representation d.grading
      (CliffordExternalEvenCycle.representation_commutes_grading d))
    ((((cliffordPairAction c.groupAction).interiorTensor (cliffordPairAction d.groupAction)
      ((CliffordExternalEvenCycle.cycle d).groupAction.representationEquivariant_of_conjugate
        (CliffordExternalEvenCycle.cycle d).representation_equivariant)).action g)
      ((hilbertEquiv (H := H) d.representation d.grading
        (CliffordExternalEvenCycle.representation_commutes_grading d)).symm
          (cliffordPairMk z 0)))).1 =
    (c.groupAction.interiorTensor d.groupAction
      (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)).action g z
  have h := hilbertEquiv_action d.representation d.grading
    (CliffordExternalEvenCycle.representation_commutes_grading d) c.groupAction d.groupAction
    d.grading_preserved
    (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)
    ((CliffordExternalEvenCycle.cycle d).groupAction.representationEquivariant_of_conjugate
      (CliffordExternalEvenCycle.cycle d).representation_equivariant) g
    ((hilbertEquiv (H := H) d.representation d.grading
      (CliffordExternalEvenCycle.representation_commutes_grading d)).symm (cliffordPairMk z 0))
  have hinv : (hilbertEquiv (H := H) d.representation d.grading
      (CliffordExternalEvenCycle.representation_commutes_grading d)).linearIsometryEquiv
      ((hilbertEquiv (H := H) d.representation d.grading
        (CliffordExternalEvenCycle.representation_commutes_grading d)).symm.linearIsometryEquiv
          (cliffordPairMk z 0)) = cliffordPairMk z 0 :=
    HilbertModuleEquiv.apply_symm_apply
      (hilbertEquiv (H := H) d.representation d.grading
        (CliffordExternalEvenCycle.representation_commutes_grading d)) (cliffordPairMk z 0)
  rw [hinv] at h
  have hfst := congrArg Prod.fst h
  change ((hilbertEquiv (H := H) d.representation d.grading
      (CliffordExternalEvenCycle.representation_commutes_grading d))
    ((((cliffordPairAction c.groupAction).interiorTensor (cliffordPairAction d.groupAction)
      ((CliffordExternalEvenCycle.cycle d).groupAction.representationEquivariant_of_conjugate
        (CliffordExternalEvenCycle.cycle d).representation_equivariant)).action g)
      ((hilbertEquiv (H := H) d.representation d.grading
        (CliffordExternalEvenCycle.representation_commutes_grading d)).symm
          (cliffordPairMk z 0)))).1 =
    (c.groupAction.interiorTensor d.groupAction
      (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)).action g z at hfst
  exact hfst

def extractionIso : OddKasparovCycleIso
    (cliffordExtractOddCycle true (rawCycle c d R hR)) (cycle c d R hR) :=
  ((rawCycle c d R hR).transportIso (balancedEquiv (H := H) d)).cliffordExtraction true |>.trans
    ((cliffordExtractOddCycle true (coordinateCycle c d R hR)).transportIso (cliffordPairFirstRangeEquiv (B := C) (E := Base (H := H) d)))

end BC4lean.KKTheory.CliffordOddEvenCorner
