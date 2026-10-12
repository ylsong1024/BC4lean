import BC4lean.GroupUniverseCompactCorrespondenceInterval
import BC4lean.GradedMatrixMoritaInverse
import BC4lean.GradedMatrixMoritaTensorDirectSumCycle

/-! # Independent-universe actual matrix Morita interval transport

Whole cycles and single full arbitrary-module interval witnesses are
transported in both directions. The actual row and column tensors raise only the module universe to
max(uE,uB). Their constructed inverse double-tensor cycle unitaries retain
the original carrier; quotient identities use an explicit actual lift. No equivalence of homotopy relations or
Morita quotient theorem is assumed.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory.GroupUniverseMatrixMoritaTransport

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ] [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {δA : CStarGrading A}
  (β : CStarAlgebraAction Γ B)

open GradedMatrixMoritaEquivariant

def toMatrix (c : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA CStarGrading.trivial) :
    BundledGradedKasparovCycle.{uΓ,uA,uB,max uE uB} α (matrixAction β) δA GradedMatrixMoritaMatrix.grading :=
  .of (E := InteriorModuleTensor (B := B) (C := GradedMatrixMoritaMatrix B)
    (E := c.carrier) (F := GradedMatrixMoritaRow B)
    (GradedMatrixMoritaRow.leftAction (B := B)))
    (GradedMatrixMoritaCycle.coefficientToMatrix (B := B) (E := c.carrier) β c.cycle)

def toCoefficient
    (c : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α (matrixAction β) δA GradedMatrixMoritaMatrix.grading) :
    BundledGradedKasparovCycle.{uΓ,uA,uB,max uE uB} α β δA CStarGrading.trivial :=
  .of (E := InteriorModuleTensor (B := GradedMatrixMoritaMatrix B) (C := B)
    (E := c.carrier) (F := GradedMatrixMoritaColumn B)
    (GradedMatrixMoritaColumn.leftAction (B := B)))
    (GradedMatrixMoritaCycle.matrixToCoefficient (B := B) (E := c.carrier) β c.cycle)


set_option maxHeartbeats 1200000 in
def coefficientInverseIso
    (c : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA CStarGrading.trivial) :
    GradedKasparovCycleIso (toCoefficient β (toMatrix β c)).cycle c.cycle := by
  rcases c with @⟨M, nM, sM, aM, hM, completeM, raw⟩
  letI : NormedAddCommGroup M := nM
  letI : NormedSpace ℂ M := sM
  letI : SMul Bᵐᵒᵖ M := aM
  letI : CStarModule Bᵐᵒᵖ M := hM
  letI : CompleteSpace M := completeM
  dsimp only [toCoefficient, toMatrix, BundledGradedKasparovCycle.of]
  exact GradedMatrixMoritaInverse.coefficientCycleIso (B := B) (E := M) β raw


set_option maxHeartbeats 1200000 in
def matrixInverseIso
    (c : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α (matrixAction β) δA GradedMatrixMoritaMatrix.grading) :
    GradedKasparovCycleIso (toMatrix β (toCoefficient β c)).cycle c.cycle := by
  rcases c with @⟨M, nM, sM, aM, hM, completeM, raw⟩
  letI : NormedAddCommGroup M := nM
  letI : NormedSpace ℂ M := sM
  letI : SMul (GradedMatrixMoritaMatrix B)ᵐᵒᵖ M := aM
  letI : CStarModule (GradedMatrixMoritaMatrix B)ᵐᵒᵖ M := hM
  letI : CompleteSpace M := completeM
  dsimp only [toMatrix, toCoefficient, BundledGradedKasparovCycle.of]
  exact GradedMatrixMoritaInverse.matrixCycleIso (B := B) (E := M) β raw


set_option maxHeartbeats 1200000 in
def toMatrixIso
    {c d : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA CStarGrading.trivial} (e : c.Iso d) :
    (toMatrix β c).Iso (toMatrix β d) := by
  let i := GradedMatrixMoritaFirstTensorUnitary.cycleIso
    (B := B) (C := GradedMatrixMoritaMatrix B) (E := c.carrier) (G := d.carrier)
    (F := GradedMatrixMoritaRow B) (c := c.cycle) (d := d.cycle)
    (GradedMatrixMoritaRow.leftAction (B := B))
      (matrixAction β) GradedMatrixMoritaMatrix.grading GradedMatrixMoritaRow.grading
      (rowAction β) (matrixAction_preservesGrading β) (rowAction_preservesGrading β)
      GradedMatrixMoritaRow.leftAction_graded (rowRepresentation_equivariant β)
      GradedMatrixMoritaRow.leftAction_compact GradedMatrixMoritaRow.countablyGenerated e
  change GradedKasparovCycleIso
    (GradedMatrixMoritaCycle.coefficientToMatrix (B := B) (E := c.carrier) β c.cycle)
    (GradedMatrixMoritaCycle.coefficientToMatrix (B := B) (E := d.carrier) β d.cycle)
  exact i


set_option maxHeartbeats 1200000 in
def toCoefficientIso
    {c d : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α (matrixAction β) δA GradedMatrixMoritaMatrix.grading}
    (e : c.Iso d) : (toCoefficient β c).Iso (toCoefficient β d) := by
  let i := GradedMatrixMoritaFirstTensorUnitary.cycleIso
    (B := GradedMatrixMoritaMatrix B) (C := B) (E := c.carrier) (G := d.carrier)
    (F := GradedMatrixMoritaColumn B) (c := c.cycle) (d := d.cycle)
    (GradedMatrixMoritaColumn.leftAction (B := B))
      β CStarGrading.trivial GradedMatrixMoritaColumn.grading (columnAction β)
      β.preservesGrading_trivial (columnAction_preservesGrading β)
      GradedMatrixMoritaColumn.leftAction_graded (columnRepresentation_equivariant β)
      GradedMatrixMoritaColumn.leftAction_compact GradedMatrixMoritaColumn.countablyGenerated e
  change GradedKasparovCycleIso
    (GradedMatrixMoritaCycle.matrixToCoefficient (B := B) (E := c.carrier) β c.cycle)
    (GradedMatrixMoritaCycle.matrixToCoefficient (B := B) (E := d.carrier) β d.cycle)
  exact i


set_option maxHeartbeats 1200000 in
def toMatrixFull {c d : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA CStarGrading.trivial}
    (h : FullGradedKasparovHomotopy c d) :
    FullGradedKasparovHomotopy (toMatrix β c) (toMatrix β d) := by
  let source := GroupUniverseCompactCorrespondenceInterval.tensor
    (Γ := Γ) (A := A) (B := B) (C := GradedMatrixMoritaMatrix B)
    (F := GradedMatrixMoritaRow B) (α := α) (β := β) (δA := δA)
    (δB := (CStarGrading.trivial : CStarGrading B))
      (matrixAction β) GradedMatrixMoritaMatrix.grading
      GradedMatrixMoritaRow.grading (rowAction β) (matrixAction_preservesGrading β)
      (rowAction_preservesGrading β) (GradedMatrixMoritaRow.leftAction (B := B))
      GradedMatrixMoritaRow.leftAction_graded (rowRepresentation_equivariant β)
      GradedMatrixMoritaRow.leftAction_compact GradedMatrixMoritaRow.countablyGenerated c
  let target := GroupUniverseCompactCorrespondenceInterval.tensor
    (Γ := Γ) (A := A) (B := B) (C := GradedMatrixMoritaMatrix B)
    (F := GradedMatrixMoritaRow B) (α := α) (β := β) (δA := δA)
    (δB := (CStarGrading.trivial : CStarGrading B))
      (matrixAction β) GradedMatrixMoritaMatrix.grading
      GradedMatrixMoritaRow.grading (rowAction β) (matrixAction_preservesGrading β)
      (rowAction_preservesGrading β) (GradedMatrixMoritaRow.leftAction (B := B))
      GradedMatrixMoritaRow.leftAction_graded (rowRepresentation_equivariant β)
      GradedMatrixMoritaRow.leftAction_compact GradedMatrixMoritaRow.countablyGenerated d
  let h' := GroupUniverseCompactCorrespondenceInterval.full
    (Γ := Γ) (A := A) (B := B) (C := GradedMatrixMoritaMatrix B)
    (F := GradedMatrixMoritaRow B) (α := α) (β := β) (δA := δA)
    (δB := (CStarGrading.trivial : CStarGrading B))
    (c := c) (d := d)
      (matrixAction β) GradedMatrixMoritaMatrix.grading
      GradedMatrixMoritaRow.grading (rowAction β) (matrixAction_preservesGrading β)
      (rowAction_preservesGrading β) (GradedMatrixMoritaRow.leftAction (B := B))
      GradedMatrixMoritaRow.leftAction_graded (rowRepresentation_equivariant β)
      GradedMatrixMoritaRow.leftAction_compact GradedMatrixMoritaRow.countablyGenerated h
  change FullGradedKasparovHomotopy source target
  exact h'


set_option maxHeartbeats 1200000 in
def toCoefficientFull
    {c d : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α (matrixAction β) δA GradedMatrixMoritaMatrix.grading}
    (h : FullGradedKasparovHomotopy c d) :
    FullGradedKasparovHomotopy (toCoefficient β c) (toCoefficient β d) := by
  let source := GroupUniverseCompactCorrespondenceInterval.tensor
    (Γ := Γ) (A := A) (B := GradedMatrixMoritaMatrix B) (C := B)
    (F := GradedMatrixMoritaColumn B) (α := α) (β := matrixAction β) (δA := δA)
    (δB := GradedMatrixMoritaMatrix.grading (B := B))
      β CStarGrading.trivial
      GradedMatrixMoritaColumn.grading (columnAction β) β.preservesGrading_trivial
      (columnAction_preservesGrading β) (GradedMatrixMoritaColumn.leftAction (B := B))
      GradedMatrixMoritaColumn.leftAction_graded (columnRepresentation_equivariant β)
      GradedMatrixMoritaColumn.leftAction_compact GradedMatrixMoritaColumn.countablyGenerated c
  let target := GroupUniverseCompactCorrespondenceInterval.tensor
    (Γ := Γ) (A := A) (B := GradedMatrixMoritaMatrix B) (C := B)
    (F := GradedMatrixMoritaColumn B) (α := α) (β := matrixAction β) (δA := δA)
    (δB := GradedMatrixMoritaMatrix.grading (B := B))
      β CStarGrading.trivial
      GradedMatrixMoritaColumn.grading (columnAction β) β.preservesGrading_trivial
      (columnAction_preservesGrading β) (GradedMatrixMoritaColumn.leftAction (B := B))
      GradedMatrixMoritaColumn.leftAction_graded (columnRepresentation_equivariant β)
      GradedMatrixMoritaColumn.leftAction_compact GradedMatrixMoritaColumn.countablyGenerated d
  let h' := GroupUniverseCompactCorrespondenceInterval.full
    (Γ := Γ) (A := A) (B := GradedMatrixMoritaMatrix B) (C := B)
    (F := GradedMatrixMoritaColumn B) (α := α) (β := matrixAction β) (δA := δA)
    (δB := GradedMatrixMoritaMatrix.grading (B := B))
    (c := c) (d := d)
      β CStarGrading.trivial
      GradedMatrixMoritaColumn.grading (columnAction β) β.preservesGrading_trivial
      (columnAction_preservesGrading β) (GradedMatrixMoritaColumn.leftAction (B := B))
      GradedMatrixMoritaColumn.leftAction_graded (columnRepresentation_equivariant β)
      GradedMatrixMoritaColumn.leftAction_compact GradedMatrixMoritaColumn.countablyGenerated h
  change FullGradedKasparovHomotopy source target
  exact h'

def toMatrixDirectSumIso
    (c d : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α β δA CStarGrading.trivial) :
    (toMatrix β (c.directSum d)).Iso ((toMatrix β c).directSum (toMatrix β d)) :=
  GradedMatrixMoritaTensorDirectSum.cycleIso GradedMatrixMoritaRow.leftAction c.cycle d.cycle
    (matrixAction β) GradedMatrixMoritaMatrix.grading GradedMatrixMoritaRow.grading
    (rowAction β) (matrixAction_preservesGrading β) (rowAction_preservesGrading β)
    GradedMatrixMoritaRow.leftAction_graded (rowRepresentation_equivariant β)
    GradedMatrixMoritaRow.leftAction_compact GradedMatrixMoritaRow.countablyGenerated

set_option maxHeartbeats 1200000 in
def toCoefficientDirectSumIso
    (c d : BundledGradedKasparovCycle.{uΓ,uA,uB,uE} α (matrixAction β) δA GradedMatrixMoritaMatrix.grading) :
    (toCoefficient β (c.directSum d)).Iso ((toCoefficient β c).directSum (toCoefficient β d)) := by
  let i := GradedMatrixMoritaTensorDirectSum.cycleIso
    (B := GradedMatrixMoritaMatrix B) (C := B)
    (E := c.carrier) (G := d.carrier) (F := GradedMatrixMoritaColumn B)
    (GradedMatrixMoritaColumn.leftAction (B := B)) c.cycle d.cycle
      β CStarGrading.trivial GradedMatrixMoritaColumn.grading (columnAction β)
      β.preservesGrading_trivial (columnAction_preservesGrading β)
      GradedMatrixMoritaColumn.leftAction_graded (columnRepresentation_equivariant β)
      GradedMatrixMoritaColumn.leftAction_compact GradedMatrixMoritaColumn.countablyGenerated
  change GradedKasparovCycleIso
    (GradedMatrixMoritaCycle.matrixToCoefficient (B := B)
      (E := HilbertModuleSum (GradedMatrixMoritaMatrix B) c.carrier d.carrier)
      β (c.cycle.directSum d.cycle))
    ((GradedMatrixMoritaCycle.matrixToCoefficient (B := B) (E := c.carrier) β c.cycle).directSum
      (GradedMatrixMoritaCycle.matrixToCoefficient (B := B) (E := d.carrier) β d.cycle))
  exact i



end BC4lean.KKTheory.GroupUniverseMatrixMoritaTransport
