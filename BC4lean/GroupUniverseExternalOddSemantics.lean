import BC4lean.GroupUniverseExternalOddClass
import BC4lean.CliffordExternalOddHilbertModule

/-! # The prescribed external tensor underlying the native odd product

The native independent-universe cycle uses the actual completed row tensor.
The genuine complex tensor of the original Clifford pair module with Cl₁
is unitarily that same module, with its full matrix-valued form and Koszul
right action. The cycle's actual grading, group action, representation and
operator have the prescribed elementary external tensor formulas.
-/

noncomputable section
namespace BC4lean.KKTheory.GroupUniverseExternalOddSemantics

open scoped InnerProductSpace TensorProduct
open CliffordExternalOddCoordinates

section Module

variable {C H : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H]
  [CStarModule Cᵐᵒᵖ H] [CompleteSpace H]

local instance groupUniverseExternalOddSemanticsModuleSumComplete :
    CompleteSpace (HilbertModuleSum C H H) := hilbertModuleSum_complete

/-- The full completed external tensor is the native row module, without
discarding either coordinate or any off-diagonal inner-product entry. -/
def moduleEquiv : HilbertModuleEquiv (GradedMatrixMoritaMatrix C)
    (ExternalTensor (C := C) (H := H)) (ExternalModule (C := C) (H := H)) :=
  CliffordExternalOddHilbertModule.hilbertEquiv

/-- The native module retains the full graded external coefficient form. -/
theorem inner_tmul (x y : CliffordPairModule C H) (z w : CliffordOne) :
    MulOpposite.unop ⟪coordinates (x ⊗ₜ[ℂ] z), coordinates (y ⊗ₜ[ℂ] w)⟫_
      ((GradedMatrixMoritaMatrix C)ᵐᵒᵖ) =
    CliffordExternalOddCoefficient.coordinates
      ((MulOpposite.unop ⟪x, y⟫_((C × C)ᵐᵒᵖ)) ⊗ₜ[ℂ]
        (CliffordTwo.evenPart (star z) * w) +
      ((MulOpposite.unop ⟪x, y⟫_((C × C)ᵐᵒᵖ)).2,
        (MulOpposite.unop ⟪x, y⟫_((C × C)ᵐᵒᵖ)).1) ⊗ₜ[ℂ]
        (CliffordTwo.oddPart (star z) * w)) :=
  CliffordExternalOddForm.coordinates_inner_tmul x y z w

/-- The actual right coefficient action has the original odd crossing. -/
theorem op_smul_tmul (a : C × C) (z w : CliffordOne) (y : CliffordPairModule C H) :
    MulOpposite.op (CliffordExternalOddCoefficient.pureMatrix a w) •
      coordinates (y ⊗ₜ[ℂ] z) =
    coordinates ((MulOpposite.op a • y) ⊗ₜ[ℂ] (CliffordTwo.evenPart z * w) +
      (MulOpposite.op (a.2, a.1) • y) ⊗ₜ[ℂ] (CliffordTwo.oddPart z * w)) :=
  CliffordExternalOddModule.coordinates_right_tmul a z w y

end Module

section Cycle

variable {Γ B C H : Type*} [Group Γ]
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder C] [StarOrderedRing C] [TopologicalSpace.SeparableSpace C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H]
  [CStarModule Cᵐᵒᵖ H] [CompleteSpace H]
  {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

local instance groupUniverseExternalOddSemanticsCycleSumComplete :
    CompleteSpace (HilbertModuleSum C H H) := hilbertModuleSum_complete

/-- The native product's actual operator is the original operator tensored
with the identity on the second Clifford factor. -/
theorem operator_tmul (c : OddKasparovCycle β γ H)
    (y : CliffordPairModule C H) (z : CliffordOne) :
    (GroupUniverseExternalOddClass.cycle c).operator (coordinates (y ⊗ₜ[ℂ] z)) =
      coordinates ((cliffordPairMap c.operator (-c.operator) y) ⊗ₜ[ℂ] z) :=
  CliffordExternalOddModule.coordinates_operator_tmul c.operator y z

/-- The native grading is the full tensor grading on the original pair. -/
theorem grading_tmul (c : OddKasparovCycle β γ H)
    (y : CliffordPairModule C H) (z : CliffordOne) :
    (GroupUniverseExternalOddClass.cycle c).grading.grading (coordinates (y ⊗ₜ[ℂ] z)) =
      coordinates ((cliffordPairMk (B := C) y.2 y.1) ⊗ₜ[ℂ]
        (CliffordOne.grading.automorphism z)) :=
  CliffordExternalOddGrading.coordinates_grading_tmul y z

/-- The native source action combines the old semilinear pair grading and
the new Clifford generator, rather than treating that grading as an endomorphism. -/
theorem representation_tmul (c : OddKasparovCycle β γ H) (b : B × B)
    (y : CliffordPairModule C H) (z : CliffordOne) :
    (GroupUniverseExternalOddClass.cycle c).representation b (coordinates (y ⊗ₜ[ℂ] z)) =
      coordinates ((cliffordPairMap
        (c.representation (CliffordExternalOddSource.evenCoefficient b))
        (c.representation (CliffordExternalOddSource.evenCoefficient b)) y) ⊗ₜ[ℂ] z +
      (cliffordPairMk (B := C)
        (c.representation (CliffordExternalOddSource.oddCoefficient b) y.2)
        (c.representation (CliffordExternalOddSource.oddCoefficient b) y.1)) ⊗ₜ[ℂ]
        (CliffordOne.epsilon * z)) :=
  CliffordExternalOddSource.coordinates_source_tmul c.representation b y z

/-- The native group action is the original action with trivial Clifford action. -/
theorem action_tmul (c : OddKasparovCycle β γ H) (g : Γ)
    (y : CliffordPairModule C H) (z : CliffordOne) :
    (GroupUniverseExternalOddClass.cycle c).groupAction.action g
      (coordinates (y ⊗ₜ[ℂ] z)) =
    coordinates ((cliffordPairMk (B := C) (c.groupAction.action g y.1)
      (c.groupAction.action g y.2)) ⊗ₜ[ℂ] z) :=
  CliffordExternalOddAction.coordinates_action_tmul c.groupAction g y z

end Cycle
end BC4lean.KKTheory.GroupUniverseExternalOddSemantics
