import BC4lean.GradedKasparovCycle
import BC4lean.StandardModuleOperator
import BC4lean.StandardHilbertModuleActions

/-! # The actual standard identity cycle for arbitrary algebra grading

The standard module has the genuine coefficient grading and action, its
actual compact left-multiplication representation, and zero operator.
Compactness uses the proved identification of standard module compacts.
This is identity cycle data; unit laws require the product construction.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ B : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]

/-- The genuine graded identity cycle, retaining a possibly nontrivial
coefficient grading and its compatible actual group action. -/
def gradedStandardIdentityCycle (β : CStarAlgebraAction Γ B) (δ : CStarGrading B)
    (hβ : β.PreservesGrading δ) : GradedKasparovCycle β β δ δ Bᵐᵒᵖ where
  sourceAction_preservesGrading := hβ
  coefficientAction_preservesGrading := hβ
  countablyGenerated := standard_module_isCountablyGenerated
  grading := GradedHilbertModule.standard δ
  groupAction := EquivariantHilbertModule.standard β
  grading_preserved := EquivariantHilbertModule.standard_preservesGrading β δ hβ
  representation := standardLeftMul
  representation_graded := by
    intro b x
    change MulOpposite.op (δ.automorphism (b * MulOpposite.unop x)) =
      MulOpposite.op (δ.automorphism b * δ.automorphism (MulOpposite.unop x))
    rw [map_mul]
  representation_equivariant := by
    intro g b
    ext x
    change MulOpposite.op (β.automorphism g
      (b * β.automorphism g⁻¹ (MulOpposite.unop x))) =
      MulOpposite.op (β.automorphism g b * MulOpposite.unop x)
    simp only [map_mul, CStarAlgebraAction.apply_inv_apply]
  operator := 0
  operator_odd := by intro x; simp
  selfadjoint_mod_compact := by
    intro b
    simpa using IsModuleCompact.zero (B := B) (E := Bᵐᵒᵖ) (F := Bᵐᵒᵖ)
  square_mod_compact := by
    intro b
    simpa using (IsModuleCompact.neg (T := standardLeftMul b)
      (standardLeftMul_mem_moduleCompact b))
  commutator_compact := by
    intro b
    simpa using IsModuleCompact.zero (B := B) (E := Bᵐᵒᵖ) (F := Bᵐᵒᵖ)
  equivariance_mod_compact := by
    intro g b
    have hzero : (EquivariantHilbertModule.standard β).conjugateOperator g
        (0 : AdjointableMap B Bᵐᵒᵖ Bᵐᵒᵖ) = 0 :=
      EquivariantHilbertModule.conjugateOperator_zero
        (EquivariantHilbertModule.standard β) g
    rw [hzero]
    simpa using IsModuleCompact.zero (B := B) (E := Bᵐᵒᵖ) (F := Bᵐᵒᵖ)

@[simp] theorem gradedStandardIdentityCycle_operator
    (β : CStarAlgebraAction Γ B) (δ : CStarGrading B) (hβ : β.PreservesGrading δ) :
    (gradedStandardIdentityCycle β δ hβ).operator = 0 := rfl

@[simp] theorem gradedStandardIdentityCycle_representation
    (β : CStarAlgebraAction Γ B) (δ : CStarGrading B) (hβ : β.PreservesGrading δ) (b : B) :
    (gradedStandardIdentityCycle β δ hβ).representation b = standardLeftMul b := rfl

end BC4lean.KKTheory
