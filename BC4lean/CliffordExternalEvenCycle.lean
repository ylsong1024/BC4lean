import BC4lean.CliffordExternalEvenOperator
import BC4lean.EquivariantOperatorAutomorphism

/-! # Genuine external Cl₁ extension of an even cycle

The coefficient tensor is the complete product model C ⊗ Cl₁; the actual
vector tensor and its full inner product are proved in ExternalEvenTensor.
The source tensor uses the Koszul representation involving the original
module grading. All four compact defects follow from the given cycle, not
from assumed existence of an external cycle or a KK product.
-/

noncomputable section
namespace BC4lean.KKTheory

namespace CliffordExternalEvenCycle

open CliffordExternalEvenRepresentation

variable {Γ B C F : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F]
  [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]
  {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  (d : GradedKasparovCycle β γ CStarGrading.trivial CStarGrading.trivial F)

theorem representation_commutes_grading (b : B) :
    d.grading.toAdjointable * d.representation b =
      d.representation b * d.grading.toAdjointable := by
  ext x
  exact d.representation_graded b x

def half : (B × B) →⋆ₙₐ[ℂ] AdjointableMap C F F :=
  halfRepresentation d.representation d.grading (representation_commutes_grading d)

theorem conjugate_grading (g : Γ) :
    d.groupAction.conjugateOperator g d.grading.toAdjointable = d.grading.toAdjointable := by
  ext x
  change d.groupAction.action g (d.grading.grading (d.groupAction.action g⁻¹ x)) =
    d.grading.grading x
  rw [d.grading_preserved, d.groupAction.apply_inv_apply]

theorem half_equivariant (g : Γ) (b : B × B) :
    d.groupAction.conjugateOperator g (half d b) =
      half d ((cliffordCoefficientAction β).automorphism g b) := by
  let U := d.groupAction.conjugateOperatorStarAlgEquiv g
  have hρ (a : B) : U (d.representation a) =
      d.representation (β.automorphism g a) := by
    change d.groupAction.conjugateOperator g (d.representation a) = _
    exact d.representation_equivariant g a
  have hJ : U d.grading.toAdjointable = d.grading.toAdjointable := by
    change d.groupAction.conjugateOperator g d.grading.toAdjointable = _
    exact conjugate_grading d g
  change U (half d b) = _
  simp only [half, halfRepresentation_eq, CliffordOne.plusProjection,
    CliffordOne.minusProjection, map_add, map_sub, map_smul, map_mul,
    map_one, hρ, hJ,
    cliffordCoefficientAction_apply]

/-- The actual external cycle, with neither a parity nor a product law
among its construction hypotheses. -/
def cycle :
    GradedKasparovCycle (cliffordCoefficientAction β) (cliffordCoefficientAction γ)
      cliffordCoefficientGrading cliffordCoefficientGrading (CliffordPairModule C F) where
  sourceAction_preservesGrading := cliffordCoefficientAction_preservesGrading β
  coefficientAction_preservesGrading := cliffordCoefficientAction_preservesGrading γ
  countablyGenerated := d.countablyGenerated.cliffordPair
  grading := cliffordExternalEvenGrading d.grading
  groupAction := cliffordPairAction d.groupAction
  grading_preserved g x := by
    apply Prod.ext <;> exact d.grading_preserved g _
  representation := representation d.representation d.grading (representation_commutes_grading d)
  representation_graded b x := by
    apply Prod.ext
    · exact congrArg (fun T : AdjointableMap C F F => T x.2)
        (grading_commutes_half d.representation d.grading
          (representation_commutes_grading d) (cliffordCoefficientGrading.automorphism b))
    · change (d.grading.toAdjointable * half d b) x.1 =
        (half d (cliffordCoefficientGrading.automorphism
          (cliffordCoefficientGrading.automorphism b)) * d.grading.toAdjointable) x.1
      rw [CStarGrading.automorphism_sq]
      exact
        congrArg (fun T : AdjointableMap C F F => T x.1)
          (grading_commutes_half d.representation d.grading
            (representation_commutes_grading d) b)
  representation_equivariant g b := by
    change (cliffordPairAction d.groupAction).conjugateOperator g
      (cliffordPairMap (half d b) (half d (cliffordCoefficientGrading.automorphism b))) = _
    rw [cliffordPairAction_conjugate, half_equivariant, half_equivariant]
    rfl
  operator := cliffordPairMap d.operator d.operator
  operator_odd x := by
    apply Prod.ext <;> exact d.operator_odd _
  selfadjoint_mod_compact b := by
    change IsModuleCompact ((cliffordPairMap d.operator d.operator -
      star (cliffordPairMap d.operator d.operator)) *
        cliffordPairMap (half d b) (half d (cliffordCoefficientGrading.automorphism b)))
    rw [← cliffordPairMap_star, ← cliffordPairMap_sub, ← cliffordPairMap_mul]
    exact (half_localized_compact d.representation d.grading
      (representation_commutes_grading d) (d.operator - star d.operator)
        d.selfadjoint_mod_compact b).cliffordPairMap
      (half_localized_compact d.representation d.grading
        (representation_commutes_grading d) (d.operator - star d.operator)
          d.selfadjoint_mod_compact (cliffordCoefficientGrading.automorphism b))
  square_mod_compact b := by
    change IsModuleCompact ((cliffordPairMap d.operator d.operator *
      cliffordPairMap d.operator d.operator - 1) *
        cliffordPairMap (half d b) (half d (cliffordCoefficientGrading.automorphism b)))
    rw [← cliffordPairMap_mul, ← cliffordPairMap_one, ← cliffordPairMap_sub, ← cliffordPairMap_mul]
    exact (half_localized_compact d.representation d.grading
      (representation_commutes_grading d) (d.operator * d.operator - 1)
        d.square_mod_compact b).cliffordPairMap
      (half_localized_compact d.representation d.grading
        (representation_commutes_grading d) (d.operator * d.operator - 1)
          d.square_mod_compact (cliffordCoefficientGrading.automorphism b))
  commutator_compact b := by
    change IsModuleCompact (cliffordPairMap d.operator d.operator *
      cliffordPairMap (half d b) (half d (cliffordCoefficientGrading.automorphism b)) -
        cliffordPairMap (half d (cliffordCoefficientGrading.automorphism b)) (half d b) *
          cliffordPairMap d.operator d.operator)
    rw [← cliffordPairMap_mul, ← cliffordPairMap_mul, ← cliffordPairMap_sub]
    apply (half_graded_commutator_compact d.representation d.grading
      (representation_commutes_grading d) d.operator d.operator_odd
        d.commutator_compact b).cliffordPairMap
    simpa only [CStarGrading.automorphism_sq, half] using
      half_graded_commutator_compact d.representation d.grading
        (representation_commutes_grading d) d.operator d.operator_odd
          d.commutator_compact (cliffordCoefficientGrading.automorphism b)
  equivariance_mod_compact g b := by
    change IsModuleCompact (((cliffordPairAction d.groupAction).conjugateOperator g
      (cliffordPairMap d.operator d.operator) - cliffordPairMap d.operator d.operator) *
        cliffordPairMap (half d b) (half d (cliffordCoefficientGrading.automorphism b)))
    rw [cliffordPairAction_conjugate, ← cliffordPairMap_sub, ← cliffordPairMap_mul]
    exact (half_localized_compact d.representation d.grading
      (representation_commutes_grading d) (d.groupAction.conjugateOperator g d.operator - d.operator)
        (d.equivariance_mod_compact g) b).cliffordPairMap
      (half_localized_compact d.representation d.grading
        (representation_commutes_grading d) (d.groupAction.conjugateOperator g d.operator - d.operator)
          (d.equivariance_mod_compact g) (cliffordCoefficientGrading.automorphism b))

end CliffordExternalEvenCycle
end BC4lean.KKTheory
