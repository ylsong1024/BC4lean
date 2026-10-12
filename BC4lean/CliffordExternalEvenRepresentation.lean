import BC4lean.CliffordExternalEvenTensor
import BC4lean.GradedKasparovCycle
import Mathlib.Tactic.NoncommRing

/-! # Genuine Koszul representation in an external Cl₁ tensor

The new odd Clifford generator acts by the original module grading in the
first coordinate and its negative in the second coordinate. In particular
the representation is not the diagonal pair of the two original source
coordinate representations. The construction uses the proved universal
Cl₁ homomorphism and the genuine commuting tensor lift.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B C F : Type*} [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F]
  [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]

namespace CliffordExternalEvenRepresentation

variable (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
  (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading C) F)
  (hφ : ∀ b, J.toAdjointable * φ b = φ b * J.toAdjointable)

omit [StarOrderedRing C] [CompleteSpace F] in
theorem grading_square : J.toAdjointable * J.toAdjointable = 1 :=
  J.toAdjointable_sq

omit [StarOrderedRing C] [CompleteSpace F] in
theorem grading_selfadjoint : star J.toAdjointable = J.toAdjointable :=
  J.toAdjointable_adjoint

/-- The new Clifford generator has its actual universal star representation. -/
def cliffordRepresentation : CliffordOne →⋆ₐ[ℂ] AdjointableMap C F F :=
  CliffordOne.lift J.toAdjointable (grading_selfadjoint J) (grading_square J)

include hφ in
theorem source_clifford_commute (b : B) (z : CliffordOne) :
    φ b * cliffordRepresentation J z = cliffordRepresentation J z * φ b := by
  change φ b * (z.1 • CliffordOne.plusProjection J.toAdjointable +
      z.2 • CliffordOne.minusProjection J.toAdjointable) = _
  simp only [cliffordRepresentation, CliffordOne.lift_apply,
    CliffordOne.plusProjection, CliffordOne.minusProjection,
    mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    mul_sub, sub_mul, one_mul, mul_one, hφ b]

/-- The first actual external tensor coordinate representation. -/
def halfRepresentation : (B × B) →⋆ₙₐ[ℂ] AdjointableMap C F F :=
  commutingCliffordLift φ (cliffordRepresentation J).toNonUnitalStarAlgHom
    (source_clifford_commute φ J hφ)

theorem halfRepresentation_pure (b : B) (z : CliffordOne) :
    halfRepresentation φ J hφ (z.1 • b, z.2 • b) =
      φ b * cliffordRepresentation J z := by
  exact commutingCliffordLift_tmul φ
    (cliffordRepresentation J).toNonUnitalStarAlgHom
      (source_clifford_commute φ J hφ) b z

/-- The full product-coefficient operator representation, with the Koszul
grading operator in the Clifford factor. -/
def representation : (B × B) →⋆ₙₐ[ℂ]
    AdjointableMap (C × C) (CliffordPairModule C F) (CliffordPairModule C F) where
  toFun b := cliffordPairMap (halfRepresentation φ J hφ b)
    (halfRepresentation φ J hφ (cliffordCoefficientGrading.automorphism b))
  map_zero' := by simp only [map_zero, cliffordPairMap_zero]
  map_add' a b := by simp only [map_add, cliffordPairMap_add]
  map_mul' a b := by simp only [map_mul, cliffordPairMap_mul]
  map_smul' c b := by simp only [map_smul, cliffordPairMap_smul, MonoidHom.id_apply]
  map_star' b := by simp only [map_star, cliffordPairMap_star]

/-- The actual source elementary tensor formula. -/
theorem representation_pure (b : B) (z : CliffordOne) :
    representation φ J hφ (z.1 • b, z.2 • b) =
      cliffordPairMap (φ b * cliffordRepresentation J z)
        (φ b * cliffordRepresentation J (CliffordOne.grading.automorphism z)) := by
  change cliffordPairMap (halfRepresentation φ J hφ (z.1 • b, z.2 • b))
    (halfRepresentation φ J hφ
      ((CliffordOne.grading.automorphism z).1 • b,
        (CliffordOne.grading.automorphism z).2 • b)) = _
  rw [halfRepresentation_pure, halfRepresentation_pure]

/-- On b ⊗ ε the actual odd source generator acts by J and -J. -/
theorem representation_epsilon (b : B) :
    representation φ J hφ (b, -b) =
      cliffordPairMap (φ b * J.toAdjointable) (-(φ b * J.toAdjointable)) := by
  have h := representation_pure φ J hφ b CliffordOne.epsilon
  have hε : cliffordRepresentation J CliffordOne.epsilon = J.toAdjointable :=
    CliffordOne.lift_epsilon J.toAdjointable (grading_selfadjoint J) (grading_square J)
  have hδε : cliffordRepresentation J (CliffordOne.grading.automorphism CliffordOne.epsilon) =
      -J.toAdjointable := by
    rw [CliffordOne.epsilon_odd, map_neg, hε]
  rw [hε, hδε] at h
  simpa only [CliffordOne.epsilon, one_smul, neg_one_smul, mul_neg] using h

end CliffordExternalEvenRepresentation
end BC4lean.KKTheory
