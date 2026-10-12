import BC4lean.CliffordExternalEvenRepresentation

/-! # Actual graded operator formulas for external Cl₁ extension

The half-representation is the sum of the two source coordinates multiplied
by the actual spectral projections of J. An odd operator exchanges these
projections. This proves the true graded commutator formula and transfers
all localized compact defects through the closed module compact ideal.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordExternalEvenRepresentation

variable {B C F : Type*} [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F]
  [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
  (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading C) F)
  (hφ : ∀ b, J.toAdjointable * φ b = φ b * J.toAdjointable)

theorem halfRepresentation_eq (b : B × B) :
    halfRepresentation φ J hφ b =
      φ b.1 * CliffordOne.plusProjection J.toAdjointable +
        φ b.2 * CliffordOne.minusProjection J.toAdjointable := by
  change φ b.1 * (cliffordRepresentation J).toNonUnitalStarAlgHom (1, 0) +
    φ b.2 * (cliffordRepresentation J).toNonUnitalStarAlgHom (0, 1) = _
  simp only [StarAlgHom.coe_toNonUnitalStarAlgHom, cliffordRepresentation,
    CliffordOne.lift_apply, one_smul, zero_smul, add_zero, zero_add]

theorem grading_commutes_plus :
    J.toAdjointable * CliffordOne.plusProjection J.toAdjointable =
      CliffordOne.plusProjection J.toAdjointable * J.toAdjointable := by
  simp only [CliffordOne.plusProjection, mul_smul_comm,
    smul_mul_assoc, mul_add, add_mul, one_mul, mul_one]

theorem grading_commutes_minus :
    J.toAdjointable * CliffordOne.minusProjection J.toAdjointable =
      CliffordOne.minusProjection J.toAdjointable * J.toAdjointable := by
  simp only [CliffordOne.minusProjection, mul_smul_comm,
    smul_mul_assoc, mul_sub, sub_mul, one_mul, mul_one]

theorem grading_commutes_half (b : B × B) :
    J.toAdjointable * halfRepresentation φ J hφ b =
      halfRepresentation φ J hφ b * J.toAdjointable := by
  rw [halfRepresentation_eq, mul_add, add_mul]
  congr 1
  · rw [← mul_assoc, hφ b.1, mul_assoc,
      grading_commutes_plus, ← mul_assoc]
  · rw [← mul_assoc, hφ b.2, mul_assoc,
      grading_commutes_minus, ← mul_assoc]

/-- A genuinely odd operator exchanges the two actual grading projections. -/
theorem odd_mul_plus (T : AdjointableMap C F F) (hT : J.IsOdd J T) :
    T * CliffordOne.plusProjection J.toAdjointable =
      CliffordOne.minusProjection J.toAdjointable * T := by
  have hJT : J.toAdjointable * T = -(T * J.toAdjointable) := by
    ext x
    simpa only [AdjointableMap.mul_apply, AdjointableMap.coe_neg_apply,
      GradedHilbertModule.toAdjointable_apply] using hT x
  have hTJ : T * J.toAdjointable = -(J.toAdjointable * T) := by
    simpa only [neg_neg] using congrArg Neg.neg hJT.symm
  simp only [CliffordOne.plusProjection, CliffordOne.minusProjection,
    mul_smul_comm, smul_mul_assoc, mul_add, add_mul, neg_mul, mul_one,
    one_mul, hTJ, sub_eq_add_neg]

theorem odd_mul_minus (T : AdjointableMap C F F) (hT : J.IsOdd J T) :
    T * CliffordOne.minusProjection J.toAdjointable =
      CliffordOne.plusProjection J.toAdjointable * T := by
  have hJT : J.toAdjointable * T = -(T * J.toAdjointable) := by
    ext x
    simpa only [AdjointableMap.mul_apply, AdjointableMap.coe_neg_apply,
      GradedHilbertModule.toAdjointable_apply] using hT x
  have hTJ : T * J.toAdjointable = -(J.toAdjointable * T) := by
    simpa only [neg_neg] using congrArg Neg.neg hJT.symm
  simp only [CliffordOne.plusProjection, CliffordOne.minusProjection,
    mul_smul_comm, smul_mul_assoc, mul_sub, add_mul, mul_one,
    one_mul, hTJ, sub_neg_eq_add]

/-- This is the real graded commutator; the reflected source coordinate
representation is essential to the formula. -/
theorem odd_half_commutator (T : AdjointableMap C F F) (hT : J.IsOdd J T)
    (b : B × B) :
    T * halfRepresentation φ J hφ b -
      halfRepresentation φ J hφ (cliffordCoefficientGrading.automorphism b) * T =
      (T * φ b.1 - φ b.1 * T) * CliffordOne.plusProjection J.toAdjointable +
        (T * φ b.2 - φ b.2 * T) * CliffordOne.minusProjection J.toAdjointable := by
  rw [halfRepresentation_eq, halfRepresentation_eq]
  change T * (φ b.1 * CliffordOne.plusProjection J.toAdjointable +
      φ b.2 * CliffordOne.minusProjection J.toAdjointable) -
    (φ b.2 * CliffordOne.plusProjection J.toAdjointable +
      φ b.1 * CliffordOne.minusProjection J.toAdjointable) * T = _
  rw [mul_add, add_mul]
  have hplus := odd_mul_plus J T hT
  have hminus := odd_mul_minus J T hT
  simp only [mul_assoc, ← hplus, ← hminus, sub_mul]
  abel

theorem half_localized_compact (T : AdjointableMap C F F)
    (hT : ∀ b, IsModuleCompact (T * φ b)) (b : B × B) :
    IsModuleCompact (T * halfRepresentation φ J hφ b) := by
  rw [halfRepresentation_eq, mul_add, ← mul_assoc, ← mul_assoc]
  exact ((hT b.1).comp_right _).add ((hT b.2).comp_right _)

theorem half_graded_commutator_compact (T : AdjointableMap C F F)
    (hT : J.IsOdd J T)
    (hcomm : ∀ b, IsModuleCompact (T * φ b - φ b * T)) (b : B × B) :
    IsModuleCompact (T * halfRepresentation φ J hφ b -
      halfRepresentation φ J hφ (cliffordCoefficientGrading.automorphism b) * T) := by
  rw [odd_half_commutator φ J hφ T hT b]
  exact ((hcomm b.1).comp_right _).add ((hcomm b.2).comp_right _)

end BC4lean.KKTheory.CliffordExternalEvenRepresentation
