import BC4lean.LeftUnitUnitizationData
import BC4lean.ClosedStarHomKernelActions
import BC4lean.GradedIntervalKasparovFibre
import BC4lean.HomogeneousModuleParsevalFrame

/-! # Genuine graded equivariant structures on the left-unit interval ideal

The unitized coefficient grading and action preserve scalar evaluation at one.
They therefore act on the actual closed ideal J. Countable generation supplies
an actual homogeneous Parseval frame. Every A-localized frame coefficient is
the embedding of a continuous A-valued function, as proved in the ideal leaf.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {Γ A : Type*} [Group Γ] [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
theorem leftUnitIntervalScalarQuotient_grading
    [PartialOrder A] [StarOrderedRing A] (δ : CStarGrading A)
    (b : C(unitInterval, Unitization ℂ A)) :
    leftUnitIntervalScalarQuotient ((δ.leftUnitUnitization.continuousSections (X := unitInterval)).automorphism b) =
      leftUnitIntervalScalarQuotient b := rfl

omit [PartialOrder A] [StarOrderedRing A] in
theorem leftUnitIntervalScalarQuotient_action
    [PartialOrder A] [StarOrderedRing A] (α : CStarAlgebraAction Γ A) (g : Γ)
    (b : C(unitInterval, Unitization ℂ A)) :
    leftUnitIntervalScalarQuotient
        ((α.leftUnitUnitization.continuousSections (X := unitInterval)).automorphism g b) =
      leftUnitIntervalScalarQuotient b := rfl

def leftUnitIntervalGrading (δ : CStarGrading A) :
    GradedHilbertModule (δ.leftUnitUnitization.continuousSections (X := unitInterval))
      (LeftUnitIntervalIdeal A) :=
  starHomKernelGrading (leftUnitIntervalScalarQuotient (A := A))
    (δ.leftUnitUnitization.continuousSections (X := unitInterval))
    (leftUnitIntervalScalarQuotient_grading δ)

def leftUnitIntervalAction (α : CStarAlgebraAction Γ A) :
    EquivariantHilbertModule (α.leftUnitUnitization.continuousSections (X := unitInterval))
      (LeftUnitIntervalIdeal A) :=
  starHomKernelAction (leftUnitIntervalScalarQuotient (A := A))
    (α.leftUnitUnitization.continuousSections (X := unitInterval))
    (leftUnitIntervalScalarQuotient_action α)

theorem leftUnitIntervalAction_preservesGrading
    {α : CStarAlgebraAction Γ A} {δ : CStarGrading A} (h : α.PreservesGrading δ) :
    (leftUnitIntervalAction α).PreservesGrading (leftUnitIntervalGrading δ) :=
  starHomKernelAction_preservesGrading (leftUnitIntervalScalarQuotient (A := A))
    (α.leftUnitUnitization.continuousSections (X := unitInterval))
    (δ.leftUnitUnitization.continuousSections (X := unitInterval))
    (leftUnitIntervalScalarQuotient_action α) (leftUnitIntervalScalarQuotient_grading δ)
    (CStarAlgebraAction.preservesGrading_continuousSections (X := unitInterval)
      (CStarAlgebraAction.leftUnitUnitization_preservesGrading h))

@[simp] theorem leftUnitIntervalGrading_apply (δ : CStarGrading A)
    (x : LeftUnitIntervalIdeal A) (t : unitInterval) :
    MulOpposite.unop ((leftUnitIntervalGrading δ).grading x :
      C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) t =
    δ.leftUnitUnitization.automorphism
      (MulOpposite.unop (x : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) t) := rfl

@[simp] theorem leftUnitIntervalAction_apply (α : CStarAlgebraAction Γ A)
    (g : Γ) (x : LeftUnitIntervalIdeal A) (t : unitInterval) :
    MulOpposite.unop ((leftUnitIntervalAction α).action g x :
      C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) t =
    α.leftUnitUnitization.automorphism g
      (MulOpposite.unop (x : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) t) := rfl

theorem leftUnitIntervalRepresentation_graded (δ : CStarGrading A)
    (a : A) (x : LeftUnitIntervalIdeal A) :
    (leftUnitIntervalGrading δ).grading (leftUnitIntervalRepresentation a x) =
      leftUnitIntervalRepresentation (δ.automorphism a) ((leftUnitIntervalGrading δ).grading x) := by
  have ha : (δ.leftUnitUnitization.continuousSections (X := unitInterval)).automorphism
      (leftUnitIntervalCoefficientHom a) =
      leftUnitIntervalCoefficientHom (δ.automorphism a) := by
    apply ContinuousMap.ext
    intro t
    exact leftUnitUnitizationEquiv_inr δ.automorphism a
  have h := starHomKernelLeftMul_graded (leftUnitIntervalScalarQuotient (A := A))
    (δ.leftUnitUnitization.continuousSections (X := unitInterval))
    (leftUnitIntervalScalarQuotient_grading δ) (leftUnitIntervalCoefficientHom a) x
  simpa only [leftUnitIntervalGrading, leftUnitIntervalRepresentation,
    NonUnitalStarAlgHom.comp_apply, ha] using h

theorem leftUnitIntervalRepresentation_equivariant (α : CStarAlgebraAction Γ A)
    (g : Γ) (a : A) :
    (leftUnitIntervalAction α).conjugateOperator g (leftUnitIntervalRepresentation a) =
      leftUnitIntervalRepresentation (α.automorphism g a) := by
  have ha : (α.leftUnitUnitization.continuousSections (X := unitInterval)).automorphism g
      (leftUnitIntervalCoefficientHom a) =
      leftUnitIntervalCoefficientHom (α.automorphism g a) := by
    apply ContinuousMap.ext
    intro t
    exact leftUnitUnitizationEquiv_inr (α.automorphism g) a
  have h := starHomKernelLeftMul_equivariant (leftUnitIntervalScalarQuotient (A := A))
    (α.leftUnitUnitization.continuousSections (X := unitInterval))
    (leftUnitIntervalScalarQuotient_action α) g (leftUnitIntervalCoefficientHom a)
  simpa only [leftUnitIntervalAction, leftUnitIntervalRepresentation,
    NonUnitalStarAlgHom.comp_apply, ha] using h

/-- A frame exists on the actual ideal, without a splitting or a presumed frame. -/
theorem leftUnitIntervalIdeal_exists_homogeneousParsevalFrame
    [TopologicalSpace.SeparableSpace A] (δ : CStarGrading A) :
    ∃ (ξ : ℕ → LeftUnitIntervalIdeal A) (p : ℕ → Bool),
      Nonempty (ModuleParsevalFrame (B := C(unitInterval, Unitization ℂ A)) ξ) ∧
      ∀ n, (leftUnitIntervalGrading δ).grading (ξ n) = if p n then -ξ n else ξ n :=
  exists_homogeneousModuleParsevalFrame (J := leftUnitIntervalGrading δ)
    (leftUnitIntervalIdeal_countablyGenerated (A := A))

set_option maxHeartbeats 800000 in
/-- The first factor is a genuine identity-type A,C(I,U) cycle with operator zero.
It is not combined with an alleged Unitization cycle in the second factor. -/
def leftUnitIntervalIdealIdentityCycle [TopologicalSpace.SeparableSpace A]
    (α : CStarAlgebraAction Γ A) (δ : CStarGrading A) (h : α.PreservesGrading δ) :
    GradedKasparovCycle α (α.leftUnitUnitization.continuousSections (X := unitInterval))
      δ (δ.leftUnitUnitization.continuousSections (X := unitInterval)) (LeftUnitIntervalIdeal A) where
  sourceAction_preservesGrading := h
  coefficientAction_preservesGrading :=
    CStarAlgebraAction.preservesGrading_continuousSections (X := unitInterval)
      (CStarAlgebraAction.leftUnitUnitization_preservesGrading h)
  countablyGenerated := leftUnitIntervalIdeal_countablyGenerated
  grading := leftUnitIntervalGrading δ
  groupAction := leftUnitIntervalAction α
  grading_preserved := leftUnitIntervalAction_preservesGrading h
  representation := leftUnitIntervalRepresentation
  representation_graded := leftUnitIntervalRepresentation_graded δ
  representation_equivariant := leftUnitIntervalRepresentation_equivariant α
  operator := 0
  operator_odd := by intro x; simp only [AdjointableMap.coe_zero_apply, map_zero, neg_zero]
  selfadjoint_mod_compact := by
    intro a
    simp only [star_zero, sub_self, zero_mul]
    exact IsModuleCompact.zero
  square_mod_compact := by
    intro a
    simp only [zero_mul, zero_sub, neg_mul, one_mul]
    exact (leftUnitIntervalRepresentation_isModuleCompact a).neg
  commutator_compact := by
    intro a
    simp only [zero_mul, mul_zero, sub_self]
    exact IsModuleCompact.zero
  equivariance_mod_compact := by
    intro g a
    have hzero : (leftUnitIntervalAction α).conjugateOperator g
        (0 : AdjointableMap C(unitInterval, Unitization ℂ A)
          (LeftUnitIntervalIdeal A) (LeftUnitIntervalIdeal A)) = 0 :=
      EquivariantHilbertModule.conjugateOperator_zero (leftUnitIntervalAction α) g
    change IsModuleCompact
      (((leftUnitIntervalAction α).conjugateOperator g 0 - 0) * leftUnitIntervalRepresentation a)
    rw [hzero, sub_self, zero_mul]
    exact IsModuleCompact.zero

end BC4lean.KKTheory
