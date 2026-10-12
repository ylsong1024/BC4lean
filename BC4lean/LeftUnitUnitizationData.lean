import BC4lean.GradedKasparovCycle
import BC4lean.LeftUnitIntervalIdeal
import Mathlib.Tactic.NoncommRing

/-! # Unitization data for the genuine nonunital left-unit construction

The source action and source grading fix the adjoined scalar unit. A possibly
degenerate representation extends unital without an essential-range splitting.
Only its graded commutator is asserted compact for every unitized coefficient.
No square, selfadjointness or equivariance defect is asserted compact at the
adjoined unit. Those defects remain localized by the original algebra A.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {Γ A B E : Type*} [NonUnitalCStarAlgebra A]

/-- The actual unitized automorphism fixes scalars and applies e to the ideal. -/
def leftUnitUnitizationEquiv (e : A ≃⋆ₐ[ℂ] A) :
    Unitization ℂ A ≃⋆ₐ[ℂ] Unitization ℂ A where
  toFun u := ⟨u.fst, e u.snd⟩
  invFun u := ⟨u.fst, e.symm u.snd⟩
  left_inv u := by apply Unitization.ext; rfl; exact e.symm_apply_apply _
  right_inv u := by apply Unitization.ext; rfl; exact e.apply_symm_apply _
  map_add' u v := by
    apply Unitization.ext
    · rfl
    · exact map_add e _ _
  map_mul' u v := by
    apply Unitization.ext
    · rfl
    · change e (u.fst • v.snd + v.fst • u.snd + u.snd * v.snd) = _
      simp only [map_add, map_smul, map_mul]
      rfl
  map_smul' c u := by
    apply Unitization.ext
    · rfl
    · exact map_smul e _ _
  map_star' u := by
    apply Unitization.ext
    · rfl
    · exact map_star e _

@[simp] theorem leftUnitUnitizationEquiv_fst (e : A ≃⋆ₐ[ℂ] A) (u : Unitization ℂ A) :
    (leftUnitUnitizationEquiv e u).fst = u.fst := rfl

@[simp] theorem leftUnitUnitizationEquiv_snd (e : A ≃⋆ₐ[ℂ] A) (u : Unitization ℂ A) :
    (leftUnitUnitizationEquiv e u).snd = e u.snd := rfl

@[simp] theorem leftUnitUnitizationEquiv_inr (e : A ≃⋆ₐ[ℂ] A) (a : A) :
    leftUnitUnitizationEquiv e (a : Unitization ℂ A) = (e a : Unitization ℂ A) := by
  apply Unitization.ext
  · rfl
  · rfl

def CStarGrading.leftUnitUnitization (δ : CStarGrading A) :
    CStarGrading (Unitization ℂ A) where
  automorphism := leftUnitUnitizationEquiv δ.automorphism
  involutive u := by
    apply Unitization.ext
    · rfl
    · exact δ.involutive u.snd

variable [Group Γ]

def CStarAlgebraAction.leftUnitUnitization (α : CStarAlgebraAction Γ A) :
    CStarAlgebraAction Γ (Unitization ℂ A) where
  automorphism :=
    { toFun := fun g => leftUnitUnitizationEquiv (α.automorphism g)
      map_one' := by
        apply StarAlgEquiv.ext
        intro u
        apply Unitization.ext
        · rfl
        · exact α.one_apply u.snd
      map_mul' := fun g h => by
        apply StarAlgEquiv.ext
        intro u
        apply Unitization.ext
        · rfl
        · exact α.mul_apply g h u.snd }

theorem CStarAlgebraAction.leftUnitUnitization_preservesGrading
    {α : CStarAlgebraAction Γ A} {δ : CStarGrading A}
    (h : α.PreservesGrading δ) : α.leftUnitUnitization.PreservesGrading δ.leftUnitUnitization := by
  intro g u
  apply Unitization.ext
  · rfl
  · exact h g u.snd

variable [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- Unital representation extension, not an extended Kasparov cycle. -/
def leftUnitExtendedRepresentation (φ : A →⋆ₙₐ[ℂ] AdjointableMap B E E) :
    Unitization ℂ A →⋆ₐ[ℂ] AdjointableMap B E E := Unitization.starLift φ

omit [StarOrderedRing B] [CompleteSpace E] in
theorem leftUnitExtendedRepresentation_apply
    (φ : A →⋆ₙₐ[ℂ] AdjointableMap B E E) (u : Unitization ℂ A) :
    leftUnitExtendedRepresentation φ u =
      u.fst • (1 : AdjointableMap B E E) + φ u.snd := by
  change algebraMap ℂ (AdjointableMap B E E) u.fst + φ u.snd = _
  rw [Algebra.algebraMap_eq_smul_one]

omit [StarOrderedRing B] [CompleteSpace E] in
@[simp] theorem leftUnitExtendedRepresentation_inr
    (φ : A →⋆ₙₐ[ℂ] AdjointableMap B E E) (a : A) :
    leftUnitExtendedRepresentation φ (a : Unitization ℂ A) = φ a := by
  rw [leftUnitExtendedRepresentation_apply]
  simp only [Unitization.fst_inr, Unitization.snd_inr, zero_smul, zero_add]

omit [StarOrderedRing B] [CompleteSpace E] in
@[simp] theorem leftUnitExtendedRepresentation_one
    (φ : A →⋆ₙₐ[ℂ] AdjointableMap B E E) :
    leftUnitExtendedRepresentation φ 1 = 1 := map_one _

variable {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

namespace GradedKasparovCycle
variable (c : GradedKasparovCycle α β δA δB E)

/-- Scalar cancellation extends exact grading compatibility. -/
theorem leftUnitExtendedRepresentation_graded (u : Unitization ℂ A) (x : E) :
    c.grading.grading (leftUnitExtendedRepresentation c.representation u x) =
      leftUnitExtendedRepresentation c.representation
        (δA.leftUnitUnitization.automorphism u) (c.grading.grading x) := by
  simp only [leftUnitExtendedRepresentation_apply, AdjointableMap.coe_add_apply,
    AdjointableMap.coe_smul_apply, AdjointableMap.one_apply,
    map_add, map_smul, c.representation_graded,
    CStarGrading.leftUnitUnitization, leftUnitUnitizationEquiv_fst,
    leftUnitUnitizationEquiv_snd]

/-- The extended representation is equivariant, including its scalar identity. -/
theorem leftUnitExtendedRepresentation_equivariant (g : Γ) (u : Unitization ℂ A) :
    c.groupAction.conjugateOperator g (leftUnitExtendedRepresentation c.representation u) =
      leftUnitExtendedRepresentation c.representation (α.leftUnitUnitization.automorphism g u) := by
  apply AdjointableMap.ext
  intro x
  have h := congrArg (fun T : AdjointableMap B E E => T x)
    (c.representation_equivariant g u.snd)
  simp only [EquivariantHilbertModule.conjugateMap_apply] at h
  simp only [EquivariantHilbertModule.conjugateMap_apply,
    leftUnitExtendedRepresentation_apply, AdjointableMap.coe_add_apply,
    AdjointableMap.coe_smul_apply, AdjointableMap.one_apply,
    map_add, map_smul, EquivariantHilbertModule.apply_inv_apply]
  exact congrArg (fun y => u.fst • x + y) h

/-- The unitized graded commutator equals an original A commutator. -/
theorem leftUnitExtendedRepresentation_commutator (u : Unitization ℂ A) :
    c.operator * leftUnitExtendedRepresentation c.representation u -
      leftUnitExtendedRepresentation c.representation
        (δA.leftUnitUnitization.automorphism u) * c.operator =
    c.operator * c.representation u.snd -
      c.representation (δA.automorphism u.snd) * c.operator := by
  simp only [leftUnitExtendedRepresentation_apply, CStarGrading.leftUnitUnitization,
    leftUnitUnitizationEquiv_fst, leftUnitUnitizationEquiv_snd,
    mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  noncomm_ring

theorem leftUnitExtendedRepresentation_commutator_compact (u : Unitization ℂ A) :
    IsModuleCompact (c.operator * leftUnitExtendedRepresentation c.representation u -
      leftUnitExtendedRepresentation c.representation
        (δA.leftUnitUnitization.automorphism u) * c.operator) := by
  rw [c.leftUnitExtendedRepresentation_commutator]
  exact c.commutator_compact u.snd

end GradedKasparovCycle
end BC4lean.KKTheory
