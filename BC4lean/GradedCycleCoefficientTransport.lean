import BC4lean.OppositeStarAlgEquivBetween
import BC4lean.HilbertModuleCoefficientTransport
import BC4lean.GradedKasparovCycle

/-! # Genuine graded cycle transport under coefficient star equivalences

The coefficient equivalence explicitly intertwines the two coefficient
gradings and group actions. The module grading keeps its actual complex
isometry and its semilinear inner-product law. Neither the grading nor the
group action is replaced by a coefficient-linear adjointable operator.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {Γ A B C M : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Bᵐᵒᵖ M] [CStarModule Bᵐᵒᵖ M]

namespace GradedHilbertModule

/-- Transport an actual semilinear module grading. -/
def coefficientChanged {δB : CStarGrading B} (γ : GradedHilbertModule δB M)
    (e : B ≃⋆ₐ[ℂ] C) (δC : CStarGrading C)
    (he : ∀ b, e (δB.automorphism b) = δC.automorphism (e b)) :
    GradedHilbertModule δC (CoefficientChangedModule e M) where
  grading := γ.grading
  involutive := γ.involutive
  inner_grading x y := by
    change opStarAlgEquivBetween e
        ⟪γ.grading (coefficientChangedToOriginal (M := M) e x),
          γ.grading (coefficientChangedToOriginal (M := M) e y)⟫_(Bᵐᵒᵖ) =
      opStarAlgEquiv δC.automorphism (opStarAlgEquivBetween e
        ⟪coefficientChangedToOriginal (M := M) e x,
          coefficientChangedToOriginal (M := M) e y⟫_(Bᵐᵒᵖ))
    rw [γ.inner_grading]
    apply MulOpposite.unop_injective
    exact he _

@[simp] theorem coefficientChanged_grading_apply {δB : CStarGrading B}
    (γ : GradedHilbertModule δB M) (e : B ≃⋆ₐ[ℂ] C) (δC : CStarGrading C)
    (he : ∀ b, e (δB.automorphism b) = δC.automorphism (e b))
    (x : CoefficientChangedModule e M) :
    (γ.coefficientChanged e δC he).grading x = γ.grading (x : M) := rfl

theorem IsOdd.coefficientChanged {δB : CStarGrading B}
    {γ : GradedHilbertModule δB M} {T : AdjointableMap B M M}
    (hT : γ.IsOdd γ T) (e : B ≃⋆ₐ[ℂ] C) (δC : CStarGrading C)
    (he : ∀ b, e (δB.automorphism b) = δC.automorphism (e b)) :
    (γ.coefficientChanged e δC he).IsOdd (γ.coefficientChanged e δC he)
      (coefficientChangedOperator e T) := hT

end GradedHilbertModule

namespace EquivariantHilbertModule

def coefficientChanged {β : CStarAlgebraAction Γ B} (U : EquivariantHilbertModule β M)
    (e : B ≃⋆ₐ[ℂ] C) (η : CStarAlgebraAction Γ C)
    (he : ∀ g b, e (β.automorphism g b) = η.automorphism g (e b)) :
    EquivariantHilbertModule η (CoefficientChangedModule e M) where
  action := U.action
  inner_action g x y := by
    change opStarAlgEquivBetween e
        ⟪U.action g (coefficientChangedToOriginal (M := M) e x),
          U.action g (coefficientChangedToOriginal (M := M) e y)⟫_(Bᵐᵒᵖ) =
      opStarAlgEquiv (η.automorphism g) (opStarAlgEquivBetween e
        ⟪coefficientChangedToOriginal (M := M) e x,
          coefficientChangedToOriginal (M := M) e y⟫_(Bᵐᵒᵖ))
    rw [U.inner_action]
    apply MulOpposite.unop_injective
    exact he g _

@[simp] theorem coefficientChanged_action_apply {β : CStarAlgebraAction Γ B}
    (U : EquivariantHilbertModule β M) (e : B ≃⋆ₐ[ℂ] C) (η : CStarAlgebraAction Γ C)
    (he : ∀ g b, e (β.automorphism g b) = η.automorphism g (e b))
    (g : Γ) (x : CoefficientChangedModule e M) :
    (U.coefficientChanged e η he).action g x = U.action g (x : M) := rfl

@[simp] theorem coefficientChanged_conjugateOperator {β : CStarAlgebraAction Γ B}
    (U : EquivariantHilbertModule β M) (e : B ≃⋆ₐ[ℂ] C) (η : CStarAlgebraAction Γ C)
    (he : ∀ g b, e (β.automorphism g b) = η.automorphism g (e b))
    (g : Γ) (T : AdjointableMap B M M) :
    (U.coefficientChanged e η he).conjugateOperator g (coefficientChangedOperator e T) =
      coefficientChangedOperator e (U.conjugateOperator g T) := by
  ext x
  rfl

end EquivariantHilbertModule

variable [CompleteSpace M]

/-- Coefficient transport preserves every actual localized compact defect. -/
def GradedKasparovCycle.coefficientChanged
    {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
    {δA : CStarGrading A} {δB : CStarGrading B}
    (c : GradedKasparovCycle α β δA δB M)
    (e : B ≃⋆ₐ[ℂ] C) (η : CStarAlgebraAction Γ C) (δC : CStarGrading C)
    (hact : ∀ g b, e (β.automorphism g b) = η.automorphism g (e b))
    (hgrade : ∀ b, e (δB.automorphism b) = δC.automorphism (e b)) :
    GradedKasparovCycle α η δA δC (CoefficientChangedModule e M) where
  sourceAction_preservesGrading := c.sourceAction_preservesGrading
  coefficientAction_preservesGrading g b := by
    obtain ⟨a, rfl⟩ := e.surjective b
    change η.automorphism g (δC.automorphism (e a)) =
      δC.automorphism (η.automorphism g (e a))
    rw [← hgrade, ← hact, c.coefficientAction_preservesGrading, hgrade, hact]
  countablyGenerated := c.countablyGenerated.coefficientChanged e
  grading := c.grading.coefficientChanged e δC hgrade
  groupAction := c.groupAction.coefficientChanged e η hact
  grading_preserved := c.grading_preserved
  representation := (coefficientChangedOperatorHom e).comp c.representation
  representation_graded := c.representation_graded
  representation_equivariant g a := by
    change (c.groupAction.coefficientChanged e η hact).conjugateOperator g
      (coefficientChangedOperator e (c.representation a)) = _
    rw [EquivariantHilbertModule.coefficientChanged_conjugateOperator,
      c.representation_equivariant]
    rfl
  operator := coefficientChangedOperator e c.operator
  operator_odd := c.operator_odd.coefficientChanged e δC hgrade
  selfadjoint_mod_compact a := by
    change IsModuleCompact ((coefficientChangedOperator e c.operator -
      star (coefficientChangedOperator e c.operator)) * coefficientChangedOperator e (c.representation a))
    rw [← coefficientChangedOperator_star, ← coefficientChangedOperator_sub,
      ← coefficientChangedOperator_mul]
    exact (c.selfadjoint_mod_compact a).coefficientChanged e
  square_mod_compact a := by
    change IsModuleCompact ((coefficientChangedOperator e c.operator *
      coefficientChangedOperator e c.operator - 1) * coefficientChangedOperator e (c.representation a))
    rw [← coefficientChangedOperator_mul, ← coefficientChangedOperator_one,
      ← coefficientChangedOperator_sub, ← coefficientChangedOperator_mul]
    exact (c.square_mod_compact a).coefficientChanged e
  commutator_compact a := by
    change IsModuleCompact (coefficientChangedOperator e c.operator *
      coefficientChangedOperator e (c.representation a) -
      coefficientChangedOperator e (c.representation (δA.automorphism a)) * coefficientChangedOperator e c.operator)
    rw [← coefficientChangedOperator_mul, ← coefficientChangedOperator_mul,
      ← coefficientChangedOperator_sub]
    exact (c.commutator_compact a).coefficientChanged e
  equivariance_mod_compact g a := by
    change IsModuleCompact (((c.groupAction.coefficientChanged e η hact).conjugateOperator g
      (coefficientChangedOperator e c.operator) - coefficientChangedOperator e c.operator) *
      coefficientChangedOperator e (c.representation a))
    rw [EquivariantHilbertModule.coefficientChanged_conjugateOperator,
      ← coefficientChangedOperator_sub, ← coefficientChangedOperator_mul]
    exact (c.equivariance_mod_compact g a).coefficientChanged e

end BC4lean.KKTheory
