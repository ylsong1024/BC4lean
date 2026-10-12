import BC4lean.GradedCycleCoefficientEquiv
import BC4lean.GradedIntervalKasparovFibre
import BC4lean.IntervalModuleFibreNorm

/-! # Coefficient star equivalences commute with genuine evaluated fibres

Continuous coefficients are changed pointwise. The original canonical fibre
evaluation, now read with the changed coefficient-valued inner product,
constructs an actual surjective form-preserving evaluation. Its completed
fibre unitary intertwines the entire graded cycle.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {Γ A B C X : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- An actual coefficient equivalence acts pointwise on continuous functions,
including when its source and target algebras are different. -/
def continuousCoefficientStarAlgEquiv (e : B ≃⋆ₐ[ℂ] C) : C(X, B) ≃⋆ₐ[ℂ] C(X, C) where
  toFun b := ⟨fun t => e (b t), (StarAlgEquiv.isometry e).continuous.comp b.continuous⟩
  invFun c := ⟨fun t => e.symm (c t), (StarAlgEquiv.isometry e.symm).continuous.comp c.continuous⟩
  left_inv b := by ext t; exact e.symm_apply_apply (b t)
  right_inv c := by ext t; exact e.apply_symm_apply (c t)
  map_add' b c := by ext t; exact e.map_add (b t) (c t)
  map_mul' b c := by ext t; exact e.map_mul (b t) (c t)
  map_star' b := by ext t; exact map_star e (b t)
  map_smul' z b := by ext t; exact map_smul e z (b t)

omit [CompactSpace X] [T2Space X] in
@[simp] theorem continuousCoefficientStarAlgEquiv_apply (e : B ≃⋆ₐ[ℂ] C)
    (b : C(X, B)) (t : X) : continuousCoefficientStarAlgEquiv e b t = e (b t) := rfl

def GradedCoefficientEquiv.continuousSections
    {β : CStarAlgebraAction Γ B} {η : CStarAlgebraAction Γ C}
    {δB : CStarGrading B} {δC : CStarGrading C}
    (e : GradedCoefficientEquiv β δB η δC) :
    GradedCoefficientEquiv (β.continuousSections (X := X)) δB.continuousSections
      (η.continuousSections (X := X)) δC.continuousSections where
  starAlgEquiv := continuousCoefficientStarAlgEquiv e.starAlgEquiv
  action_intertwine g b := by ext t; exact e.action_intertwine g (b t)
  grading_intertwine b := by ext t; exact e.grading_intertwine (b t)

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

/-- Evaluate the unchanged vector and change its actual fibre coefficients. -/
def coefficientChangedFibreEvaluation (e : B ≃⋆ₐ[ℂ] C) (t : X) :
    CoefficientChangedModule (continuousCoefficientStarAlgEquiv (X := X) e) M →L[ℂ]
      CoefficientChangedModule e (HilbertModuleFibre B M t) :=
  hilbertModuleFibreMk (B := B) (M := M) t

omit [T2Space X] [CompleteSpace M] in
theorem coefficientChangedFibreEvaluation_inner (e : B ≃⋆ₐ[ℂ] C) (t : X)
    (x y : CoefficientChangedModule (continuousCoefficientStarAlgEquiv (X := X) e) M) :
    ⟪coefficientChangedFibreEvaluation e t x, coefficientChangedFibreEvaluation e t y⟫_(Cᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪x, y⟫_(C(X, C)ᵐᵒᵖ) t) := by
  change opStarAlgEquivBetween e
    ⟪hilbertModuleFibreMk (B := B) (M := M) t
        (coefficientChangedToOriginal (M := M)
          (continuousCoefficientStarAlgEquiv (X := X) e) x),
      hilbertModuleFibreMk (B := B) (M := M) t
        (coefficientChangedToOriginal (M := M)
          (continuousCoefficientStarAlgEquiv (X := X) e) y)⟫_(Bᵐᵒᵖ) = _
  rw [hilbertModuleFibre_inner_mk]
  rfl

/-- The actual coefficient-changed fibre is unitarily the coefficient change
of the original completed fibre. Surjectivity is the proved Banach-quotient
surjectivity of the genuine canonical evaluation map. -/
def coefficientChangedFibreEquiv (e : B ≃⋆ₐ[ℂ] C) (t : X) :
    HilbertModuleEquiv C
      (HilbertModuleFibre C
        (CoefficientChangedModule (continuousCoefficientStarAlgEquiv (X := X) e) M) t)
      (CoefficientChangedModule e (HilbertModuleFibre B M t)) :=
  hilbertModuleFibreEquivOfEvaluation t (coefficientChangedFibreEvaluation e t)
    (coefficientChangedFibreEvaluation_inner e t)
    (hilbertModuleFibreMk_surjective (B := B) (M := M) t)

@[simp] theorem coefficientChangedFibreEquiv_mk (e : B ≃⋆ₐ[ℂ] C) (t : X)
    (x : CoefficientChangedModule (continuousCoefficientStarAlgEquiv (X := X) e) M) :
    coefficientChangedFibreEquiv e t (hilbertModuleFibreMk (B := C) t x) =
      coefficientChangedFibreEvaluation e t x :=
  hilbertModuleFibreEquivOfEvaluation_mk t _ _ _ x

private theorem coefficientChangedCanonicalFibreMk_surjective
    (e : B ≃⋆ₐ[ℂ] C) (t : X) :
    Function.Surjective (hilbertModuleFibreMk (X := X) (B := C)
      (M := CoefficientChangedModule (continuousCoefficientStarAlgEquiv (X := X) e) M) t) :=
  @hilbertModuleFibreMk_surjective C X
    (CoefficientChangedModule (continuousCoefficientStarAlgEquiv (X := X) e) M)
    _ _ _ _ _ _
    (coefficientChangedNormedAddCommGroup (M := M)
      (continuousCoefficientStarAlgEquiv (X := X) e))
    (coefficientChangedNormedSpace (M := M)
      (continuousCoefficientStarAlgEquiv (X := X) e))
    (coefficientChangedSMul (M := M)
      (continuousCoefficientStarAlgEquiv (X := X) e))
    (coefficientChangedCStarModule (M := M)
      (continuousCoefficientStarAlgEquiv (X := X) e))
    (coefficientChangedCompleteSpace (M := M)
      (continuousCoefficientStarAlgEquiv (X := X) e)) t

variable {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {η : CStarAlgebraAction Γ C} {δA : CStarGrading A}
  {δB : CStarGrading B} {δC : CStarGrading C}

set_option maxHeartbeats 800000 in
/-- This genuine fibre unitary intertwines grading, group action,
representation and Fredholm operator at the same parameter. -/
def GradedKasparovCycle.changeCoefficientsFibreIso
    (c : GradedKasparovCycle α (β.continuousSections (X := X))
      δA δB.continuousSections M) (e : GradedCoefficientEquiv β δB η δC) (t : X) :
    GradedKasparovCycleIso ((c.changeCoefficients e.continuousSections).fibre t)
      ((c.fibre t).changeCoefficients e) := by
  let u : HilbertModuleEquiv C
      (HilbertModuleFibre C
        (CoefficientChangedModule
          (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv) M) t)
      (CoefficientChangedModule e.starAlgEquiv (HilbertModuleFibre B M t)) :=
    coefficientChangedFibreEquiv e.starAlgEquiv t
  have hu (x : CoefficientChangedModule
      (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv) M) :
      u (hilbertModuleFibreMk (B := C) t x) =
        coefficientChangedFibreEvaluation e.starAlgEquiv t x :=
    coefficientChangedFibreEquiv_mk (B := B) (C := C) (X := X) (M := M)
      e.starAlgEquiv t x
  refine
    { moduleEquiv := u
      grading_intertwine := ?_
      action_intertwine := ?_
      representation_intertwine := ?_
      operator_intertwine := ?_ }
  · intro z
    let : NormedAddCommGroup
        (CoefficientChangedModule (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv) M) :=
      coefficientChangedNormedAddCommGroup (M := M)
        (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv)
    let : NormedSpace ℂ
        (CoefficientChangedModule (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv) M) :=
      coefficientChangedNormedSpace (M := M)
        (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv)
    let : SMul C(X, C)ᵐᵒᵖ
        (CoefficientChangedModule (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv) M) :=
      coefficientChangedSMul (M := M)
        (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv)
    let : CStarModule C(X, C)ᵐᵒᵖ
        (CoefficientChangedModule (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv) M) :=
      coefficientChangedCStarModule (M := M)
        (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv)
    let : CompleteSpace
        (CoefficientChangedModule (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv) M) :=
      coefficientChangedCompleteSpace (M := M)
        (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv)
    obtain ⟨x, rfl⟩ := coefficientChangedCanonicalFibreMk_surjective e.starAlgEquiv t z
    rw (config := { transparency := .all })
      [(c.changeCoefficients e.continuousSections).fibre_grading_mk t x,
      hu, hu]
    exact (c.fibre_grading_mk t (coefficientChangedToOriginal (M := M)
      (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv) x)).symm
  · intro g z
    let : NormedAddCommGroup
        (CoefficientChangedModule (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv) M) :=
      coefficientChangedNormedAddCommGroup (M := M)
        (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv)
    let : NormedSpace ℂ
        (CoefficientChangedModule (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv) M) :=
      coefficientChangedNormedSpace (M := M)
        (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv)
    let : SMul C(X, C)ᵐᵒᵖ
        (CoefficientChangedModule (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv) M) :=
      coefficientChangedSMul (M := M)
        (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv)
    let : CStarModule C(X, C)ᵐᵒᵖ
        (CoefficientChangedModule (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv) M) :=
      coefficientChangedCStarModule (M := M)
        (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv)
    let : CompleteSpace
        (CoefficientChangedModule (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv) M) :=
      coefficientChangedCompleteSpace (M := M)
        (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv)
    obtain ⟨x, rfl⟩ := coefficientChangedCanonicalFibreMk_surjective e.starAlgEquiv t z
    rw (config := { transparency := .all })
      [(c.changeCoefficients e.continuousSections).fibre_action_mk t g x,
      hu, hu]
    exact (c.fibre_action_mk t g (coefficientChangedToOriginal (M := M)
      (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv) x)).symm
  · intro a z
    let : NormedAddCommGroup
        (CoefficientChangedModule (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv) M) :=
      coefficientChangedNormedAddCommGroup (M := M)
        (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv)
    let : NormedSpace ℂ
        (CoefficientChangedModule (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv) M) :=
      coefficientChangedNormedSpace (M := M)
        (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv)
    let : SMul C(X, C)ᵐᵒᵖ
        (CoefficientChangedModule (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv) M) :=
      coefficientChangedSMul (M := M)
        (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv)
    let : CStarModule C(X, C)ᵐᵒᵖ
        (CoefficientChangedModule (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv) M) :=
      coefficientChangedCStarModule (M := M)
        (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv)
    let : CompleteSpace
        (CoefficientChangedModule (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv) M) :=
      coefficientChangedCompleteSpace (M := M)
        (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv)
    obtain ⟨x, rfl⟩ := coefficientChangedCanonicalFibreMk_surjective e.starAlgEquiv t z
    rw (config := { transparency := .all })
      [(c.changeCoefficients e.continuousSections).fibre_representation_mk t a x,
      hu, hu]
    exact (c.fibre_representation_mk t a (coefficientChangedToOriginal (M := M)
      (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv) x)).symm
  · intro z
    let : NormedAddCommGroup
        (CoefficientChangedModule (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv) M) :=
      coefficientChangedNormedAddCommGroup (M := M)
        (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv)
    let : NormedSpace ℂ
        (CoefficientChangedModule (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv) M) :=
      coefficientChangedNormedSpace (M := M)
        (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv)
    let : SMul C(X, C)ᵐᵒᵖ
        (CoefficientChangedModule (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv) M) :=
      coefficientChangedSMul (M := M)
        (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv)
    let : CStarModule C(X, C)ᵐᵒᵖ
        (CoefficientChangedModule (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv) M) :=
      coefficientChangedCStarModule (M := M)
        (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv)
    let : CompleteSpace
        (CoefficientChangedModule (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv) M) :=
      coefficientChangedCompleteSpace (M := M)
        (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv)
    obtain ⟨x, rfl⟩ := coefficientChangedCanonicalFibreMk_surjective e.starAlgEquiv t z
    rw (config := { transparency := .all })
      [(c.changeCoefficients e.continuousSections).fibre_operator_mk t x,
      hu, hu]
    exact (c.fibre_operator_mk t (coefficientChangedToOriginal (M := M)
      (continuousCoefficientStarAlgEquiv (X := X) e.starAlgEquiv) x)).symm

end BC4lean.KKTheory
