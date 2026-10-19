import BC4lean.ReducedCrossedGradingOperators
import BC4lean.KasparovOperatorAlgebraActions
import BC4lean.ReducedCrossedNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The actual induced grading on the reduced crossed product

The actual coordinatewise coefficient grading on the regular Hilbert module
conjugates regular generators to regular generators when the action preserves
the coefficient grading. Closed-algebra minimality proves invariance of the
concrete reduced crossed product. Restricting this actual involutive operator
automorphism gives the induced C⋆-grading.

The underlying C⋆-algebra, operator norm, and separability instance are those of
`ReducedCrossedProduct α`; no new topology or norm is introduced here.
-/

noncomputable section
namespace BC4lean.KKTheory

private theorem starAlgEquiv_closed_comap {A : Type*} [NonUnitalCStarAlgebra A]
    (S : NonUnitalStarSubalgebra ℂ A) (ρ : A ≃⋆ₐ[ℂ] A)
    (hS : IsClosed (S : Set A)) :
    IsClosed (NonUnitalStarSubalgebra.comap ρ.toNonUnitalStarAlgHom S : Set A) :=
  hS.preimage (StarAlgEquiv.isometry ρ).continuous

variable {Γ B : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]

/-- Name the actual ambient automorphism, keeping its large module construction
out of the closed-algebra proof terms. -/
def reducedCrossedGradingConjugation (β : CStarGrading B) :
    AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ)
      ≃⋆ₐ[ℂ]
    AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ) :=
  (reducedCrossedHilbertGrading (Γ := Γ) β).conjugateOperatorStarAlgEquiv

/-- The inverse image of the actual reduced algebra under grading conjugation. -/
def reducedCrossedGradingPreimage (α : CStarAlgebraAction Γ B) (β : CStarGrading B) :
    NonUnitalStarSubalgebra ℂ
      (AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ)) :=
  NonUnitalStarSubalgebra.comap (reducedCrossedGradingConjugation (Γ := Γ) β).toNonUnitalStarAlgHom
    (reducedCrossedAlgebra α)

theorem mem_reducedCrossedGradingPreimage (α : CStarAlgebraAction Γ B) (β : CStarGrading B)
    (T : AdjointableMap B (ReducedCrossedHilbertModule B Γ)
      (ReducedCrossedHilbertModule B Γ)) :
    T ∈ reducedCrossedGradingPreimage α β ↔
      (reducedCrossedHilbertGrading (Γ := Γ) β).conjugateOperatorStarAlgEquiv T ∈
        reducedCrossedAlgebra α := Iff.rfl

theorem reducedCrossedGradingPreimage_isClosed (α : CStarAlgebraAction Γ B)
    (β : CStarGrading B) :
    IsClosed (reducedCrossedGradingPreimage α β : Set (AdjointableMap B
      (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ))) :=
  starAlgEquiv_closed_comap (reducedCrossedAlgebra α)
    (reducedCrossedGradingConjugation (Γ := Γ) β) (reducedCrossedAlgebra_isClosed α)

theorem reducedCrossedAlgebra_le_gradingPreimage (α : CStarAlgebraAction Γ B)
    (β : CStarGrading B) (hα : α.PreservesGrading β) :
    reducedCrossedAlgebra α ≤ reducedCrossedGradingPreimage α β := by
  apply reducedCrossedAlgebra_minimal α (reducedCrossedGradingPreimage α β)
    (reducedCrossedGradingPreimage_isClosed α β)
  intro b g
  apply (mem_reducedCrossedGradingPreimage α β _).mpr
  rw [reducedCrossedGrading_generator α β hα b g]
  exact reducedCrossedGenerator_mem α (β.automorphism b) g

/-- Actual grading conjugation preserves the operator-norm closed crossed product. -/
theorem reducedCrossedGrading_mem (α : CStarAlgebraAction Γ B)
    (β : CStarGrading B) (hα : α.PreservesGrading β)
    (T : AdjointableMap B (ReducedCrossedHilbertModule B Γ)
      (ReducedCrossedHilbertModule B Γ)) (hT : T ∈ reducedCrossedAlgebra α) :
    (reducedCrossedHilbertGrading (Γ := Γ) β).conjugateOperatorStarAlgEquiv T ∈
      reducedCrossedAlgebra α := by
  exact (mem_reducedCrossedGradingPreimage α β T).mp
    (reducedCrossedAlgebra_le_gradingPreimage α β hα hT)

/-- The inverse grading conjugation also preserves the actual closed algebra. -/
theorem reducedCrossedGrading_symm_mem (α : CStarAlgebraAction Γ B)
    (β : CStarGrading B) (hα : α.PreservesGrading β)
    (T : AdjointableMap B (ReducedCrossedHilbertModule B Γ)
      (ReducedCrossedHilbertModule B Γ)) (hT : T ∈ reducedCrossedAlgebra α) :
    (reducedCrossedHilbertGrading (Γ := Γ) β).conjugateOperatorStarAlgEquiv.symm T ∈
      reducedCrossedAlgebra α := by
  change (reducedCrossedHilbertGrading (Γ := Γ) β).conjugateOperator T ∈
    reducedCrossedAlgebra α
  exact reducedCrossedGrading_mem α β hα T hT

/-- Restrict the actual grading conjugation, with its actual inverse restriction. -/
def reducedCrossedProductGradingAutomorphism (α : CStarAlgebraAction Γ B)
    (β : CStarGrading B) (hα : α.PreservesGrading β) :
    ReducedCrossedProduct α ≃⋆ₐ[ℂ] ReducedCrossedProduct α :=
  restrictStarAlgEquiv (reducedCrossedAlgebra α)
    (reducedCrossedHilbertGrading (Γ := Γ) β).conjugateOperatorStarAlgEquiv
    (reducedCrossedGrading_mem α β hα) (reducedCrossedGrading_symm_mem α β hα)

@[simp] theorem reducedCrossedProductGradingAutomorphism_coe
    (α : CStarAlgebraAction Γ B) (β : CStarGrading B) (hα : α.PreservesGrading β)
    (T : ReducedCrossedProduct α) :
    (reducedCrossedProductGradingAutomorphism α β hα T :
      AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ)) =
      (reducedCrossedHilbertGrading (Γ := Γ) β).conjugateOperatorStarAlgEquiv T := rfl

/-- The induced grading on the actual reduced crossed-product C⋆-algebra. -/
def reducedCrossedProductGrading (α : CStarAlgebraAction Γ B)
    (β : CStarGrading B) (hα : α.PreservesGrading β) :
    CStarGrading (ReducedCrossedProduct α) where
  automorphism := reducedCrossedProductGradingAutomorphism α β hα
  involutive T := by
    apply Subtype.ext
    change (reducedCrossedHilbertGrading (Γ := Γ) β).conjugateOperator
      ((reducedCrossedHilbertGrading (Γ := Γ) β).conjugateOperator T) = T
    exact (reducedCrossedHilbertGrading (Γ := Γ) β).conjugateOperator_involutive T

@[simp] theorem reducedCrossedProductGrading_coe (α : CStarAlgebraAction Γ B)
    (β : CStarGrading B) (hα : α.PreservesGrading β) (T : ReducedCrossedProduct α) :
    ((reducedCrossedProductGrading α β hα).automorphism T :
      AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ)) =
      (reducedCrossedHilbertGrading (Γ := Γ) β).conjugateOperatorStarAlgEquiv T := rfl

/-- The actual coefficient embedding intertwines the coefficient and crossed-product gradings. -/
@[simp] theorem reducedCrossedProductGrading_coefficient (α : CStarAlgebraAction Γ B)
    (β : CStarGrading B) (hα : α.PreservesGrading β) (b : B) :
    (reducedCrossedProductGrading α β hα).automorphism (coefficientToReducedCrossed α b) =
      coefficientToReducedCrossed α (β.automorphism b) := by
  apply Subtype.ext
  simpa only [reducedCrossedProductGrading_coe, coefficientToReducedCrossed_coe] using
    reducedCrossedGrading_coefficient α β hα b

/-- On each actual regular generator, the induced grading changes only its coefficient. -/
@[simp] theorem reducedCrossedProductGrading_generator (α : CStarAlgebraAction Γ B)
    (β : CStarGrading B) (hα : α.PreservesGrading β) (b : B) (g : Γ) :
    ((reducedCrossedProductGrading α β hα).automorphism
      ⟨reducedCrossedGenerator α b g, reducedCrossedGenerator_mem α b g⟩ :
        AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ)) =
      reducedCrossedGenerator α (β.automorphism b) g := by
  exact reducedCrossedGrading_generator α β hα b g

/-- The induced grading is an isometry for the existing reduced norm. -/
theorem reducedCrossedProductGrading_isometry (α : CStarAlgebraAction Γ B)
    (β : CStarGrading B) (hα : α.PreservesGrading β) :
    Isometry (reducedCrossedProductGrading α β hα).automorphism :=
  NonUnitalStarAlgHom.isometry (reducedCrossedProductGrading α β hα).automorphism
    (reducedCrossedProductGrading α β hα).automorphism.injective

@[simp] theorem reducedCrossedProductGrading_norm (α : CStarAlgebraAction Γ B)
    (β : CStarGrading B) (hα : α.PreservesGrading β) (T : ReducedCrossedProduct α) :
    ‖(reducedCrossedProductGrading α β hα).automorphism T‖ = ‖T‖ :=
  NonUnitalStarAlgHom.norm_map (reducedCrossedProductGrading α β hα).automorphism
    (reducedCrossedProductGrading α β hα).automorphism.injective T

/-- Trivial coefficient grading induces the identity on the actual reduced crossed product. -/
@[simp] theorem reducedCrossedProductGrading_trivial_apply (α : CStarAlgebraAction Γ B)
    (T : ReducedCrossedProduct α) :
    (reducedCrossedProductGrading α CStarGrading.trivial α.preservesGrading_trivial).automorphism T =
      T := by
  apply Subtype.ext
  change (reducedCrossedHilbertGrading (Γ := Γ) (CStarGrading.trivial : CStarGrading B)).conjugateOperator T = T
  ext x
  simp only [GradedHilbertModule.conjugateOperator_apply,
    reducedCrossedHilbertGrading_trivial_apply]

/-- The induced grading from an ungraded coefficient algebra is exactly the trivial grading. -/
@[simp] theorem reducedCrossedProductGrading_trivial (α : CStarAlgebraAction Γ B) :
    reducedCrossedProductGrading α CStarGrading.trivial α.preservesGrading_trivial =
      (CStarGrading.trivial : CStarGrading (ReducedCrossedProduct α)) := by
  have hinj : Function.Injective
      (fun γ : CStarGrading (ReducedCrossedProduct α) => γ.automorphism) := by
    rintro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ he
    cases he
    rfl
  apply hinj
  apply StarAlgEquiv.ext
  intro T
  exact reducedCrossedProductGrading_trivial_apply α T

end BC4lean.KKTheory
