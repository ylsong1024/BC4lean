import BC4lean.ReducedCrossedHilbertModule
import BC4lean.StandardHilbertModuleActions

/-! # The actual coordinate grading of the regular coefficient module

A coefficient grading acts on each finite coefficient coordinate. The actual
coefficient-valued finite form transforms by the coefficient automorphism,
so its form norm is preserved. The map therefore descends to the radical
quotient and extends to the genuine Hilbert-module completion. Its square and
inner-product laws are inherited through the dense canonical finite vectors.
-/

noncomputable section
namespace BC4lean.KKTheory

open UniformSpace
open scoped InnerProductSpace

variable {Γ B : Type*} [NonUnitalCStarAlgebra B]

/-- Apply the coefficient grading at every finitely supported coordinate. -/
def reducedCrossedFiniteGradingLinear (β : CStarGrading B) :
    ReducedCrossedVectors B Γ →ₗ[ℂ] ReducedCrossedVectors B Γ :=
  Finsupp.mapRange.linearMap
    (starAlgEquivLinearIsometry (opStarAlgEquiv β.automorphism)).toLinearEquiv.toLinearMap

@[simp] theorem reducedCrossedFiniteGradingLinear_apply (β : CStarGrading B)
    (x : ReducedCrossedVectors B Γ) (i : Γ) :
    reducedCrossedFiniteGradingLinear β x i = opStarAlgEquiv β.automorphism (x i) := rfl

@[simp] theorem reducedCrossedFiniteGradingLinear_single (β : CStarGrading B)
    (i : Γ) (b : Bᵐᵒᵖ) :
    reducedCrossedFiniteGradingLinear β (Finsupp.single i b) =
      Finsupp.single i (opStarAlgEquiv β.automorphism b) :=
  Finsupp.mapRange_single (hf := map_zero (opStarAlgEquiv β.automorphism))

theorem reducedCrossedFiniteGradingLinear_support_subset (β : CStarGrading B)
    (x : ReducedCrossedVectors B Γ) :
    (reducedCrossedFiniteGradingLinear β x).support ⊆ x.support :=
  Finsupp.support_mapRange (hf := map_zero (opStarAlgEquiv β.automorphism))

@[simp] theorem reducedCrossedFiniteGradingLinear_involutive (β : CStarGrading B)
    (x : ReducedCrossedVectors B Γ) :
    reducedCrossedFiniteGradingLinear β (reducedCrossedFiniteGradingLinear β x) = x := by
  ext i
  simp only [reducedCrossedFiniteGradingLinear_apply, CStarGrading.op_automorphism_sq]

@[simp] theorem reducedCrossedFiniteGradingLinear_trivial (x : ReducedCrossedVectors B Γ) :
    reducedCrossedFiniteGradingLinear (CStarGrading.trivial : CStarGrading B) x = x := by
  ext i
  simp only [reducedCrossedFiniteGradingLinear_apply, CStarGrading.op_trivial_apply]

variable [PartialOrder B] [StarOrderedRing B]

/-- Coordinate grading transforms the actual finite coefficient-valued form. -/
theorem reducedCrossedFiniteGradingLinear_inner (β : CStarGrading B)
    (x y : ReducedCrossedVectors B Γ) :
    reducedCrossedFiniteInner (reducedCrossedFiniteGradingLinear β x)
      (reducedCrossedFiniteGradingLinear β y) =
      opStarAlgEquiv β.automorphism (reducedCrossedFiniteInner x y) := by
  classical
  rw [reducedCrossedFiniteInner_eq_sum _ _ x.support
    (reducedCrossedFiniteGradingLinear_support_subset β x),
    reducedCrossedFiniteInner_eq_sum x y x.support Finset.Subset.rfl, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [reducedCrossedFiniteGradingLinear_apply]
  exact (GradedHilbertModule.standard β).inner_grading (x i) (y i)

/-- The genuine coefficient-form norm is invariant under coordinate grading. -/
theorem reducedCrossedFiniteGradingLinear_formNorm (β : CStarGrading B)
    (x : ReducedCrossedVectors B Γ) :
    PositiveModuleForm.formNorm (B := B) (reducedCrossedFiniteGradingLinear β x) =
      PositiveModuleForm.formNorm (B := B) x := by
  rw [PositiveModuleForm.formNorm, reducedCrossedFinite_inner,
    reducedCrossedFiniteGradingLinear_inner,
    StarAlgEquiv.norm_map (opStarAlgEquiv β.automorphism)]
  rfl

/-- The form isometry descends to the actual finite-vector radical quotient. -/
def reducedCrossedGradingPreCLM (β : CStarGrading B) :
    ReducedCrossedPreModule B Γ →L[ℂ] ReducedCrossedPreModule B Γ :=
  positiveModuleQuotientLiftCLM (reducedCrossedFiniteGradingLinear β) (K := 1)
    (fun x => by rw [reducedCrossedFiniteGradingLinear_formNorm, one_mul])

@[simp] theorem reducedCrossedGradingPreCLM_mk (β : CStarGrading B)
    (x : ReducedCrossedVectors B Γ) :
    reducedCrossedGradingPreCLM β (positiveModuleQuotientMk (B := B) x) =
      positiveModuleQuotientMk (B := B) (reducedCrossedFiniteGradingLinear β x) :=
  positiveModuleQuotientLiftCLM_mk _ _ x

/-- Extend the actual quotient grading to the completed regular coefficient module. -/
def reducedCrossedGradingCLM (β : CStarGrading B) :
    ReducedCrossedHilbertModule B Γ →L[ℂ] ReducedCrossedHilbertModule B Γ :=
  (reducedCrossedGradingPreCLM β).completion

@[simp] theorem reducedCrossedGradingCLM_mk (β : CStarGrading B)
    (x : ReducedCrossedVectors B Γ) :
    reducedCrossedGradingCLM β (reducedCrossedMk x) =
      reducedCrossedMk (reducedCrossedFiniteGradingLinear β x) := by
  rw [reducedCrossedGradingCLM, reducedCrossedMk_apply,
    ContinuousLinearMap.completion_apply_coe, reducedCrossedGradingPreCLM_mk]
  rfl

/-- The completed map transforms the actual coefficient-valued inner product. -/
theorem reducedCrossedGradingCLM_inner (β : CStarGrading B)
    (x y : ReducedCrossedHilbertModule B Γ) :
    ⟪reducedCrossedGradingCLM β x, reducedCrossedGradingCLM β y⟫_(Bᵐᵒᵖ) =
      opStarAlgEquiv β.automorphism ⟪x, y⟫_(Bᵐᵒᵖ) := by
  have he := (reducedCrossedMk_denseRange (B := B) (Γ := Γ)).prodMap
    (reducedCrossedMk_denseRange (B := B) (Γ := Γ)) |>.equalizer
    (CStarModule.continuous_inner.comp
      ((reducedCrossedGradingCLM β).continuous.comp continuous_fst |>.prodMk
        ((reducedCrossedGradingCLM β).continuous.comp continuous_snd)))
    ((StarAlgEquiv.isometry (opStarAlgEquiv β.automorphism)).continuous.comp
      CStarModule.continuous_inner)
    (by
      funext w
      change ⟪reducedCrossedGradingCLM β (reducedCrossedMk w.1),
        reducedCrossedGradingCLM β (reducedCrossedMk w.2)⟫_(Bᵐᵒᵖ) =
        opStarAlgEquiv β.automorphism ⟪reducedCrossedMk w.1, reducedCrossedMk w.2⟫_(Bᵐᵒᵖ)
      simp only [reducedCrossedGradingCLM_mk, reducedCrossedMk_inner,
        reducedCrossedFiniteGradingLinear_inner])
  exact congrFun he (x, y)

/-- The completed coordinate grading has square the identity. -/
theorem reducedCrossedGradingCLM_involutive (β : CStarGrading B) :
    Function.Involutive (reducedCrossedGradingCLM (Γ := Γ) β) := by
  have he := (reducedCrossedMk_denseRange (B := B) (Γ := Γ)).equalizer
    ((reducedCrossedGradingCLM β).continuous.comp (reducedCrossedGradingCLM β).continuous)
    continuous_id (by
      funext x
      change reducedCrossedGradingCLM β
        (reducedCrossedGradingCLM β (reducedCrossedMk x)) = reducedCrossedMk x
      simp only [reducedCrossedGradingCLM_mk, reducedCrossedFiniteGradingLinear_involutive])
  exact congrFun he

/-- Coordinate grading is an isometry for the actual completed module norm. -/
@[simp] theorem reducedCrossedGradingCLM_norm (β : CStarGrading B)
    (x : ReducedCrossedHilbertModule B Γ) : ‖reducedCrossedGradingCLM β x‖ = ‖x‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ),
    reducedCrossedGradingCLM_inner, StarAlgEquiv.norm_map (opStarAlgEquiv β.automorphism)]
  exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm

/-- The regular coefficient Hilbert module with its actual coordinatewise grading. -/
def reducedCrossedHilbertGrading (β : CStarGrading B) :
    GradedHilbertModule β (ReducedCrossedHilbertModule B Γ) where
  grading :=
    { toLinearEquiv :=
        { toLinearMap := (reducedCrossedGradingCLM β).toLinearMap
          invFun := reducedCrossedGradingCLM β
          left_inv := reducedCrossedGradingCLM_involutive β
          right_inv := reducedCrossedGradingCLM_involutive β }
      norm_map' := reducedCrossedGradingCLM_norm β }
  involutive := reducedCrossedGradingCLM_involutive β
  inner_grading := reducedCrossedGradingCLM_inner β

@[simp] theorem reducedCrossedHilbertGrading_mk (β : CStarGrading B)
    (x : ReducedCrossedVectors B Γ) :
    (reducedCrossedHilbertGrading β).grading (reducedCrossedMk x) =
      reducedCrossedMk (reducedCrossedFiniteGradingLinear β x) :=
  reducedCrossedGradingCLM_mk β x

@[simp] theorem reducedCrossedHilbertGrading_sq (β : CStarGrading B)
    (x : ReducedCrossedHilbertModule B Γ) :
    (reducedCrossedHilbertGrading β).grading ((reducedCrossedHilbertGrading β).grading x) = x :=
  (reducedCrossedHilbertGrading β).grading_sq x

theorem reducedCrossedHilbertGrading_inner (β : CStarGrading B)
    (x y : ReducedCrossedHilbertModule B Γ) :
    ⟪(reducedCrossedHilbertGrading β).grading x,
      (reducedCrossedHilbertGrading β).grading y⟫_(Bᵐᵒᵖ) =
      opStarAlgEquiv β.automorphism ⟪x, y⟫_(Bᵐᵒᵖ) :=
  (reducedCrossedHilbertGrading β).inner_grading x y

/-- Evaluation reads the coefficient grading at the same actual coordinate. -/
@[simp] theorem reducedCrossedEvaluation_hilbertGrading (β : CStarGrading B)
    (i : Γ) (x : ReducedCrossedHilbertModule B Γ) :
    reducedCrossedEvaluation i ((reducedCrossedHilbertGrading β).grading x) =
      opStarAlgEquiv β.automorphism (reducedCrossedEvaluation i x) := by
  have he := (reducedCrossedMk_denseRange (B := B) (Γ := Γ)).equalizer
    ((reducedCrossedEvaluation (B := B) i).toCLM.continuous.comp
      (reducedCrossedGradingCLM β).continuous)
    ((StarAlgEquiv.isometry (opStarAlgEquiv β.automorphism)).continuous.comp
      (reducedCrossedEvaluation (B := B) i).toCLM.continuous) (by
      funext y
      change reducedCrossedEvaluation i (reducedCrossedGradingCLM β (reducedCrossedMk y)) =
        opStarAlgEquiv β.automorphism (reducedCrossedEvaluation i (reducedCrossedMk y))
      simp only [reducedCrossedGradingCLM_mk, reducedCrossedEvaluation_mk,
        reducedCrossedFiniteGradingLinear_apply])
  exact congrFun he x

/-- The actual coordinate inclusion intertwines the coefficient and module gradings. -/
@[simp] theorem reducedCrossedHilbertGrading_inclusion (β : CStarGrading B)
    (i : Γ) (b : Bᵐᵒᵖ) :
    (reducedCrossedHilbertGrading β).grading (reducedCrossedInclusion i b) =
      reducedCrossedInclusion i (opStarAlgEquiv β.automorphism b) := by
  rw [reducedCrossedInclusion_apply, reducedCrossedHilbertGrading_mk,
    reducedCrossedFiniteGradingLinear_single, reducedCrossedInclusion_apply]

/-- Trivial coefficient grading gives the identity on the full completed module. -/
@[simp] theorem reducedCrossedHilbertGrading_trivial_apply
    (x : ReducedCrossedHilbertModule B Γ) :
    (reducedCrossedHilbertGrading (Γ := Γ) (CStarGrading.trivial : CStarGrading B)).grading x = x := by
  refine (reducedCrossedMk_denseRange (B := B) (Γ := Γ)).induction_on x ?_ ?_
  · exact isClosed_eq
      (reducedCrossedHilbertGrading (Γ := Γ) (CStarGrading.trivial : CStarGrading B)).grading.continuous
      continuous_id
  · intro y
    rw [reducedCrossedHilbertGrading_mk, reducedCrossedFiniteGradingLinear_trivial]

private theorem reducedCrossedHilbertGrading_ext {β : CStarGrading B}
    (J K : GradedHilbertModule β (ReducedCrossedHilbertModule B Γ))
    (h : J.grading = K.grading) : J = K := by
  cases J
  cases K
  cases h
  rfl

/-- The bundled grading itself specializes to the existing trivial module grading. -/
@[simp] theorem reducedCrossedHilbertGrading_trivial :
    reducedCrossedHilbertGrading (Γ := Γ) (CStarGrading.trivial : CStarGrading B) =
      (GradedHilbertModule.trivial :
        GradedHilbertModule (CStarGrading.trivial : CStarGrading B)
          (ReducedCrossedHilbertModule B Γ)) := by
  apply reducedCrossedHilbertGrading_ext
  apply LinearIsometryEquiv.ext
  intro x
  exact reducedCrossedHilbertGrading_trivial_apply x

end BC4lean.KKTheory
