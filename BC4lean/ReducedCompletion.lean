import BC4lean.ReducedNormGroupAlgebra
import Mathlib.Analysis.Normed.Module.Completion

/-! # The abstract reduced-norm completion and its concrete realization

The source is Mathlib's uniform completion of the reduced-norm group algebra.
Its ring, complex module and algebra operations are the standard completion
operations. Its star is `Completion.map star`, not a transported operation.
-/

noncomputable section
namespace BC4lean
open UniformSpace

variable (Γ : Type*) [Group Γ]

/-- Abstract norm completion of the complex group algebra with reduced norm. -/
abbrev ReducedCompletion := Completion (ReducedNormGroupAlgebra Γ)

/-- Continuous extension of the canonical ring homomorphism. -/
def completionMap : ReducedCompletion Γ →+* ReducedGroupCStar Γ :=
  Completion.extensionHom (ReducedNormGroupAlgebra.toReduced Γ).toAlgHom.toRingHom
    (ReducedNormGroupAlgebra.toReduced_isometry Γ).continuous

@[simp] theorem completionMap_coe (a : ReducedNormGroupAlgebra Γ) :
    completionMap Γ (a : ReducedCompletion Γ) = ReducedNormGroupAlgebra.toReduced Γ a :=
  Completion.extensionHom_coe _ _ a

theorem completionMap_isometry : Isometry (completionMap Γ) :=
  (ReducedNormGroupAlgebra.toReduced_isometry Γ).completion_extension

theorem completionMap_injective : Function.Injective (completionMap Γ) :=
  (completionMap_isometry Γ).injective

@[simp] theorem norm_completionMap (x : ReducedCompletion Γ) :
    ‖completionMap Γ x‖ = ‖x‖ := by
  simpa only [map_zero, dist_zero_right] using (completionMap_isometry Γ).dist_eq x 0

theorem completionMap_surjective : Function.Surjective (completionMap Γ) := by
  intro T
  have hsubset : Set.range (ReducedNormGroupAlgebra.toReduced Γ) ⊆
      Set.range (completionMap Γ) := by
    rintro _ ⟨a, rfl⟩
    exact ⟨(a : ReducedCompletion Γ), completionMap_coe Γ a⟩
  have h := closure_mono hsubset (ReducedNormGroupAlgebra.toReduced_denseRange Γ T)
  rwa [(completionMap_isometry Γ).isClosedEmbedding.isClosed_range.closure_eq] at h

/-- Complex-linearity of the canonical extension. -/
def completionAlgHom : ReducedCompletion Γ →ₐ[ℂ] ReducedGroupCStar Γ where
  toRingHom := completionMap Γ
  commutes' z := by
    change completionMap Γ ((algebraMap ℂ (ReducedNormGroupAlgebra Γ) z :
      ReducedNormGroupAlgebra Γ) : ReducedCompletion Γ) = _
    rw [completionMap_coe]
    exact (ReducedNormGroupAlgebra.toReduced Γ).commutes z

instance completionStar : Star (ReducedCompletion Γ) :=
  ⟨Completion.map (star : ReducedNormGroupAlgebra Γ → ReducedNormGroupAlgebra Γ)⟩

@[simp] theorem completion_star_coe (a : ReducedNormGroupAlgebra Γ) :
    star (a : ReducedCompletion Γ) = (star a : ReducedNormGroupAlgebra Γ) :=
  Completion.map_coe star_isometry.uniformContinuous a

instance completionContinuousStar : ContinuousStar (ReducedCompletion Γ) :=
  ⟨Completion.continuous_map⟩

theorem completionMap_star (x : ReducedCompletion Γ) :
    completionMap Γ (star x) = star (completionMap Γ x) := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq ((completionMap_isometry Γ).continuous.comp continuous_star)
      (continuous_star.comp (completionMap_isometry Γ).continuous)
  | ih a => simp only [completion_star_coe, completionMap_coe, map_star]

instance completionStarRing : StarRing (ReducedCompletion Γ) :=
  (completionMap_injective Γ).starRing (completionMap Γ)
    (completionMap_star Γ) (map_add _) (map_mul _)

instance completionStarModule : StarModule ℂ (ReducedCompletion Γ) :=
  Function.Injective.starModule (completionMap Γ) ℂ (completionMap_injective Γ)
    (completionMap_star Γ) (map_smul (completionAlgHom Γ))

instance completionNormedAlgebra : NormedAlgebra ℂ (ReducedCompletion Γ) where
  norm_smul_le := norm_smul_le

instance completionCStarRing : CStarRing (ReducedCompletion Γ) where
  norm_mul_self_le x := by
    rw [← norm_completionMap Γ x, ← norm_completionMap Γ (star x * x),
      map_mul, completionMap_star]
    exact CStarRing.norm_star_mul_self.symm.le

instance completionCStarAlgebra : CStarAlgebra (ReducedCompletion Γ) where

/-- The extended map as a unital complex star-algebra homomorphism. -/
def completionStarHom : ReducedCompletion Γ →⋆ₐ[ℂ] ReducedGroupCStar Γ where
  toAlgHom := completionAlgHom Γ
  map_star' := completionMap_star Γ

/-- The abstract norm completion is canonically the concrete reduced group C⋆-algebra. -/
def reducedCompletionEquiv : ReducedCompletion Γ ≃⋆ₐ[ℂ] ReducedGroupCStar Γ :=
  StarAlgEquiv.ofBijective (completionStarHom Γ)
    ⟨completionMap_injective Γ, completionMap_surjective Γ⟩

theorem reducedCompletionEquiv_isometry : Isometry (reducedCompletionEquiv Γ) :=
  completionMap_isometry Γ

@[simp] theorem reducedCompletionEquiv_coe (a : ReducedNormGroupAlgebra Γ) :
    reducedCompletionEquiv Γ (a : ReducedCompletion Γ) =
      ReducedNormGroupAlgebra.toReduced Γ a := completionMap_coe Γ a

/-- The original algebra embeds in the abstract completion. -/
def groupAlgebraToCompletion : GroupAlgebra Γ →⋆ₐ[ℂ] ReducedCompletion Γ where
  toAlgHom :=
    { toRingHom := Completion.coeRingHom.comp
        (ReducedNormGroupAlgebra.ofGroupAlgebra Γ).toAlgEquiv.toAlgHom.toRingHom
      commutes' _ := rfl }
  map_star' a := (completion_star_coe Γ (ReducedNormGroupAlgebra.ofGroupAlgebra Γ a)).symm

@[simp] theorem norm_groupAlgebraToCompletion (a : GroupAlgebra Γ) :
    ‖groupAlgebraToCompletion Γ a‖ = reducedNorm a :=
  Completion.norm_coe (ReducedNormGroupAlgebra.ofGroupAlgebra Γ a)

@[simp] theorem reducedCompletionEquiv_extends (a : GroupAlgebra Γ) :
    reducedCompletionEquiv Γ (groupAlgebraToCompletion Γ a) = integratedToReduced a :=
  completionMap_coe Γ (ReducedNormGroupAlgebra.ofGroupAlgebra Γ a)

/-- Uniqueness already holds among all continuous functions with the prescribed restriction. -/
theorem reducedCompletionEquiv_unique (f : ReducedCompletion Γ → ReducedGroupCStar Γ)
    (hf : Continuous f)
    (h : ∀ a : GroupAlgebra Γ, f (groupAlgebraToCompletion Γ a) = integratedToReduced a) :
    f = reducedCompletionEquiv Γ := by
  apply Completion.ext hf (reducedCompletionEquiv_isometry Γ).continuous
  intro a
  obtain ⟨b, rfl⟩ := (ReducedNormGroupAlgebra.ofGroupAlgebra Γ).surjective a
  exact (h b).trans (reducedCompletionEquiv_extends Γ b).symm

/-- In particular the extension is the unique isometric star-algebra isomorphism. -/
theorem reducedCompletionEquiv_unique_isometric
    (e : ReducedCompletion Γ ≃⋆ₐ[ℂ] ReducedGroupCStar Γ) (he : Isometry e)
    (h : ∀ a : GroupAlgebra Γ, e (groupAlgebraToCompletion Γ a) = integratedToReduced a) :
    e = reducedCompletionEquiv Γ := by
  apply DFunLike.coe_injective
  exact reducedCompletionEquiv_unique Γ e he.continuous h

end BC4lean
