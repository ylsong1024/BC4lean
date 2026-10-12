import BC4lean.GradedMatrixMoritaCycle
import BC4lean.GradedIntervalKasparovNormalization

/-! # The actual correspondence on continuous sections

A left action acts pointwise on sections. Its continuity comes from C⋆
contractivity, and compactness comes from the uniform finite-rank partition
theorem. This construction uses the Hilbert-module section norm.
-/

noncomputable section
namespace BC4lean.KKTheory.GradedMatrixMoritaSectionRepresentation
open scoped InnerProductSpace

variable {B C F X : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder C] [StarOrderedRing C] [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace F]

def leftActionCLM (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    B →L[ℂ] AdjointableMap C F F :=
  ({ toFun := φ, map_add' := φ.map_add, map_smul' := φ.map_smul } :
    B →ₗ[ℂ] AdjointableMap C F F).mkContinuous 1
      (fun b => by
        change ‖φ b‖ ≤ 1 * ‖b‖
        simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le φ b)

/-- The complete coefficient star homomorphism, with the actual section action. -/
def leftAction (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    C(X, B) →⋆ₙₐ[ℂ] AdjointableMap C(X, C) C(X, F) C(X, F) where
  toFun b := continuousSectionOperator
    ⟨fun t => φ (b t), (leftActionCLM φ).continuous.comp b.continuous⟩
  map_zero' := by ext s t; simp
  map_add' a b := by
    ext s t
    change φ (a t + b t) (s t) = φ (a t) (s t) + φ (b t) (s t)
    rw [map_add]
    rfl
  map_mul' a b := by
    ext s t
    change φ (a t * b t) (s t) = φ (a t) (φ (b t) (s t))
    rw [map_mul]
    rfl
  map_smul' z b := by
    ext s t
    change φ (z • b t) (s t) = z • φ (b t) (s t)
    rw [map_smul]
    rfl
  map_star' b := by
    ext s t
    change φ (star (b t)) (s t) = (star (φ (b t))) (s t)
    rw [map_star]

@[simp] theorem leftAction_apply (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (b : C(X, B)) (s : C(X, F)) (t : X) : leftAction φ b s t = φ (b t) (s t) := rfl

theorem leftAction_compact [T2Space X] (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (hφ : ∀ b, IsModuleCompact (φ b)) (b : C(X, B)) : IsModuleCompact (leftAction φ b) :=
  continuousSectionOperator_isModuleCompact _ (fun t => hφ (b t))

variable {Γ : Type*} [Group Γ] {δB : CStarGrading B} {δC : CStarGrading C}
  {β : CStarAlgebraAction Γ B} {η : CStarAlgebraAction Γ C}

local instance sourceSpectralOrder : PartialOrder B := CStarAlgebra.spectralOrder B
local instance sourceSpectralOrderedRing : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

theorem leftAction_graded (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (K : GradedHilbertModule δC F) (hφ : ModuleTensorRepresentationGraded (δB := δB) φ K) :
    ModuleTensorRepresentationGraded (δB := δB.continuousSections (X := X))
      (leftAction φ) (K.gradedContinuousSections (X := X)) := by
  intro b s
  ext t
  exact hφ (b t) (s t)

theorem leftAction_equivariant (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (V : EquivariantHilbertModule η F) (hφ : ModuleTensorRepresentationEquivariant φ β V) :
    ModuleTensorRepresentationEquivariant (leftAction φ)
      (β.continuousSections (X := X)) (V.continuousSections (X := X)) := by
  intro g b s
  ext t
  exact hφ g (b t) (s t)

theorem action_preservesGrading {C F X : Type*} [NonUnitalCStarAlgebra C]
    [PartialOrder C] [StarOrderedRing C] [TopologicalSpace X] [CompactSpace X]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
    [CompleteSpace F] {Γ : Type*} [Group Γ]
    {δC : CStarGrading C} {η : CStarAlgebraAction Γ C}
    (K : GradedHilbertModule δC F)
    (V : EquivariantHilbertModule η F) (h : V.PreservesGrading K) :
    (V.continuousSections (X := X)).PreservesGrading K.gradedContinuousSections := by
  intro g s
  ext t
  exact h g (s t)

end BC4lean.KKTheory.GradedMatrixMoritaSectionRepresentation
