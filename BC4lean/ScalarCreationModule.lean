import BC4lean.ScalarHilbertModule
import BC4lean.HilbertModuleCreationMap

/-! # The scalar tensor creation map is adjointable and need not be module compact

We retain the genuine Hilbert-space tensor product ℂ ⊗ H and its Hilbert
norm. The scalar Hilbert-module instances on H and ℂ ⊗ H reinterpret their
existing Hilbert inner products, without changing either norm. The creation
map at 1 on ℓ²(ℕ) is not compact even in the Hilbert C⋆-module sense.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace TensorProduct ComplexOrder ScalarHilbertModule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The actual scalar tensor creation map, with its proved bounded adjoint,
as an adjointable right Hilbert ℂ-module map. -/
def scalarCreationModuleMap (ξ : ℂ) : AdjointableMap ℂ H (ℂ ⊗[ℂ] H) :=
  ScalarHilbertModule.ofAdjointPair (scalarCreationMap ξ) (scalarCreationAdjoint ξ)
    (scalarCreationMap_adjoint_identity ξ)

@[simp] theorem scalarCreationModuleMap_toCLM (ξ : ℂ) :
    (scalarCreationModuleMap (H := H) ξ).toCLM = scalarCreationMap ξ := rfl

@[simp] theorem scalarCreationModuleMap_adjointCLM (ξ : ℂ) :
    (scalarCreationModuleMap (H := H) ξ).adjointCLM = scalarCreationAdjoint ξ := rfl

@[simp] theorem scalarCreationModuleMap_apply (ξ : ℂ) (η : H) :
    scalarCreationModuleMap ξ η = ξ ⊗ₜ[ℂ] η := rfl

@[simp] theorem scalarCreationModuleMap_norm (ξ : ℂ) :
    ‖scalarCreationModuleMap (H := H) ξ‖ = ‖scalarCreationMap (H := H) ξ‖ := rfl

/-- Adjointable module creation at 1 can fail module compactness, using the
actual scalar Hilbert tensor product on the infinite-dimensional ℓ²(ℕ). -/
theorem scalarCreationModuleMap_one_not_moduleCompact :
    ¬ IsModuleCompact (scalarCreationModuleMap (H := BC4lean.L2Group ℕ) 1) := by
  intro h
  exact scalarCreationMap_one_not_compact
    (ScalarHilbertModule.isCompactOperator_of_isModuleCompact h)

end BC4lean.KKTheory
