import BC4lean.InteriorModuleTensor
import BC4lean.HilbertModuleEquiv
import Mathlib.Topology.Algebra.LinearMapCompletion

/-! # Completion of an actual balanced coefficient-form isometry

A linear map on the actual balanced tensor preserving its whole
coefficient-valued form annihilates the null submodule. Its separated
isometry extends to the actual Hilbert-module completion and retains
the whole pairing. This helper uses no matrix Morita construction.
-/

noncomputable section
namespace BC4lean.KKTheory.InteriorModuleTensorFormCompletion
open scoped InnerProductSpace

variable {B C E F H : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H] [CStarModule Cᵐᵒᵖ H]
  [CompleteSpace E] [CompleteSpace F] [CompleteSpace H]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
  (L : BalancedModuleTensor (E := E) φ →ₗ[ℂ] H)
  (hL : ∀ u v, ⟪L u, L v⟫_(Cᵐᵒᵖ) = moduleTensorInner φ u v)

def preLinear : PreHilbertModuleTensor (E := E) φ →ₗ[ℂ] H :=
  (moduleTensorNull φ).liftQ L (by
    intro u hu
    apply (CStarModule.inner_self (A := Cᵐᵒᵖ)).mp
    rw [hL]
    exact (mem_moduleTensorNull_iff φ u).mp hu)

omit [CompleteSpace H] in
theorem preLinear_inner (u v : PreHilbertModuleTensor (E := E) φ) :
    ⟪preLinear φ L hL u, preLinear φ L hL v⟫_(Cᵐᵒᵖ) = ⟪u, v⟫_(Cᵐᵒᵖ) := by
  induction u using Submodule.Quotient.induction_on with
  | H u =>
    induction v using Submodule.Quotient.induction_on with
    | H v => exact hL u v

def preIsometry : PreHilbertModuleTensor (E := E) φ →ₗᵢ[ℂ] H where
  toLinearMap := preLinear φ L hL
  norm_map' u := by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ), preLinear_inner,
      ← CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ)]

def completedCLM : InteriorModuleTensor (E := E) φ →L[ℂ] H :=
  (preIsometry φ L hL).toContinuousLinearMap.fromCompletion

@[simp] theorem completedCLM_coe (u : PreHilbertModuleTensor (E := E) φ) :
    completedCLM φ L hL (moduleTensorToCompletion φ u) = preIsometry φ L hL u :=
  ContinuousLinearMap.fromCompletion_apply_coe _ u

theorem completedCLM_norm (u : InteriorModuleTensor (E := E) φ) :
    ‖completedCLM φ L hL u‖ = ‖u‖ := by
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih u =>
    change ‖completedCLM φ L hL (moduleTensorToCompletion φ u)‖ =
      ‖moduleTensorToCompletion φ u‖
    rw [completedCLM_coe, (preIsometry φ L hL).norm_map, (moduleTensorToCompletion φ).norm_map]

def completedIsometry : InteriorModuleTensor (E := E) φ →ₗᵢ[ℂ] H where
  toLinearMap := (completedCLM φ L hL).toLinearMap
  norm_map' := completedCLM_norm φ L hL

@[simp] theorem completedIsometry_mk (x : E) (y : F) :
    completedIsometry φ L hL (interiorModuleTensorMk φ x y) = L (moduleTensorMk φ x y) :=
  completedCLM_coe φ L hL (preModuleTensorMk φ x y)

theorem completedIsometry_inner (u v : InteriorModuleTensor (E := E) φ) :
    ⟪completedIsometry φ L hL u, completedIsometry φ L hL v⟫_(Cᵐᵒᵖ) = ⟪u, v⟫_(Cᵐᵒᵖ) := by
  induction u, v using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih u v =>
    change ⟪completedCLM φ L hL (moduleTensorToCompletion φ u),
      completedCLM φ L hL (moduleTensorToCompletion φ v)⟫_(Cᵐᵒᵖ) =
      ⟪moduleTensorToCompletion φ u, moduleTensorToCompletion φ v⟫_(Cᵐᵒᵖ)
    rw [completedCLM_coe, completedCLM_coe]
    exact (preLinear_inner φ L hL u v).trans (hilbertModuleToCompletion_inner u v).symm

end BC4lean.KKTheory.InteriorModuleTensorFormCompletion
