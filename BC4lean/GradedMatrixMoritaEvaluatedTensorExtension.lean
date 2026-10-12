import BC4lean.GradedMatrixMoritaFibreEvaluation
import BC4lean.InteriorModuleTensor

/-! # Contractive completion from the entire evaluated tensor pairing

This common construction descends an explicitly supplied balanced linear
map through the actual tensor null space. Its bound follows from evaluation
of the inner square. It assumes no norm or surjectivity identity.
-/

noncomputable section
namespace BC4lean.KKTheory.GradedMatrixMoritaEvaluatedTensorExtension
open scoped InnerProductSpace

variable {B C X E F H : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul C(X, C)ᵐᵒᵖ F] [CStarModule C(X, C)ᵐᵒᵖ F]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H] [CStarModule Cᵐᵒᵖ H]
  [CompleteSpace E] [CompleteSpace F] [CompleteSpace H]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C(X, C) F F) (t : X)
  (L : BalancedModuleTensor (E := E) φ →ₗ[ℂ] H)
  (hL : ∀ u v, ⟪L u, L v⟫_(Cᵐᵒᵖ) =
    MulOpposite.op (MulOpposite.unop (moduleTensorInner φ u v) t))

def preLinear : PreHilbertModuleTensor (E := E) φ →ₗ[ℂ] H :=
  (moduleTensorNull φ).liftQ L (by
    intro u hu
    apply (CStarModule.inner_self (A := Cᵐᵒᵖ)).mp
    rw [hL, (mem_moduleTensorNull_iff φ u).mp hu]
    rfl)

omit [CompleteSpace H] in
theorem preLinear_inner (u v : PreHilbertModuleTensor (E := E) φ) :
    ⟪preLinear φ t L hL u, preLinear φ t L hL v⟫_(Cᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪u, v⟫_(C(X, C)ᵐᵒᵖ) t) := by
  induction u using Submodule.Quotient.induction_on with
  | H u =>
    induction v using Submodule.Quotient.induction_on with
    | H v => exact hL u v

omit [CompleteSpace H] in
theorem preLinear_norm_le (u : PreHilbertModuleTensor (E := E) φ) :
    ‖preLinear φ t L hL u‖ ≤ ‖u‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ)
    (preLinear φ t L hL u), preLinear_inner]
  change Real.sqrt ‖MulOpposite.unop ⟪u, u⟫_(C(X, C)ᵐᵒᵖ) t‖ ≤ ‖u‖
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := C(X, C)ᵐᵒᵖ) u]
  exact Real.sqrt_le_sqrt ((MulOpposite.unop ⟪u, u⟫_(C(X, C)ᵐᵒᵖ)).norm_coe_le_norm t)

def preCLM : PreHilbertModuleTensor (E := E) φ →L[ℂ] H :=
  (preLinear φ t L hL).mkContinuous 1
    (fun u => by simpa only [one_mul] using preLinear_norm_le φ t L hL u)

def completedCLM : InteriorModuleTensor (E := E) φ →L[ℂ] H :=
  (preCLM φ t L hL).fromCompletion

@[simp] theorem completedCLM_coe (u : PreHilbertModuleTensor (E := E) φ) :
    completedCLM φ t L hL (moduleTensorToCompletion φ u) = preLinear φ t L hL u :=
  ContinuousLinearMap.fromCompletion_apply_coe _ u

@[simp] theorem completedCLM_mk (x : E) (y : F) :
    completedCLM φ t L hL (interiorModuleTensorMk φ x y) = L (moduleTensorMk φ x y) :=
  completedCLM_coe φ t L hL (preModuleTensorMk φ x y)

theorem completedCLM_inner (u v : InteriorModuleTensor (E := E) φ) :
    ⟪completedCLM φ t L hL u, completedCLM φ t L hL v⟫_(Cᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪u, v⟫_(C(X, C)ᵐᵒᵖ) t) := by
  induction u, v using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih u v =>
    change ⟪completedCLM φ t L hL (moduleTensorToCompletion φ u),
      completedCLM φ t L hL (moduleTensorToCompletion φ v)⟫_(Cᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop
        ⟪moduleTensorToCompletion φ u, moduleTensorToCompletion φ v⟫_(C(X, C)ᵐᵒᵖ) t)
    have hinner :
        ⟪moduleTensorToCompletion φ u, moduleTensorToCompletion φ v⟫_(C(X, C)ᵐᵒᵖ) =
          ⟪u, v⟫_(C(X, C)ᵐᵒᵖ) := hilbertModuleToCompletion_inner u v
    rw [completedCLM_coe, completedCLM_coe, hinner]
    exact preLinear_inner φ t L hL u v

end BC4lean.KKTheory.GradedMatrixMoritaEvaluatedTensorExtension
