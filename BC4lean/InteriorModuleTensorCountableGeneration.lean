import BC4lean.InteriorModuleTensor
import BC4lean.CountablyGeneratedModule
import Mathlib.Data.Nat.Pairing

/-! # Countable generation of the constructed interior tensor

Two actual coefficient-generating sequences give a paired generating sequence
of elementary tensors. Density is proved twice with the elementary cross-norm
bound and the balancing identity. Neither the coefficient algebras nor the
left action is required to be unital, and the left action need not be
nondegenerate.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B C E F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

/-- Elementary tensors depend boundedly and complex-linearly on the first factor. -/
def interiorModuleTensorLeftCLM (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (y : F) :
    E →L[ℂ] InteriorModuleTensor (E := E) φ :=
  ((interiorModuleTensorMk φ).flip y).mkContinuous ‖y‖ (fun x => by
    change ‖interiorModuleTensorMk φ x y‖ ≤ ‖y‖ * ‖x‖
    simpa only [mul_comm] using interiorModuleTensorMk_norm_le φ x y)

@[simp] theorem interiorModuleTensorLeftCLM_apply
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x : E) (y : F) :
    interiorModuleTensorLeftCLM φ y x = interiorModuleTensorMk φ x y := rfl

/-- Elementary tensors depend boundedly and complex-linearly on the second factor. -/
def interiorModuleTensorRightCLM (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x : E) :
    F →L[ℂ] InteriorModuleTensor (E := E) φ :=
  (interiorModuleTensorMk φ x).mkContinuous ‖x‖ (interiorModuleTensorMk_norm_le φ x)

@[simp] theorem interiorModuleTensorRightCLM_apply
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x : E) (y : F) :
    interiorModuleTensorRightCLM φ x y = interiorModuleTensorMk φ x y := rfl

/-- The actual tensor of two countably generated Hilbert modules is countably
 generated, including for degenerate nonunital left actions. -/
theorem IsCountablyGeneratedModule.interiorTensor
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule C F)
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    IsCountablyGeneratedModule C (InteriorModuleTensor (E := E) φ) := by
  obtain ⟨ξ, hξ⟩ := hE
  obtain ⟨η, hη⟩ := hF
  let ζ : ℕ → InteriorModuleTensor (E := E) φ :=
    fun k => interiorModuleTensorMk φ (ξ (Nat.unpair k).1) (η (Nat.unpair k).2)
  let M : Submodule ℂ (InteriorModuleTensor (E := E) φ) := moduleGeneratingSpan (B := C) ζ
  let K := M.topologicalClosure
  have hK : IsClosed (K : Set (InteriorModuleTensor (E := E) φ)) :=
    M.isClosed_topologicalClosure
  have hright (n : ℕ) (y : F) : interiorModuleTensorMk φ (ξ n) y ∈ K := by
    refine hη.induction ?_ ?_ y
    · intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        rcases hy with ⟨m, a, rfl⟩
        have heq : interiorModuleTensorMk φ (ξ n) (a • η m) = a • ζ (Nat.pair n m) := by
          simp only [ζ, Nat.unpair_pair, ← interiorModuleTensor_smul_mk]
        rw [heq]
        exact M.le_topologicalClosure (smul_mem_moduleGeneratingSpan ζ (Nat.pair n m) a)
      | zero =>
        simpa only [map_zero] using K.zero_mem
      | add y z _ _ hy hz =>
        simpa only [map_add] using K.add_mem hy hz
      | smul c y _ hy =>
        simpa only [map_smul] using K.smul_mem c hy
    · exact hK.preimage (interiorModuleTensorRightCLM φ (ξ n)).continuous
  have hleft (x : E) (y : F) : interiorModuleTensorMk φ x y ∈ K := by
    refine hξ.induction ?_ ?_ x
    · intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        rcases hx with ⟨n, b, rfl⟩
        change interiorModuleTensorMk φ (MulOpposite.op (MulOpposite.unop b) • ξ n) y ∈ K
        rw [interiorModuleTensorMk_balance]
        exact hright n _
      | zero =>
        simpa only [map_zero, LinearMap.zero_apply] using K.zero_mem
      | add x z _ _ hx hz =>
        simpa only [map_add, LinearMap.add_apply] using K.add_mem hx hz
      | smul c x _ hx =>
        simpa only [map_smul, LinearMap.smul_apply] using K.smul_mem c hx
    · exact hK.preimage (interiorModuleTensorLeftCLM φ y).continuous
  refine ⟨ζ, (moduleGeneratingSpan_closure_eq_top_iff ζ).mp ?_⟩
  apply top_unique
  intro u _
  have hp : Submodule.span ℂ
      (Set.range fun p : E × F => interiorModuleTensorMk φ p.1 p.2) ≤ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    exact hleft x y
  exact (interiorModuleTensor_span_dense φ).induction (fun _ hu => hp hu) hK u

end BC4lean.KKTheory
