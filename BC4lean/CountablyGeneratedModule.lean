import BC4lean.HilbertCStarModule
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-! # Countable generation of right Hilbert C⋆-modules

Countable generation means norm density of the complex linear span of all right
coefficient multiples of a sequence of vectors. This definition uses the
coefficient action of the actual module, including for nonunital coefficients.
It does not mean finite-dimensionality over the complex numbers.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

/-- The complex linear span of coefficient multiples of a generating sequence. -/
def moduleGeneratingSpan (ξ : ℕ → E) : Submodule ℂ E :=
  Submodule.span ℂ {x | ∃ n : ℕ, ∃ b : Bᵐᵒᵖ, x = b • ξ n}

/-- Countable generation in the Hilbert-module norm. -/
def IsCountablyGeneratedModule (B E : Type*) [NonUnitalCStarAlgebra B] [PartialOrder B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] : Prop :=
  ∃ ξ : ℕ → E, Dense (moduleGeneratingSpan (B := B) ξ : Set E)

omit [NonUnitalCStarAlgebra B] [PartialOrder B] [CStarModule Bᵐᵒᵖ E] in
/-- Every coefficient multiple of a sequence member lies in its generating span. -/
theorem smul_mem_moduleGeneratingSpan (ξ : ℕ → E) (n : ℕ) (b : Bᵐᵒᵖ) :
    b • ξ n ∈ moduleGeneratingSpan (B := B) ξ :=
  Submodule.subset_span ⟨n, b, rfl⟩

omit [NonUnitalCStarAlgebra B] [PartialOrder B] [CStarModule Bᵐᵒᵖ E] in
/-- A complete norm closure of the generating span is the entire module exactly
when the chosen sequence generates densely. -/
theorem moduleGeneratingSpan_closure_eq_top_iff (ξ : ℕ → E) :
    (moduleGeneratingSpan (B := B) ξ).topologicalClosure = ⊤ ↔
      Dense (moduleGeneratingSpan (B := B) ξ : Set E) := by
  exact Submodule.dense_iff_topologicalClosure_eq_top.symm

/-- The zero module is countably generated, including over nonunital B. -/
theorem isCountablyGeneratedModule_of_subsingleton [Subsingleton E] :
    IsCountablyGeneratedModule B E := by
  refine ⟨fun _ => 0, ?_⟩
  have h : (moduleGeneratingSpan (B := B) (fun _ : ℕ => (0 : E)) : Set E) = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true]
    have hx : x = 0 := Subsingleton.elim x 0
    rw [hx]
    exact Submodule.zero_mem _
  rw [h]
  exact dense_univ

/-- Countable generation is invariant under an isometric module isomorphism,
including a semilinear isomorphism twisting coefficients by an automorphism. -/
theorem IsCountablyGeneratedModule.map_linearIsometryEquiv
    (hE : IsCountablyGeneratedModule B E) (e : E ≃ₗᵢ[ℂ] F) (ρ : Bᵐᵒᵖ → Bᵐᵒᵖ)
    (he : ∀ b x, e (b • x) = ρ b • e x) : IsCountablyGeneratedModule B F := by
  obtain ⟨ξ, hξ⟩ := hE
  refine ⟨fun n => e (ξ n), ?_⟩
  have hm : ∀ x ∈ moduleGeneratingSpan (B := B) ξ,
      e x ∈ moduleGeneratingSpan (B := B) (fun n => e (ξ n)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨n, b, rfl⟩
      rw [he]
      exact smul_mem_moduleGeneratingSpan _ n (ρ b)
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      rw [map_smul]
      exact Submodule.smul_mem _ c hx
  have hd : DenseRange e := by
    rw [DenseRange, e.surjective.range_eq]
    exact dense_univ
  exact (hd.dense_image e.continuous hξ).mono (by
    rintro y ⟨x, hx, rfl⟩
    exact hm x hx)

end BC4lean.KKTheory
