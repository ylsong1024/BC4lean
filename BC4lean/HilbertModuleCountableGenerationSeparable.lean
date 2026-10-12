import BC4lean.CountablyGeneratedModule
import BC4lean.HilbertModuleCoefficientApproximateUnit
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! # Separability and countable generation of actual Hilbert modules

A countably generated module over separable coefficients is separable as a
complex normed space. Conversely, a separable Hilbert module is countably
generated, including for nonunital coefficients: the actual coefficient
approximate unit puts every member of a dense sequence in the closure of its
coefficient generating span. These results justify countable generation of
closed matching subspaces in the separable-coefficient homotopy setting.
-/

noncomputable section
namespace BC4lean.KKTheory

open Filter
open scoped Topology

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

/-- The actual bounded complex-linear map taking a coefficient to its action
on a fixed vector. Its bound follows from the Hilbert-module inner product. -/
def moduleCoefficientVector (x : E) : Bᵐᵒᵖ →L[ℂ] E :=
  (show Bᵐᵒᵖ →ₗ[ℂ] E from
    { toFun := fun b => b • x
      map_add' := fun b c => module_add_smul b c x
      map_smul' := fun c b => module_complex_smul c b x }).mkContinuous ‖x‖
        (fun b => by
          change ‖b • x‖ ≤ ‖x‖ * ‖b‖
          simpa only [mul_comm] using module_norm_smul_le b x)

@[simp] theorem moduleCoefficientVector_apply (x : E) (b : Bᵐᵒᵖ) :
    moduleCoefficientVector x b = b • x := rfl

/-- Countable Hilbert-module generation over separable coefficients gives
actual separability of the ambient complex normed vector space. -/
theorem IsCountablyGeneratedModule.separableSpace
    [TopologicalSpace.SeparableSpace B] (h : IsCountablyGeneratedModule B E) :
    TopologicalSpace.SeparableSpace E := by
  have : TopologicalSpace.SeparableSpace Bᵐᵒᵖ :=
    (MulOpposite.op_surjective : Function.Surjective
      (MulOpposite.op : B → Bᵐᵒᵖ)).denseRange.separableSpace MulOpposite.continuous_op
  obtain ⟨ξ, hξ⟩ := h
  have hset : {x : E | ∃ n : ℕ, ∃ b : Bᵐᵒᵖ, x = b • ξ n} =
      ⋃ n : ℕ, Set.range (moduleCoefficientVector (B := B) (ξ n)) := by
    ext x
    constructor
    · rintro ⟨n, b, rfl⟩
      exact Set.mem_iUnion.mpr ⟨n, ⟨b, rfl⟩⟩
    · intro hx
      obtain ⟨n, b, hb⟩ := Set.mem_iUnion.mp hx
      exact ⟨n, b, hb.symm⟩
  apply hξ.isSeparable_iff.mp
  change TopologicalSpace.IsSeparable
    (Submodule.span ℂ {x : E | ∃ n : ℕ, ∃ b : Bᵐᵒᵖ, x = b • ξ n} : Set E)
  apply TopologicalSpace.IsSeparable.span
  rw [hset]
  apply TopologicalSpace.IsSeparable.iUnion
  intro n
  exact TopologicalSpace.isSeparable_range
    (moduleCoefficientVector (B := B) (ξ n)).continuous

variable [StarOrderedRing B]

/-- Every member of a vector sequence lies in the closure of its coefficient
generating span through the actual nonunital coefficient approximate unit. -/
theorem vector_mem_closure_moduleGeneratingSpan (ξ : ℕ → E) (n : ℕ) :
    ξ n ∈ closure (moduleGeneratingSpan (B := B) ξ : Set E) := by
  apply (Submodule.isClosed_topologicalClosure (moduleGeneratingSpan (B := B) ξ)).mem_of_tendsto
    (tendsto_coefficient_approximateUnit_smul (D := Bᵐᵒᵖ) (ξ n))
  exact Eventually.of_forall fun b =>
    Submodule.le_topologicalClosure _ (smul_mem_moduleGeneratingSpan ξ n b)

/-- A vector sequence with dense range generates the actual nonunital Hilbert
module, because every sequence vector is approximated by coefficient multiples. -/
theorem moduleGeneratingSpan_dense_of_denseRange (ξ : ℕ → E) (hξ : DenseRange ξ) :
    Dense (moduleGeneratingSpan (B := B) ξ : Set E) := by
  have hrange : Set.range ξ ⊆ closure (moduleGeneratingSpan (B := B) ξ : Set E) := by
    rintro _ ⟨n, rfl⟩
    exact vector_mem_closure_moduleGeneratingSpan ξ n
  intro x
  have hx := closure_mono hrange (hξ x)
  simpa only [closure_closure] using hx

/-- Separability of the actual vector space implies Hilbert-module countable
generation without assuming a unit or a separate essentiality hypothesis. -/
theorem isCountablyGeneratedModule_of_separableSpace
    [TopologicalSpace.SeparableSpace E] : IsCountablyGeneratedModule B E := by
  refine ⟨TopologicalSpace.denseSeq E, ?_⟩
  exact moduleGeneratingSpan_dense_of_denseRange _ (TopologicalSpace.denseRange_denseSeq E)

end BC4lean.KKTheory
