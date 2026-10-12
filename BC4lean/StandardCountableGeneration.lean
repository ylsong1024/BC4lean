import BC4lean.StandardCountableHilbertModule
import Mathlib.Data.Nat.Pairing

/-! # Countable generation of the actual standard countable Hilbert module

A countable family generating B_B is placed into every natural-number
coordinate. Continuity of each actual coordinate inclusion puts its entire
range into the closed coefficient span. Finite coefficient vectors are finite
sums of such coordinate vectors, and their canonical image is dense in H_B.
Thus separable nonunital coefficients give a countably generated standard
Hilbert module without inserting a coefficient unit.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Countable generation of the coefficient module passes to the actual H_B. -/
theorem standardCountableHilbertModule_countablyGenerated_of_standard
    (hB : IsCountablyGeneratedModule B Bᵐᵒᵖ) :
    IsCountablyGeneratedModule B (StandardCountableHilbertModule B) := by
  obtain ⟨ξ, hξ⟩ := hB
  let ζ : ℕ → StandardCountableHilbertModule B := fun k =>
    standardCountableInclusion (Nat.unpair k).1 (ξ (Nat.unpair k).2)
  have hζ (i j : ℕ) : ζ (Nat.pair i j) = standardCountableInclusion i (ξ j) := by
    simp [ζ, Nat.unpair_pair]
  let S := (moduleGeneratingSpan (B := B) ζ).topologicalClosure
  have hm (i : ℕ) : ∀ b ∈ moduleGeneratingSpan (B := B) ξ,
      standardCountableInclusion i b ∈ S := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      rcases hb with ⟨j, a, rfl⟩
      rw [(standardCountableInclusion (B := B) i).map_op_smul, ← hζ i j]
      exact (moduleGeneratingSpan (B := B) ζ).le_topologicalClosure
        (smul_mem_moduleGeneratingSpan ζ (Nat.pair i j) a)
    | zero =>
      rw [(standardCountableInclusion (B := B) i).toCLM.map_zero]
      exact S.zero_mem
    | add b c _ _ hb hc =>
      rw [(standardCountableInclusion (B := B) i).toCLM.map_add]
      exact S.add_mem hb hc
    | smul c b _ hb =>
      rw [(standardCountableInclusion (B := B) i).toCLM.map_smul]
      exact S.smul_mem c hb
  have hi (i : ℕ) (b : Bᵐᵒᵖ) : standardCountableInclusion i b ∈ S := by
    have hc : IsClosed {a : Bᵐᵒᵖ | standardCountableInclusion i a ∈ S} :=
      (moduleGeneratingSpan (B := B) ζ).isClosed_topologicalClosure.preimage
        (standardCountableInclusion (B := B) i).toCLM.continuous
    exact closure_minimal (hm i) hc (hξ b)
  have hfinite (v : StandardCountableVectors B) : standardCountableMk v ∈ S := by
    have hv : standardCountableMk v =
        ∑ i ∈ v.support, standardCountableInclusion i (v i) := by
      calc
        standardCountableMk v = standardCountableMk (v.sum Finsupp.single) :=
          congrArg (standardCountableMk (B := B)) v.sum_single.symm
        _ = ∑ i ∈ v.support, standardCountableMk (Finsupp.single i (v i)) := by
          change standardCountableMk (∑ i ∈ v.support, Finsupp.single i (v i)) = _
          rw [map_sum]
        _ = ∑ i ∈ v.support, standardCountableInclusion i (v i) := rfl
    rw [hv]
    exact S.sum_mem (fun i _ => hi i (v i))
  have ht : S = ⊤ := by
    apply top_unique
    intro x _
    exact closure_minimal (by
      rintro y ⟨v, rfl⟩
      exact hfinite v) (moduleGeneratingSpan (B := B) ζ).isClosed_topologicalClosure
        (standardCountableMk_denseRange (B := B) x)
  exact ⟨ζ, (moduleGeneratingSpan_closure_eq_top_iff ζ).mp ht⟩

/-- Separable nonunital coefficients give a genuinely countably generated H_B. -/
theorem standardCountableHilbertModule_isCountablyGenerated
    [TopologicalSpace.SeparableSpace B] :
    IsCountablyGeneratedModule B (StandardCountableHilbertModule B) :=
  standardCountableHilbertModule_countablyGenerated_of_standard standard_module_isCountablyGenerated

end BC4lean.KKTheory
