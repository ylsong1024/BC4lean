import BC4lean.CountableModuleOperator
import BC4lean.FiniteModuleCountableGeneration
import Mathlib.Data.Nat.Pairing

/-! # Countable generation of the genuine countable row sum

Actual coordinate inclusions place a countable generating family into each
completed row. Their closed coefficient span contains every finite vector,
whose actual image is dense. Thus countable generation passes to the genuine
countable sum without a coefficient unit or a tensor identification.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

/-- Countable generation passes to the actual completed countable sum. -/
theorem oddKTheoryCountableModule_countablyGenerated
    (hE : IsCountablyGeneratedModule B E) :
    IsCountablyGeneratedModule B (CountableHilbertModuleSum B E) := by
  obtain ⟨ξ, hξ⟩ := hE
  let ζ : ℕ → CountableHilbertModuleSum B E := fun k =>
    countableModuleInclusion (B := B) (E := E) (Nat.unpair k).1 (ξ (Nat.unpair k).2)
  have hζ (i j : ℕ) : ζ (Nat.pair i j) = countableModuleInclusion (B := B) (E := E) i (ξ j) := by
    simp [ζ, Nat.unpair_pair]
  let S := (moduleGeneratingSpan (B := B) ζ).topologicalClosure
  have hm (i : ℕ) : ∀ b ∈ moduleGeneratingSpan (B := B) ξ,
      countableModuleInclusion (B := B) (E := E) i b ∈ S := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      rcases hb with ⟨j, a, rfl⟩
      rw [(countableModuleInclusion (B := B) (E := E) i).map_op_smul, ← hζ i j]
      exact (moduleGeneratingSpan (B := B) ζ).le_topologicalClosure
        (smul_mem_moduleGeneratingSpan ζ (Nat.pair i j) a)
    | zero =>
      rw [(countableModuleInclusion (B := B) (E := E) i).toCLM.map_zero]
      exact S.zero_mem
    | add b c _ _ hb hc =>
      rw [(countableModuleInclusion (B := B) (E := E) i).toCLM.map_add]
      exact S.add_mem hb hc
    | smul c b _ hb =>
      rw [(countableModuleInclusion (B := B) (E := E) i).toCLM.map_smul]
      exact S.smul_mem c hb
  have hi (i : ℕ) (b : E) : countableModuleInclusion (B := B) (E := E) i b ∈ S := by
    have hc : IsClosed {a : E | countableModuleInclusion (B := B) (E := E) i a ∈ S} :=
      (moduleGeneratingSpan (B := B) ζ).isClosed_topologicalClosure.preimage
        (countableModuleInclusion (B := B) (E := E) i).toCLM.continuous
    exact closure_minimal (hm i) hc (hξ b)
  have hfinite (v : CountableModuleVectors E) : countableModuleMk (B := B) (E := E) v ∈ S := by
    have hv : countableModuleMk (B := B) (E := E) v =
        ∑ i ∈ v.support, countableModuleInclusion (B := B) (E := E) i (v i) := by
      calc
        countableModuleMk (B := B) (E := E) v = countableModuleMk (B := B) (E := E) (v.sum Finsupp.single) :=
          congrArg (countableModuleMk (B := B) (E := E)) v.sum_single.symm
        _ = ∑ i ∈ v.support, countableModuleMk (B := B) (E := E) (Finsupp.single i (v i)) := by
          change countableModuleMk (B := B) (E := E) (∑ i ∈ v.support, Finsupp.single i (v i)) = _
          rw [map_sum]
        _ = ∑ i ∈ v.support, countableModuleInclusion (B := B) (E := E) i (v i) := rfl
    rw [hv]
    exact S.sum_mem (fun i _ => hi i (v i))
  have ht : S = ⊤ := by
    apply top_unique
    intro x _
    exact closure_minimal (by
      rintro y ⟨v, rfl⟩
      exact hfinite v) (moduleGeneratingSpan (B := B) ζ).isClosed_topologicalClosure
        (countableModuleMk_denseRange (B := B) x)
  exact ⟨ζ, (moduleGeneratingSpan_closure_eq_top_iff ζ).mp ht⟩

/-- Separable nonunital coefficients give countably generated genuine
countable sums of finite B-valued row modules. -/
theorem oddKTheoryCountableFiniteRows_isCountablyGenerated {ι : Type*}
    [Fintype ι] [DecidableEq ι] [TopologicalSpace.SeparableSpace B] :
    IsCountablyGeneratedModule B (CountableHilbertModuleSum B (FiniteStandardModule B ι)) :=
  oddKTheoryCountableModule_countablyGenerated finiteStandardModule_isCountablyGenerated_nonunital

end BC4lean.KKTheory
