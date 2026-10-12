import BC4lean.FiniteProjectionModule
import Mathlib.Logic.Encodable.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # Countable generation of finite standard modules without a coefficient unit

A countable family of generators of B_B is placed in every finite coordinate.
The norm closure of its right-coefficient span contains each full coordinate
range, by continuity of the genuine coordinate inclusion. Their finite sum is
the entire finite standard Hilbert module. Separability of B supplies the
standard-module generating family through its proved approximate-unit argument.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B ι : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype ι] [DecidableEq ι]

/-- Countable standard-module generators give countable generators in every finite coordinate. -/
theorem finiteStandardModule_countablyGenerated_of_standard
    (hB : IsCountablyGeneratedModule B Bᵐᵒᵖ) :
    IsCountablyGeneratedModule B (FiniteStandardModule B ι) := by
  obtain ⟨ξ, hξ⟩ := hB
  let : Encodable (ι × ℕ) := Encodable.ofCountable _
  let ζ : ℕ → FiniteStandardModule B ι := fun k =>
    match Encodable.decode (α := ι × ℕ) k with
    | none => 0
    | some p => finiteStandardSingle p.1 (ξ p.2)
  have hζ (i : ι) (n : ℕ) : ζ (Encodable.encode (i, n)) = finiteStandardSingle i (ξ n) := by
    simp [ζ]
  let S := (moduleGeneratingSpan (B := B) ζ).topologicalClosure
  have hm (i : ι) : ∀ x ∈ moduleGeneratingSpan (B := B) ξ, finiteStandardInclusion (B := B) i x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨n, b, rfl⟩
      rw [(finiteStandardInclusion (B := B) i).map_op_smul, finiteStandardInclusion_apply, ← hζ]
      exact (moduleGeneratingSpan (B := B) ζ).le_topologicalClosure
        (smul_mem_moduleGeneratingSpan ζ (Encodable.encode (i, n)) b)
    | zero => rw [(finiteStandardInclusion (B := B) i).toCLM.map_zero]; exact S.zero_mem
    | add x y _ _ hx hy =>
      rw [(finiteStandardInclusion (B := B) i).toCLM.map_add]
      exact S.add_mem hx hy
    | smul c x _ hx =>
      rw [(finiteStandardInclusion (B := B) i).toCLM.map_smul]
      exact S.smul_mem c hx
  have hi (i : ι) (x : Bᵐᵒᵖ) : finiteStandardInclusion (B := B) i x ∈ S := by
    have hc : IsClosed {y : Bᵐᵒᵖ | finiteStandardInclusion (B := B) i y ∈ S} :=
      (moduleGeneratingSpan (B := B) ζ).isClosed_topologicalClosure.preimage
        (finiteStandardInclusion (B := B) i).toCLM.continuous
    exact closure_minimal (hm i) hc (hξ x)
  have ht : S = ⊤ := by
    apply top_unique
    intro v _
    have hv : v = ∑ i : ι, finiteStandardInclusion (B := B) i (v i) := by
      ext j
      change v j = (∑ i : ι, Pi.single i (v i)) j
      simp only [Finset.sum_apply, Pi.single_apply]
      exact (Fintype.sum_ite_eq j (fun i : ι => v i)).symm
    rw [hv]
    exact S.sum_mem (fun i _ => hi i (v i))
  exact ⟨ζ, (moduleGeneratingSpan_closure_eq_top_iff ζ).mp ht⟩

/-- A separable possibly nonunital coefficient algebra gives a countably generated
finite standard module with the actual Hilbert-module norm. -/
theorem finiteStandardModule_isCountablyGenerated_nonunital [TopologicalSpace.SeparableSpace B] :
    IsCountablyGeneratedModule B (FiniteStandardModule B ι) :=
  finiteStandardModule_countablyGenerated_of_standard standard_module_isCountablyGenerated

end BC4lean.KKTheory
