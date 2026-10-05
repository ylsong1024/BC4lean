import BC4lean.EquivariantCW
import BC4lean.LabeledOrbitRealization
import Mathlib.Topology.Compactness.SigmaCompact

/-! # Countability and sigma compactness of the join realization -/
noncomputable section
namespace BC4lean.ProperActions
variable {Γ : Type*} [Group Γ] [Countable Γ]

instance : Countable (FiniteOrbitVertex Γ) := by
  let : Countable {H : Subgroup Γ // Finite H} := finiteIsotropy_countable (Γ := Γ)
  let (H : {H : Subgroup Γ // Finite H}) : Countable (Γ ⧸ H.val) :=
    (QuotientGroup.mk_surjective (s := H.val)).countable
  change Countable (Σ H : {H : Subgroup Γ // Finite H}, Γ ⧸ H.val)
  infer_instance

instance : Countable (LabeledOrbitSimplex Γ) := by
  have hi : Function.Injective (LabeledOrbitSimplex.vertices (Γ := Γ)) :=
    fun _ _ h => LabeledOrbitSimplex.ext h
  exact hi.countable

namespace LabeledOrbitRealization
omit [Countable Γ] in
/-- The countable family of compact finite simplex charts covers the realization. -/
theorem iUnion_range_chart : (⋃ s : LabeledOrbitSimplex Γ, Set.range (chart s)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨s, hs⟩ := x.property
  exact Set.mem_iUnion.mpr ⟨s, ⟨⟨x.val, hs⟩, rfl⟩⟩

/-- Sigma compactness follows from chart countability; local compactness is a
separate property and is not claimed for this weak join realization. -/
instance : SigmaCompactSpace (LabeledOrbitRealization Γ) := by
  apply isSigmaCompact_univ_iff.mp
  rw [← iUnion_range_chart (Γ := Γ)]
  exact isSigmaCompact_iUnion_of_isCompact _ isCompact_range_chart

end LabeledOrbitRealization
end BC4lean.ProperActions
