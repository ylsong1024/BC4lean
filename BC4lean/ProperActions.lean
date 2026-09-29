import Mathlib.Topology.Algebra.ProperAction.CompactlyGenerated

/-! # Proper actions of discrete groups

We use Mathlib's `ProperSMul`, defined by properness of the action-pair map.
The compact-transporter criterion requires a locally compact Hausdorff space;
finite stabilizers are proved as a consequence, not used as a definition.
-/
namespace BC4lean.ProperActions
open scoped Pointwise

variable {Γ X : Type*} [Group Γ] [TopologicalSpace Γ]
variable [TopologicalSpace X] [MulAction Γ X]

/-- The map whose properness defines a proper action. -/
def actionMap : Γ × X → X × X := fun p => (p.1 • p.2, p.2)

/-- The project uses precisely Mathlib's proper-action predicate. -/
theorem proper_iff_actionMap : ProperSMul Γ X ↔ IsProperMap (actionMap (Γ := Γ) (X := X)) :=
  properSMul_iff Γ X

/-- Group elements moving one set to meet another. -/
def transporter (K L : Set X) : Set Γ := {g | (g • K ∩ L).Nonempty}

/-- A proper discrete-group action has finite compact transporters. -/
theorem finite_transporter [DiscreteTopology Γ] [ProperSMul Γ X]
    {K L : Set X} (hK : IsCompact K) (hL : IsCompact L) :
    (transporter (Γ := Γ) K L).Finite :=
  isCompact_iff_finite.mp (ProperSMul.isCompact_setOfPred_inter_nonempty hK hL)

/-- Properness implies finite stabilizers without a local compactness hypothesis. -/
theorem finite_stabilizer [DiscreteTopology Γ] [ProperSMul Γ X] (x : X) :
    (MulAction.stabilizer Γ x : Set Γ).Finite := by
  apply (finite_transporter (Γ := Γ) (K := {x}) (L := {x})
    isCompact_singleton isCompact_singleton).subset
  intro g hg
  refine ⟨g • x, Set.smul_mem_smul_set (Set.mem_singleton x), ?_⟩
  exact Set.mem_singleton_iff.mpr (MulAction.mem_stabilizer_iff.mp hg)

/-- A proper action has a Hausdorff orbit space. -/
theorem orbitSpace_t2 [ProperSMul Γ X] : T2Space (Quotient (MulAction.orbitRel Γ X)) :=
  inferInstance

omit [TopologicalSpace Γ] in
/-- An orbit space of a locally compact space is locally compact for a continuous action. -/
theorem orbitSpace_locallyCompact [ContinuousConstSMul Γ X] [LocallyCompactSpace X] :
    LocallyCompactSpace (Quotient (MulAction.orbitRel Γ X)) :=
  MulAction.isOpenQuotientMap_quotientMk.locallyCompactSpace

/-- Restricting a proper discrete-group action to any subgroup preserves properness. -/
theorem proper_subgroup [DiscreteTopology Γ] [ProperSMul Γ X] (H : Subgroup Γ) :
    ProperSMul H X :=
  properSMul_of_isClosedEmbedding H.subtype
    (isClosed_discrete (H : Set Γ)).isClosedEmbedding_subtypeVal (fun _ _ => rfl)

/-- A proper action on a nonempty compact space forces a discrete group to be finite. -/
theorem finite_group_of_compact [DiscreteTopology Γ] [ProperSMul Γ X]
    [CompactSpace X] [Nonempty X] : Finite Γ := by
  have h : (Set.univ : Set Γ).Finite := by
    simpa [transporter] using
      (finite_transporter (Γ := Γ) (X := X) isCompact_univ isCompact_univ)
  exact Set.finite_univ_iff.mp h

section LocallyCompact
variable [LocallyCompactSpace X] [T2Space X] [ContinuousSMul Γ X]

/-- On a locally compact Hausdorff space, properness is compactness of compact preimages. -/
theorem proper_iff_compact_preimages : ProperSMul Γ X ↔
    ∀ {K : Set (X × X)}, IsCompact K →
      IsCompact ((actionMap (Γ := Γ) (X := X)) ⁻¹' K) := by
  rw [proper_iff_actionMap, isProperMap_iff_isCompact_preimage]
  exact and_iff_right (continuous_smul.prodMk continuous_snd)

/-- The compact-transporter characterization of proper discrete-group actions. -/
theorem proper_iff_finite_transporters [DiscreteTopology Γ] : ProperSMul Γ X ↔
    ∀ {K L : Set X}, IsCompact K → IsCompact L → (transporter (Γ := Γ) K L).Finite := by
  rw [MulAction.properSMul_iff_isCompact_setOfPred_inter_nonempty]
  simp only [transporter, isCompact_iff_finite]

/-- Every continuous action of a finite discrete group on an LCH space is proper. -/
theorem proper_of_finite [DiscreteTopology Γ] [Finite Γ] : ProperSMul Γ X :=
  proper_iff_finite_transporters.mpr (fun _ _ => Set.toFinite _)
end LocallyCompact

/-- Left translation is proper for every topological group, in particular a discrete one. -/
theorem proper_leftTranslation [IsTopologicalGroup Γ] : ProperSMul Γ Γ :=
  inferInstance

end BC4lean.ProperActions
