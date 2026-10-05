import BC4lean.LabeledOrbitSimplices
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Separation.Hausdorff

/-! # Weak-topology realization of labeled orbit simplices

Points are finite barycentric combinations with admissible support. The topology
is the final topology of the finite simplex charts, rather than the subspace
topology of an infinite product. No CW attachment witnesses are asserted here.
-/
noncomputable section
namespace BC4lean.ProperActions
variable (Γ : Type*) [Group Γ]

/-- Barycentric coordinates in a specified finite labeled simplex. -/
def LabeledSimplexCoordinates (s : LabeledOrbitSimplex Γ) : Set (LabeledOrbitVertex Γ → ℝ) :=
  {w | (∀ v, 0 ≤ w v) ∧ (∀ v, v ∉ s.vertices → w v = 0) ∧
    ∑ v ∈ s.vertices, w v = 1}

/-- Each finite coordinate chart is closed in the coordinate product. -/
theorem labeledSimplexCoordinates_isClosed (s : LabeledOrbitSimplex Γ) :
    IsClosed (LabeledSimplexCoordinates Γ s) := by
  have he : LabeledSimplexCoordinates Γ s =
      (⋂ v, {w : LabeledOrbitVertex Γ → ℝ | 0 ≤ w v}) ∩
      ((⋂ v, ⋂ (_ : v ∉ s.vertices), {w : LabeledOrbitVertex Γ → ℝ | w v = 0}) ∩
      {w : LabeledOrbitVertex Γ → ℝ | ∑ v ∈ s.vertices, w v = 1}) := by
    ext w
    simp only [LabeledSimplexCoordinates, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_iInter]
  rw [he]
  exact (isClosed_iInter fun v => isClosed_le continuous_const (continuous_apply v)).inter
    ((isClosed_iInter fun v => isClosed_iInter fun _ =>
      isClosed_eq (continuous_apply v) continuous_const).inter
      (isClosed_eq (continuous_finsetSum s.vertices fun v _ => continuous_apply v)
        continuous_const))

/-- Every coordinate of a chart lies in the unit interval. -/
theorem labeledSimplexCoordinates_le_one (s : LabeledOrbitSimplex Γ)
    {w : LabeledOrbitVertex Γ → ℝ} (hw : w ∈ LabeledSimplexCoordinates Γ s)
    (v : LabeledOrbitVertex Γ) : w v ≤ 1 := by
  by_cases hv : v ∈ s.vertices
  · calc
      w v ≤ ∑ u ∈ s.vertices, w u := Finset.single_le_sum (fun u _ => hw.1 u) hv
      _ = 1 := hw.2.2
  · rw [hw.2.1 v hv]
    exact zero_le_one

/-- Finite charts are compact, including the empty chart. -/
theorem labeledSimplexCoordinates_isCompact (s : LabeledOrbitSimplex Γ) :
    IsCompact (LabeledSimplexCoordinates Γ s) := by
  apply (isCompact_pi_infinite (fun _ : LabeledOrbitVertex Γ =>
    isCompact_Icc (a := (0 : ℝ)) (b := 1))).of_isClosed_subset
    (labeledSimplexCoordinates_isClosed Γ s)
  intro w hw v
  exact ⟨hw.1 v, labeledSimplexCoordinates_le_one Γ s hw v⟩

instance (s : LabeledOrbitSimplex Γ) : CompactSpace (LabeledSimplexCoordinates Γ s) :=
  isCompact_iff_compactSpace.mp (labeledSimplexCoordinates_isCompact Γ s)

/-- The carrier identifies equal barycentric coordinates across overlapping charts. -/
def LabeledOrbitRealization :=
  {w : LabeledOrbitVertex Γ → ℝ // ∃ s, w ∈ LabeledSimplexCoordinates Γ s}

namespace LabeledOrbitRealization
variable {Γ}

/-- A finite simplex chart, including all of its faces. -/
def chart (s : LabeledOrbitSimplex Γ) (w : LabeledSimplexCoordinates Γ s) :
    LabeledOrbitRealization Γ := ⟨w.val, s, w.property⟩

/-- Weak topology: a map out is continuous precisely when it is continuous on
every finite simplex. -/
instance : TopologicalSpace (LabeledOrbitRealization Γ) :=
  ⨆ s, TopologicalSpace.coinduced (chart s) inferInstance

theorem continuous_chart (s : LabeledOrbitSimplex Γ) : Continuous (chart s) :=
  continuous_iSup_rng continuous_coinduced_rng

theorem continuous_iff {Y : Type*} [TopologicalSpace Y]
    (f : LabeledOrbitRealization Γ → Y) :
    Continuous f ↔ ∀ s, Continuous (f ∘ chart s) := by
  change @Continuous _ _ (⨆ s, TopologicalSpace.coinduced (chart s) inferInstance) _ f ↔ _
  simp only [continuous_iSup_dom, continuous_coinduced_dom]

theorem isOpen_iff (U : Set (LabeledOrbitRealization Γ)) :
    IsOpen U ↔ ∀ s, IsOpen ((chart s) ⁻¹' U) := by
  change @IsOpen _ (⨆ s, TopologicalSpace.coinduced (chart s) inferInstance) U ↔ _
  simp only [isOpen_iSup_iff, isOpen_coinduced]

theorem isClosed_iff (U : Set (LabeledOrbitRealization Γ)) :
    IsClosed U ↔ ∀ s, IsClosed ((chart s) ⁻¹' U) := by
  change @IsClosed _ (⨆ s, TopologicalSpace.coinduced (chart s) inferInstance) U ↔ _
  simp only [isClosed_iSup_iff, isClosed_coinduced]

/-- The coordinate vector of a realization point. -/
def coordinates (x : LabeledOrbitRealization Γ) : LabeledOrbitVertex Γ → ℝ := x.val

/-- Barycentric coordinates remain continuous for the weak topology. -/
theorem continuous_coordinates : Continuous (coordinates (Γ := Γ)) := by
  apply (continuous_iff _).mpr
  intro s
  exact continuous_subtype_val

theorem continuous_coordinate (v : LabeledOrbitVertex Γ) :
    Continuous (fun x : LabeledOrbitRealization Γ => x.val v) :=
  (continuous_apply v).comp (continuous_coordinates (Γ := Γ))

/-- Distinct coordinate vectors are separated in the realization. -/
instance : T2Space (LabeledOrbitRealization Γ) :=
  .of_injective_continuous Subtype.val_injective (continuous_coordinates (Γ := Γ))

/-- A finite simplex chart embeds as a closed subspace of the realization. -/
theorem chart_isClosedEmbedding (s : LabeledOrbitSimplex Γ) :
    Topology.IsClosedEmbedding (chart s) :=
  (continuous_chart s).isClosedEmbedding (fun _ _ h =>
    Subtype.ext (congrArg (fun z : LabeledOrbitRealization Γ => z.val) h))

theorem isCompact_range_chart (s : LabeledOrbitSimplex Γ) :
    IsCompact (Set.range (chart s)) :=
  isCompact_range (continuous_chart s)

/-- A realization point has a nonzero coordinate, since its total mass is one. -/
theorem exists_nonzero (x : LabeledOrbitRealization Γ) : ∃ v, x.val v ≠ 0 := by
  obtain ⟨s, hs⟩ := x.property
  by_contra h
  have hz : ∀ v, x.val v = 0 := fun v => not_not.mp (fun hv => h ⟨v, hv⟩)
  have he := hs.2.2
  simp only [hz, Finset.sum_const_zero] at he
  exact zero_ne_one he

/-- Active vertices form an admissible finite set; labels identify them uniquely. -/
theorem labels_injective_support (x : LabeledOrbitRealization Γ) :
    Set.InjOn Prod.fst {v | x.val v ≠ 0} := by
  obtain ⟨s, hs⟩ := x.property
  intro v hv w hw he
  exact s.labels_injective (by by_contra h; exact hv (hs.2.1 v h))
    (by by_contra h; exact hw (hs.2.1 w h)) he

theorem finite_support (x : LabeledOrbitRealization Γ) :
    ({v | x.val v ≠ 0} : Set (LabeledOrbitVertex Γ)).Finite := by
  obtain ⟨s, hs⟩ := x.property
  apply s.vertices.finite_toSet.subset
  intro v hv
  by_contra h
  exact hv (hs.2.1 v h)

end LabeledOrbitRealization
end BC4lean.ProperActions
