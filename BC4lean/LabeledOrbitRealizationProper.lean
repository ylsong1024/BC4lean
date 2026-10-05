import BC4lean.LabeledOrbitRealizationAction
import BC4lean.ProperFixedPoints

/-! # Properness of the weak labeled-orbit realization

Compact sets have uniformly concentrated finite barycentric mass. Finite vertex
transporters therefore bound compact transporters, proving properness.
-/
noncomputable section
open scoped BigOperators Pointwise Classical
open Filter Topology
namespace BC4lean.ProperActions.LabeledOrbitRealization
variable {Γ : Type*} [Group Γ]

theorem coordinate_nonneg (x : LabeledOrbitRealization Γ) (v : LabeledOrbitVertex Γ) :
    0 ≤ x.val v := x.property.choose_spec.1 v

theorem sum_le_one (x : LabeledOrbitRealization Γ) (t : Finset (LabeledOrbitVertex Γ)) :
    ∑ v ∈ t, x.val v ≤ 1 := by
  classical
  obtain ⟨s, hs⟩ := x.property
  calc
    ∑ v ∈ t, x.val v = ∑ v ∈ t ∩ s.vertices, x.val v := by
      symm
      apply Finset.sum_subset (Finset.inter_subset_left)
      intro v hv hn
      exact hs.2.1 v (fun hv' => hn (Finset.mem_inter.mpr ⟨hv, hv'⟩))
    _ ≤ ∑ v ∈ s.vertices, x.val v :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun v _ _ => hs.1 v)
    _ = 1 := hs.2.2

theorem exists_half_mass (x : LabeledOrbitRealization Γ) :
    ∃ s : Finset (LabeledOrbitVertex Γ), (1 / 2 : ℝ) < ∑ v ∈ s, x.val v := by
  obtain ⟨s, hs⟩ := x.property
  exact ⟨s.vertices, by rw [hs.2.2]; norm_num⟩

theorem compact_half_mass {K : Set (LabeledOrbitRealization Γ)} (hK : IsCompact K) :
    ∃ s : Finset (LabeledOrbitVertex Γ), ∀ x ∈ K, (1 / 2 : ℝ) < ∑ v ∈ s, x.val v := by
  classical
  let U (s : Finset (LabeledOrbitVertex Γ)) : Set (LabeledOrbitRealization Γ) :=
    {x | (1 / 2 : ℝ) < ∑ v ∈ s, x.val v}
  have ho (s : Finset (LabeledOrbitVertex Γ)) : IsOpen (U s) :=
    isOpen_lt continuous_const (continuous_finsetSum s fun v _ => continuous_coordinate v)
  have hc : K ⊆ ⋃ s, U s := by
    intro x _
    obtain ⟨s, hs⟩ := exists_half_mass x
    exact Set.mem_iUnion.mpr ⟨s, hs⟩
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover U ho hc
  refine ⟨S.biUnion id, fun x hx => ?_⟩
  obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp (hS hx)
  apply lt_of_lt_of_le hxs
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun v hv => Finset.mem_biUnion.mpr ⟨s, hs, hv⟩)
    (fun v _ _ => coordinate_nonneg x v)

theorem half_mass_inter (x : LabeledOrbitRealization Γ)
    (s t : Finset (LabeledOrbitVertex Γ))
    (hs : (1 / 2 : ℝ) < ∑ v ∈ s, x.val v)
    (ht : (1 / 2 : ℝ) < ∑ v ∈ t, x.val v) : (s ∩ t).Nonempty := by
  classical
  by_contra h
  have hd : Disjoint s t := Finset.disjoint_iff_inter_eq_empty.mpr
    (Finset.not_nonempty_iff_eq_empty.mp h)
  have hle := sum_le_one x (s ∪ t)
  rw [Finset.sum_union hd] at hle
  linarith

theorem sum_translate_image (g : Γ) (x : LabeledOrbitRealization Γ)
    (s : Finset (LabeledOrbitVertex Γ)) :
    ∑ v ∈ s.image (fun w => g • w), (g • x).val v = ∑ w ∈ s, x.val w := by
  classical
  rw [Finset.sum_image (fun _ _ _ _ h => (MulAction.injective g) h)]
  simp

/-- Vertex transporters are translates of finite stabilizers when nonempty. -/
theorem finite_vertex_transporter (v w : LabeledOrbitVertex Γ) :
    ({g : Γ | g • v = w} : Set Γ).Finite := by
  classical
  by_cases he : ∃ a : Γ, a • v = w
  · obtain ⟨a, ha⟩ := he
    apply ((FiniteOrbitVertex.finite_fixing Γ v.2).image (fun h => a * h)).subset
    intro g hg
    refine ⟨a⁻¹ * g, ?_, by simp⟩
    change (a⁻¹ * g) • v.2 = v.2
    have hv : (a⁻¹ * g) • v = v := by rw [mul_smul, hg, ← ha]; simp
    exact congrArg Prod.snd hv
  · have hempty : ({g : Γ | g • v = w} : Set Γ) = ∅ := by
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => he ⟨g, h⟩
    rw [hempty]
    exact Set.finite_empty

theorem finite_compact_transporter {K L : Set (LabeledOrbitRealization Γ)}
    (hK : IsCompact K) (hL : IsCompact L) :
    {g : Γ | (g • K ∩ L).Nonempty}.Finite := by
  classical
  obtain ⟨s, hs⟩ := compact_half_mass hK
  obtain ⟨t, ht⟩ := compact_half_mass hL
  have hf : (⋃ v ∈ (s : Set (LabeledOrbitVertex Γ)),
      ⋃ w ∈ (t : Set (LabeledOrbitVertex Γ)), {g : Γ | g • v = w}).Finite :=
    s.finite_toSet.biUnion (fun v _ => t.finite_toSet.biUnion
      (fun w _ => finite_vertex_transporter v w))
  apply hf.subset
  intro g hg
  obtain ⟨q, hq, hqL⟩ := hg
  obtain ⟨x, hx, rfl⟩ := hq
  have himage : (1 / 2 : ℝ) < ∑ v ∈ s.image (fun w => g • w), (g • x).val v := by
    rw [sum_translate_image]
    exact hs x hx
  obtain ⟨v, hv⟩ := half_mass_inter (g • x) (s.image (fun w => g • w)) t
    himage (ht _ hqL)
  obtain ⟨hv, hvt⟩ := Finset.mem_inter.mp hv
  obtain ⟨w, hws, rfl⟩ := Finset.mem_image.mp hv
  exact Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr ⟨hws,
    Set.mem_iUnion.mpr ⟨g • w, Set.mem_iUnion.mpr ⟨hvt, rfl⟩⟩⟩⟩

theorem properlyDiscontinuous : ProperlyDiscontinuousSMul Γ (LabeledOrbitRealization Γ) :=
  properlyDiscontinuousSMul_iff.mpr (fun hK hL => finite_compact_transporter hK hL)

/-- Coordinate neighborhoods force every convergent action-pair ultrafilter to
concentrate on a finite set of group elements. No product compact-generation
hypothesis is needed. -/
theorem proper [TopologicalSpace Γ] [DiscreteTopology Γ] :
    ProperSMul Γ (LabeledOrbitRealization Γ) := by
  classical
  let : ContinuousSMul Γ (LabeledOrbitRealization Γ) :=
    ⟨continuous_prod_of_discrete_left.mpr continuous_const_smul⟩
  apply properSMul_iff_continuousSMul_ultrafilter_tendsto_t2.mpr
  refine ⟨inferInstance, ?_⟩
  intro F y x hF
  obtain ⟨s, hs⟩ := exists_half_mass x
  obtain ⟨t, ht⟩ := exists_half_mass y
  let B : Set Γ := ⋃ v ∈ (s : Set (LabeledOrbitVertex Γ)),
    ⋃ w ∈ (t : Set (LabeledOrbitVertex Γ)), {g : Γ | g • v = w}
  have hB : B.Finite := s.finite_toSet.biUnion (fun v _ =>
    t.finite_toSet.biUnion (fun w _ => finite_vertex_transporter v w))
  have hxs : ∀ᶠ z in (F : Filter (Γ × LabeledOrbitRealization Γ)),
      (1 / 2 : ℝ) < ∑ v ∈ s, z.2.val v := by
    have hn : {z : LabeledOrbitRealization Γ | (1 / 2 : ℝ) < ∑ v ∈ s, z.val v} ∈
        nhds x := (isOpen_lt continuous_const
          (continuous_finsetSum s fun v _ => continuous_coordinate v)).mem_nhds hs
    exact ((continuous_snd.tendsto (y, x)).comp hF) hn
  have hyt : ∀ᶠ z in (F : Filter (Γ × LabeledOrbitRealization Γ)),
      (1 / 2 : ℝ) < ∑ v ∈ t, (z.1 • z.2).val v := by
    have hn : {z : LabeledOrbitRealization Γ | (1 / 2 : ℝ) < ∑ v ∈ t, z.val v} ∈
        nhds y := (isOpen_lt continuous_const
          (continuous_finsetSum t fun v _ => continuous_coordinate v)).mem_nhds ht
    exact ((continuous_fst.tendsto (y, x)).comp hF) hn
  have he : ∀ᶠ z in (F : Filter (Γ × LabeledOrbitRealization Γ)), z.1 ∈ B := by
    filter_upwards [hxs, hyt] with z hz1 hz2
    have him : (1 / 2 : ℝ) <
        ∑ v ∈ s.image (fun w => z.1 • w), (z.1 • z.2).val v := by
      rw [sum_translate_image]
      exact hz1
    obtain ⟨v, hv⟩ := half_mass_inter (z.1 • z.2)
      (s.image (fun w => z.1 • w)) t him hz2
    obtain ⟨hv, hvt⟩ := Finset.mem_inter.mp hv
    obtain ⟨w, hws, rfl⟩ := Finset.mem_image.mp hv
    exact Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr ⟨hws,
      Set.mem_iUnion.mpr ⟨z.1 • w, Set.mem_iUnion.mpr ⟨hvt, rfl⟩⟩⟩⟩
  obtain ⟨g, _, hg⟩ := hB.isCompact.ultrafilter_le_nhds'
    (F.map Prod.fst) he
  exact ⟨g, hg⟩

/-- Infinite subgroups cannot fix a realization point. -/
theorem infinite_fixedPoints_empty [TopologicalSpace Γ] [DiscreteTopology Γ]
    (H : Subgroup Γ) [Infinite H] :
    IsEmpty (FixedPointSpace H (LabeledOrbitRealization Γ)) := by
  let := proper (Γ := Γ)
  exact fixedPointSpace_isEmpty H

end BC4lean.ProperActions.LabeledOrbitRealization
