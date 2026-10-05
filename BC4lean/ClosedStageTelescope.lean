import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Archimedean.Basic

/-! # A geometric telescope of nested closed subspaces

The carrier is the union of the cylinders Eₙ × [n,n+1] inside X × ℝ.
Bounded open height slices embed in a finite-stage product with locally closed
range. These facts give local compactness and second countability from the
corresponding hypotheses on every stage. No homotopy equivalence, continuous
section, or CW structure is asserted.
-/
noncomputable section
open Set Topology Filter

namespace BC4lean.ClosedStageTelescope
variable {X : Type*} [TopologicalSpace X]

/-- The cylinders meet at their integer-height endpoints. -/
def carrier (E : ℕ → Set X) : Set (X × ℝ) :=
  {p | ∃ n : ℕ, p.1 ∈ E n ∧ p.2 ∈ Icc (n : ℝ) ((n : ℝ) + 1)}

abbrev Telescope (E : ℕ → Set X) := carrier E

/-- The bounded open height slice used for local topology. -/
def slice (E : ℕ → Set X) (N : ℕ) : Set (Telescope E) :=
  {p | p.val.2 < (N : ℝ)}

theorem slice_isOpen (E : ℕ → Set X) (N : ℕ) : IsOpen (slice E N) :=
  isOpen_Iio.preimage (continuous_snd.comp continuous_subtype_val)

omit [TopologicalSpace X] in
theorem slices_cover (E : ℕ → Set X) : (⋃ N : ℕ, slice E N) = univ := by
  apply eq_univ_of_forall
  intro p
  obtain ⟨N, hN⟩ := exists_nat_gt p.val.2
  exact mem_iUnion.mpr ⟨N, hN⟩

omit [TopologicalSpace X] in
theorem slice_mem_stage (E : ℕ → Set X) (hm : Monotone E) (N : ℕ)
    (p : slice E N) : p.val.val.1 ∈ E N := by
  obtain ⟨n, hn, ht⟩ := p.val.property
  have hlt : (n : ℝ) < (N : ℝ) := lt_of_le_of_lt ht.1 p.property
  have hnN : n < N := Nat.cast_lt.mp hlt
  exact hm (Nat.le_of_lt hnN) hn

/-- A bounded slice fits in one finite-stage product. -/
def sliceMap (E : ℕ → Set X) (hm : Monotone E) (N : ℕ) :
    slice E N → E N × ℝ :=
  fun p => (⟨p.val.val.1, slice_mem_stage E hm N p⟩, p.val.val.2)

theorem sliceMap_isEmbedding (E : ℕ → Set X) (hm : Monotone E) (N : ℕ) :
    IsEmbedding (sliceMap E hm N) := by
  let g : E N × ℝ → X × ℝ := fun p => (p.1.val, p.2)
  have hg : IsEmbedding g := IsEmbedding.subtypeVal.prodMap IsEmbedding.id
  have hcomp : IsEmbedding (g ∘ sliceMap E hm N) :=
    IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  exact (IsEmbedding.of_comp_iff hg).mp hcomp

/-- The finitely many closed cylinders visible below height N. -/
def cylinderPrefix (E : ℕ → Set X) (N : ℕ) : Set (E N × ℝ) :=
  ⋃ n : Fin N, {p | p.1.val ∈ E n.val ∧
    p.2 ∈ Icc (n.val : ℝ) ((n.val : ℝ) + 1)}

theorem cylinderPrefix_isClosed (E : ℕ → Set X) (hc : ∀ n, IsClosed (E n)) (N : ℕ) :
    IsClosed (cylinderPrefix E N) := by
  apply isClosed_iUnion_of_finite
  intro n
  exact ((hc n.val).preimage (continuous_subtype_val.comp continuous_fst)).inter
    (isClosed_Icc.preimage continuous_snd)

omit [TopologicalSpace X] in
theorem range_sliceMap (E : ℕ → Set X) (hm : Monotone E) (N : ℕ) :
    range (sliceMap E hm N) = cylinderPrefix E N ∩ {p : E N × ℝ | p.2 < (N : ℝ)} := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨n, hn, ht⟩ := p.val.property
    have hlt : (n : ℝ) < (N : ℝ) := lt_of_le_of_lt ht.1 p.property
    have hnN : n < N := Nat.cast_lt.mp hlt
    exact ⟨mem_iUnion.mpr ⟨⟨n, hnN⟩, hn, ht⟩, p.property⟩
  · rintro ⟨hp, ht⟩
    obtain ⟨n, hn⟩ := mem_iUnion.mp hp
    let p : slice E N := ⟨⟨(q.1.val, q.2), n.val, hn⟩, ht⟩
    refine ⟨p, ?_⟩
    exact Prod.ext (Subtype.ext rfl) rfl

theorem range_sliceMap_isLocallyClosed (E : ℕ → Set X) (hm : Monotone E)
    (hc : ∀ n, IsClosed (E n)) (N : ℕ) :
    IsLocallyClosed (range (sliceMap E hm N)) := by
  rw [range_sliceMap]
  exact ⟨{p : E N × ℝ | p.2 < (N : ℝ)}, cylinderPrefix E N,
    isOpen_Iio.preimage continuous_snd, cylinderPrefix_isClosed E hc N, inter_comm _ _⟩

theorem slice_locallyCompact (E : ℕ → Set X) (hm : Monotone E)
    (hc : ∀ n, IsClosed (E n)) (N : ℕ) [LocallyCompactSpace (E N)] :
    LocallyCompactSpace (slice E N) :=
  (sliceMap_isEmbedding E hm N).isInducing.locallyCompactSpace
    (range_sliceMap_isLocallyClosed E hm hc N)

theorem slice_secondCountable (E : ℕ → Set X) (hm : Monotone E)
    (N : ℕ) [SecondCountableTopology (E N)] : SecondCountableTopology (slice E N) :=
  (sliceMap_isEmbedding E hm N).secondCountableTopology

/-- The telescope is second countable when each nested stage is second countable. -/
theorem secondCountable (E : ℕ → Set X) (hm : Monotone E)
    [∀ N, SecondCountableTopology (E N)] : SecondCountableTopology (Telescope E) := by
  let (N : ℕ) : SecondCountableTopology (slice E N) := slice_secondCountable E hm N
  exact TopologicalSpace.secondCountableTopology_of_countable_cover (slice_isOpen E) (slices_cover E)

/-- Closed locally compact stages give a locally compact geometric telescope. -/
theorem locallyCompact (E : ℕ → Set X) (hm : Monotone E)
    (hc : ∀ n, IsClosed (E n)) [∀ N, LocallyCompactSpace (E N)] :
    LocallyCompactSpace (Telescope E) where
  local_compact_nhds := by
    intro p U hU
    obtain ⟨N, hN⟩ := exists_nat_gt p.val.2
    let q : slice E N := ⟨p, hN⟩
    let : LocallyCompactSpace (slice E N) := slice_locallyCompact E hm hc N
    obtain ⟨K, hKq, hKU, hKc⟩ :=
      local_compact_nhds (continuous_subtype_val.continuousAt hU :
        ((↑) : slice E N → Telescope E) ⁻¹' U ∈ 𝓝 q)
    refine ⟨((↑) : slice E N → Telescope E) '' K, ?_, ?_, ?_⟩
    · exact (slice_isOpen E N).isOpenMap_subtype_val.image_mem_nhds hKq
    · exact image_subset_iff.mpr hKU
    · exact hKc.image continuous_subtype_val

omit [TopologicalSpace X] in
/-- A finite upper height bound also bounds the stage containing the point. -/
theorem mem_stage_of_height_le (E : ℕ → Set X) (hm : Monotone E)
    (p : Telescope E) (N : ℕ) (hN : p.val.2 ≤ (N : ℝ)) : p.val.1 ∈ E N := by
  obtain ⟨n, hn, ht⟩ := p.property
  have hle : (n : ℝ) ≤ (N : ℝ) := ht.1.trans hN
  exact hm (Nat.cast_le.mp hle) hn

/-- The projection to the original space is continuous. -/
theorem continuous_projection (E : ℕ → Set X) :
    Continuous (fun p : Telescope E => p.val.1) :=
  continuous_fst.comp continuous_subtype_val

end BC4lean.ClosedStageTelescope
