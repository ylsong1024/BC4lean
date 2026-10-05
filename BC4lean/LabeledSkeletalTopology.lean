import BC4lean.LabeledOrbitSkeleta
import BC4lean.LabeledSimplexFaces

/-! # The skeletal subspace has the weak topology of its finite charts -/
noncomputable section
namespace BC4lean.ProperActions.LabeledOrbitRealization
variable {Γ : Type*} [Group Γ]

/-- The finite chart in a skeleton containing its entire simplex. -/
def boundedSkeletalChart (n : ℕ) (s : LabeledOrbitSimplex Γ) (hs : s.vertices.card ≤ n)
    (w : LabeledSimplexCoordinates Γ s) : skeletalCarrier (Γ := Γ) n :=
  ⟨chart s w, (mem_skeletalCarrier_iff n (chart s w)).mpr ⟨s, hs, w.property⟩⟩

theorem continuous_boundedSkeletalChart (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (hs : s.vertices.card ≤ n) : Continuous (boundedSkeletalChart n s hs) :=
  (continuous_chart s).subtype_mk _

/-- Face inclusions are closed embeddings of coordinate charts. -/
theorem faceCoordinates_isClosedEmbedding (s : LabeledOrbitSimplex Γ)
    (t : Finset (LabeledOrbitVertex Γ)) (ht : t ⊆ s.vertices) :
    Topology.IsClosedEmbedding (faceCoordinates s t ht) :=
  (continuous_faceCoordinates s t ht).isClosedEmbedding (fun _ _ h =>
    Subtype.ext (congrArg (fun z : LabeledSimplexCoordinates Γ s => z.val) h))

/-- Closedness on all finite skeletal charts implies closedness in the actual
induced skeletal topology. Higher charts meet a skeleton in finitely many faces. -/
theorem isClosed_iff_boundedSkeletalCharts (n : ℕ) (U : Set (skeletalCarrier (Γ := Γ) n)) :
    IsClosed U ↔ ∀ s (hs : s.vertices.card ≤ n),
      IsClosed ((boundedSkeletalChart n s hs) ⁻¹' U) := by
  classical
  constructor
  · intro hU s hs
    exact hU.preimage (continuous_boundedSkeletalChart n s hs)
  · intro hU
    have hA : IsClosed (Subtype.val '' U : Set (LabeledOrbitRealization Γ)) := by
      apply (isClosed_iff _).mpr
      intro s
      have he : (chart s) ⁻¹' (Subtype.val '' U) =
          ⋃ t : s.vertices.powerset, ⋃ (ht : t.val.card ≤ n),
            faceCoordinates s t.val (Finset.mem_powerset.mp t.property) ''
              ((boundedSkeletalChart n (s.ofSubset t.val (Finset.mem_powerset.mp t.property)) ht) ⁻¹' U) := by
        ext w
        simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
        constructor
        · rintro ⟨x,hx,he⟩
          let z := chart s w
          let t := (supportSimplex z).vertices
          have hts : t ⊆ s.vertices := by
            intro v hv
            have hz := (mem_supportSimplex z v).mp hv
            by_contra h
            exact hz (w.property.2.1 v h)
          have htn : t.card ≤ n := by
            have hz : z ∈ skeletalCarrier n := by
              change chart s w ∈ skeletalCarrier n
              rw [← he]
              exact x.property
            exact hz
          have hw : w.val ∈ LabeledSimplexCoordinates Γ (s.ofSubset t hts) :=
            mem_coordinates_supportSimplex z
          refine ⟨⟨t, Finset.mem_powerset.mpr hts⟩, htn, ⟨w.val,hw⟩, ?_, ?_⟩
          · have hxz : boundedSkeletalChart n (s.ofSubset t hts) htn ⟨w.val,hw⟩ = x := by
              apply Subtype.ext
              exact he.symm
            simpa only [hxz] using hx
          · exact Subtype.ext rfl
        · rintro ⟨t,hn,w',hw',he⟩
          refine ⟨boundedSkeletalChart n (s.ofSubset t.val (Finset.mem_powerset.mp t.property)) hn w', hw', ?_⟩
          exact congrArg (chart s) he
      rw [he]
      apply isClosed_iUnion_of_finite
      intro t
      apply isClosed_iUnion_of_finite
      intro hn
      exact (faceCoordinates_isClosedEmbedding s t.val (Finset.mem_powerset.mp t.property)).isClosedMap _
        (hU _ hn)
    have hpre := hA.preimage (continuous_subtype_val :
      Continuous (Subtype.val : skeletalCarrier (Γ := Γ) n → LabeledOrbitRealization Γ))
    have he : Subtype.val ⁻¹' (Subtype.val '' U) = U :=
      Set.preimage_image_eq _ Subtype.val_injective
    exact he ▸ hpre

/-- Maps out of a skeleton are continuous exactly on its finite simplex charts. -/
theorem continuous_iff_boundedSkeletalCharts {Y : Type*} [TopologicalSpace Y] (n : ℕ)
    (f : skeletalCarrier (Γ := Γ) n → Y) :
    Continuous f ↔ ∀ s (hs : s.vertices.card ≤ n),
      Continuous (f ∘ boundedSkeletalChart n s hs) := by
  constructor
  · intro hf s hs
    exact hf.comp (continuous_boundedSkeletalChart n s hs)
  · intro hf
    apply continuous_iff_isClosed.mpr
    intro U hU
    apply (isClosed_iff_boundedSkeletalCharts n _).mpr
    intro s hs
    exact hU.preimage (hf s hs)

end BC4lean.ProperActions.LabeledOrbitRealization
