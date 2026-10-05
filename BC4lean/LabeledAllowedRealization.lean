import BC4lean.LabeledSimplexFaces
import BC4lean.LabeledOrbitRealizationAction

/-! # Weak realization of a downward family of labeled simplices -/
noncomputable section
namespace BC4lean.ProperActions.LabeledOrbitRealization
variable {Γ : Type*} [Group Γ]

/-- The genuine induced subspace supported on an allowed face family. -/
def AllowedRealization (A : Set (LabeledOrbitSimplex Γ)) :=
  {x : LabeledOrbitRealization Γ | supportSimplex x ∈ A}

/-- A coordinate chart into the allowed subcomplex. -/
def allowedChart (A : Set (LabeledOrbitSimplex Γ))
    (hA : ∀ {s t : LabeledOrbitSimplex Γ}, s ∈ A → t.vertices ⊆ s.vertices → t ∈ A)
    (s : LabeledOrbitSimplex Γ) (hs : s ∈ A)
    (w : LabeledSimplexCoordinates Γ s) : AllowedRealization A := by
  refine ⟨chart s w, hA hs ?_⟩
  intro v hv
  have hn := (mem_supportSimplex (chart s w) v).mp hv
  by_contra h
  exact hn (w.property.2.1 v h)

theorem continuous_allowedChart (A : Set (LabeledOrbitSimplex Γ))
    (hA : ∀ {s t : LabeledOrbitSimplex Γ}, s ∈ A → t.vertices ⊆ s.vertices → t ∈ A)
    (s : LabeledOrbitSimplex Γ) (hs : s ∈ A) :
    Continuous (allowedChart A hA s hs) :=
  (continuous_chart s).subtype_mk _

private theorem allowedFace_isClosedEmbedding (s : LabeledOrbitSimplex Γ)
    (t : Finset (LabeledOrbitVertex Γ)) (ht : t ⊆ s.vertices) :
    Topology.IsClosedEmbedding (faceCoordinates s t ht) :=
  (continuous_faceCoordinates s t ht).isClosedEmbedding (fun _ _ h =>
    Subtype.ext (congrArg (fun z : LabeledSimplexCoordinates Γ s => z.val) h))

/-- Chartwise closed subsets of a downward subcomplex are closed even in the ambient join. -/
theorem isClosed_image_of_allowedCharts (A : Set (LabeledOrbitSimplex Γ))
    (hA : ∀ {s t : LabeledOrbitSimplex Γ}, s ∈ A → t.vertices ⊆ s.vertices → t ∈ A)
    (U : Set (AllowedRealization A))
    (hU : ∀ s (hs : s ∈ A), IsClosed ((allowedChart A hA s hs) ⁻¹' U)) :
    IsClosed (Subtype.val '' U : Set (LabeledOrbitRealization Γ)) := by
  apply (isClosed_iff _).mpr
  intro s
  have he : (chart s) ⁻¹' (Subtype.val '' U) =
      ⋃ t : s.vertices.powerset,
        ⋃ (ht : s.ofSubset t.val (Finset.mem_powerset.mp t.property) ∈ A),
          faceCoordinates s t.val (Finset.mem_powerset.mp t.property) ''
            ((allowedChart A hA
              (s.ofSubset t.val (Finset.mem_powerset.mp t.property)) ht) ⁻¹' U) := by
    ext w
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨x, hx, he⟩
      let z := chart s w
      let t := (supportSimplex z).vertices
      have hts : t ⊆ s.vertices := by
        intro v hv
        have hz := (mem_supportSimplex z v).mp hv
        by_contra h
        exact hz (w.property.2.1 v h)
      have hsa : s.ofSubset t hts ∈ A := by
        have heq : s.ofSubset t hts = supportSimplex z := LabeledOrbitSimplex.ext rfl
        rw [heq]
        change supportSimplex (chart s w) ∈ A
        rw [← he]
        exact x.property
      have hw : w.val ∈ LabeledSimplexCoordinates Γ (s.ofSubset t hts) :=
        mem_coordinates_supportSimplex z
      refine ⟨⟨t, Finset.mem_powerset.mpr hts⟩, hsa, ⟨w.val, hw⟩, ?_, ?_⟩
      · have hxz : allowedChart A hA (s.ofSubset t hts) hsa ⟨w.val, hw⟩ = x := by
          exact Subtype.ext he.symm
        simpa only [hxz] using hx
      · exact Subtype.ext rfl
    · rintro ⟨t, ht, w', hw', he⟩
      refine ⟨allowedChart A hA (s.ofSubset t.val (Finset.mem_powerset.mp t.property)) ht w',
        hw', ?_⟩
      exact congrArg (chart s) he
  rw [he]
  apply isClosed_iUnion_of_finite
  intro t
  apply isClosed_iUnion_of_finite
  intro ht
  exact (allowedFace_isClosedEmbedding s t.val
    (Finset.mem_powerset.mp t.property)).isClosedMap _ (hU _ ht)

/-- Every finite ambient chart meets the allowed realization in finitely many faces. -/
theorem isClosed_iff_allowedCharts (A : Set (LabeledOrbitSimplex Γ))
    (hA : ∀ {s t : LabeledOrbitSimplex Γ}, s ∈ A → t.vertices ⊆ s.vertices → t ∈ A)
    (U : Set (AllowedRealization A)) :
    IsClosed U ↔ ∀ s (hs : s ∈ A), IsClosed ((allowedChart A hA s hs) ⁻¹' U) := by
  classical
  constructor
  · intro hU s hs
    exact hU.preimage (continuous_allowedChart A hA s hs)
  · intro hU
    have hclosed : IsClosed (Subtype.val '' U : Set (LabeledOrbitRealization Γ)) := by
      apply (isClosed_iff _).mpr
      intro s
      have he : (chart s) ⁻¹' (Subtype.val '' U) =
          ⋃ t : s.vertices.powerset,
            ⋃ (ht : s.ofSubset t.val (Finset.mem_powerset.mp t.property) ∈ A),
              faceCoordinates s t.val (Finset.mem_powerset.mp t.property) ''
                ((allowedChart A hA
                  (s.ofSubset t.val (Finset.mem_powerset.mp t.property)) ht) ⁻¹' U) := by
        ext w
        simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
        constructor
        · rintro ⟨x, hx, he⟩
          let z := chart s w
          let t := (supportSimplex z).vertices
          have hts : t ⊆ s.vertices := by
            intro v hv
            have hz := (mem_supportSimplex z v).mp hv
            by_contra h
            exact hz (w.property.2.1 v h)
          have hsa : s.ofSubset t hts ∈ A := by
            have heq : s.ofSubset t hts = supportSimplex z := LabeledOrbitSimplex.ext rfl
            rw [heq]
            change supportSimplex (chart s w) ∈ A
            rw [← he]
            exact x.property
          have hw : w.val ∈ LabeledSimplexCoordinates Γ (s.ofSubset t hts) :=
            mem_coordinates_supportSimplex z
          refine ⟨⟨t, Finset.mem_powerset.mpr hts⟩, hsa, ⟨w.val, hw⟩, ?_, ?_⟩
          · have hxz : allowedChart A hA (s.ofSubset t hts) hsa ⟨w.val, hw⟩ = x := by
              exact Subtype.ext he.symm
            simpa only [hxz] using hx
          · exact Subtype.ext rfl
        · rintro ⟨t, ht, w', hw', he⟩
          refine ⟨allowedChart A hA (s.ofSubset t.val (Finset.mem_powerset.mp t.property)) ht w',
            hw', ?_⟩
          exact congrArg (chart s) he
      rw [he]
      apply isClosed_iUnion_of_finite
      intro t
      apply isClosed_iUnion_of_finite
      intro ht
      exact (allowedFace_isClosedEmbedding s t.val
        (Finset.mem_powerset.mp t.property)).isClosedMap _ (hU _ ht)
    have hp := hclosed.preimage (continuous_subtype_val :
      Continuous (Subtype.val : AllowedRealization A → LabeledOrbitRealization Γ))
    simpa only [Set.preimage_image_eq U Subtype.val_injective] using hp

/-- Every downward simplex subcomplex is closed in the weak join topology. -/
theorem isClosed_allowedCarrier (A : Set (LabeledOrbitSimplex Γ))
    (hA : ∀ {s t : LabeledOrbitSimplex Γ}, s ∈ A → t.vertices ⊆ s.vertices → t ∈ A) :
    IsClosed {x : LabeledOrbitRealization Γ | supportSimplex x ∈ A} := by
  have hc := isClosed_image_of_allowedCharts A hA Set.univ (fun _ _ => by simp)
  simpa only [Set.image_univ, Subtype.range_val_subtype, AllowedRealization, Set.mem_ofPred_eq] using hc


theorem continuous_iff_allowedCharts (A : Set (LabeledOrbitSimplex Γ))
    (hA : ∀ {s t : LabeledOrbitSimplex Γ}, s ∈ A → t.vertices ⊆ s.vertices → t ∈ A)
    {Y : Type*} [TopologicalSpace Y] (f : AllowedRealization A → Y) :
    Continuous f ↔ ∀ s (hs : s ∈ A), Continuous (f ∘ allowedChart A hA s hs) := by
  constructor
  · intro hf s hs
    exact hf.comp (continuous_allowedChart A hA s hs)
  · intro hf
    apply continuous_iff_isClosed.mpr
    intro U hU
    apply (isClosed_iff_allowedCharts A hA _).mpr
    intro s hs
    exact hU.preimage (hf s hs)


end BC4lean.ProperActions.LabeledOrbitRealization
