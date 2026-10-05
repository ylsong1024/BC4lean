import BC4lean.LabeledAllowedAction

/-! # Weak charts for the dimension filtration of an allowed subcomplex -/
noncomputable section
namespace BC4lean.ProperActions.LabeledOrbitRealization
variable {Γ : Type*} [Group Γ]
variable (A : Set (LabeledOrbitSimplex Γ))
variable (hA : ∀ {s t : LabeledOrbitSimplex Γ}, s ∈ A → t.vertices ⊆ s.vertices → t ∈ A)

def boundedAllowedSkeletalChart (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (hs : s ∈ A) (hn : s.vertices.card ≤ n) (w : LabeledSimplexCoordinates Γ s) :
    allowedSkeletalCarrier A n :=
  ⟨allowedChart A hA s hs w, (mem_skeletalCarrier_iff _ _).mpr ⟨s, hn, w.property⟩⟩

theorem continuous_boundedAllowedSkeletalChart (n : ℕ) (s : LabeledOrbitSimplex Γ)
    (hs : s ∈ A) (hn : s.vertices.card ≤ n) :
    Continuous (boundedAllowedSkeletalChart A hA n s hs hn) :=
  (continuous_allowedChart A hA s hs).subtype_mk _

theorem isClosed_iff_allowedSkeletalCharts (n : ℕ) (U : Set (allowedSkeletalCarrier A n)) :
    IsClosed U ↔ ∀ s (hs : s ∈ A) (hn : s.vertices.card ≤ n),
      IsClosed ((boundedAllowedSkeletalChart A hA n s hs hn) ⁻¹' U) := by
  classical
  constructor
  · intro hU s hs hn
    exact hU.preimage (continuous_boundedAllowedSkeletalChart A hA n s hs hn)
  · intro hU
    have hc : IsClosed (Subtype.val '' U : Set (AllowedRealization A)) := by
      apply (isClosed_iff_allowedCharts A hA _).mpr
      intro s hs
      have he : (allowedChart A hA s hs) ⁻¹' (Subtype.val '' U) =
          ⋃ t : s.vertices.powerset, ⋃ (hn : t.val.card ≤ n),
            faceCoordinates s t.val (Finset.mem_powerset.mp t.property) ''
              ((boundedAllowedSkeletalChart A hA n
                (s.ofSubset t.val (Finset.mem_powerset.mp t.property))
                (hA hs (Finset.mem_powerset.mp t.property)) hn) ⁻¹' U) := by
        ext w
        simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
        constructor
        · rintro ⟨x, hx, he⟩
          let z := allowedChart A hA s hs w
          let t := (supportSimplex z.val).vertices
          have hts : t ⊆ s.vertices := by
            intro v hv
            have hz := (mem_supportSimplex z.val v).mp hv
            by_contra h
            exact hz (w.property.2.1 v h)
          have htn : t.card ≤ n := by
            have hz : z ∈ allowedSkeletalCarrier A n := by
              change allowedChart A hA s hs w ∈ allowedSkeletalCarrier A n
              rw [← he]
              exact x.property
            exact hz
          have hw : w.val ∈ LabeledSimplexCoordinates Γ (s.ofSubset t hts) :=
            mem_coordinates_supportSimplex z.val
          refine ⟨⟨t, Finset.mem_powerset.mpr hts⟩, htn, ⟨w.val, hw⟩, ?_, ?_⟩
          · have hxz : boundedAllowedSkeletalChart A hA n (s.ofSubset t hts)
                (hA hs hts) htn ⟨w.val, hw⟩ = x := by
              exact Subtype.ext he.symm
            simpa only [hxz] using hx
          · exact Subtype.ext rfl
        · rintro ⟨t, hn, w', hw', he⟩
          refine ⟨boundedAllowedSkeletalChart A hA n
            (s.ofSubset t.val (Finset.mem_powerset.mp t.property))
            (hA hs (Finset.mem_powerset.mp t.property)) hn w', hw', ?_⟩
          exact congrArg (allowedChart A hA s hs) he
      rw [he]
      apply isClosed_iUnion_of_finite
      intro t
      apply isClosed_iUnion_of_finite
      intro hn
      have hf : Topology.IsClosedEmbedding
          (faceCoordinates s t.val (Finset.mem_powerset.mp t.property)) :=
        (continuous_faceCoordinates _ _ _).isClosedEmbedding (fun _ _ h =>
          Subtype.ext (congrArg (fun z : LabeledSimplexCoordinates Γ s => z.val) h))
      exact hf.isClosedMap _ (hU _ _ hn)
    have hp := hc.preimage (continuous_subtype_val :
      Continuous (Subtype.val : allowedSkeletalCarrier A n → AllowedRealization A))
    simpa only [Set.preimage_image_eq U Subtype.val_injective] using hp

theorem continuous_iff_allowedSkeletalCharts {Y : Type*} [TopologicalSpace Y] (n : ℕ)
    (f : allowedSkeletalCarrier A n → Y) :
    Continuous f ↔ ∀ s (hs : s ∈ A) (hn : s.vertices.card ≤ n),
      Continuous (f ∘ boundedAllowedSkeletalChart A hA n s hs hn) := by
  constructor
  · intro hf s hs hn
    exact hf.comp (continuous_boundedAllowedSkeletalChart A hA n s hs hn)
  · intro hf
    apply continuous_iff_isClosed.mpr
    intro U hU
    apply (isClosed_iff_allowedSkeletalCharts A hA n _).mpr
    intro s hs hn
    exact hU.preimage (hf s hs hn)

end BC4lean.ProperActions.LabeledOrbitRealization
