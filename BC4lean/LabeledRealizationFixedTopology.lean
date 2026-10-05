import BC4lean.LabeledOrbitRealizationProper
import BC4lean.LabeledRealizationProducts

/-! # Weak chart topology on subgroup-fixed realization spaces -/
noncomputable section
open Topology
namespace BC4lean.ProperActions.LabeledOrbitRealization
variable {Γ : Type*} [Group Γ]

/-- A simplex whose vertices are all fixed by the subgroup. -/
def FixedSimplex (H : Subgroup Γ) :=
  {s : LabeledOrbitSimplex Γ // ∀ v ∈ s.vertices, ∀ h : H, (h : Γ) • v = v}

/-- The fixed face discards exactly the nonfixed vertices. -/
def fixedFace (H : Subgroup Γ) (s : LabeledOrbitSimplex Γ) : FixedSimplex H := by
  classical
  refine ⟨s.ofSubset (s.vertices.filter (fun v => ∀ h : H, (h : Γ) • v = v))
    (Finset.filter_subset _ _), ?_⟩
  intro v hv
  exact (Finset.mem_filter.mp hv).2

@[simp] theorem mem_fixedFace (H : Subgroup Γ) (s : LabeledOrbitSimplex Γ)
    (v : LabeledOrbitVertex Γ) :
    v ∈ (fixedFace H s).val.vertices ↔ v ∈ s.vertices ∧ ∀ h : H, (h : Γ) • v = v := by
  classical
  exact Finset.mem_filter

/-- A fixed chart takes values in the actual subgroup fixed-point subspace. -/
def fixedChart (H : Subgroup Γ) (s : FixedSimplex H)
    (w : LabeledSimplexCoordinates Γ s.val) : FixedPointSpace H (LabeledOrbitRealization Γ) := by
  refine ⟨chart s.val w, ?_⟩
  apply (fixed_iff_support_fixed H _).mpr
  intro v hv
  apply s.property v
  by_contra hn
  exact hv (w.property.2.1 v hn)

theorem continuous_fixedChart (H : Subgroup Γ) (s : FixedSimplex H) :
    Continuous (fixedChart H s) := (continuous_chart s.val).subtype_mk _

/-- Including a face retains precisely its barycentric coordinate vector. -/
def faceInclusion (H : Subgroup Γ) (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ (fixedFace H s).val) :
    LabeledSimplexCoordinates Γ s := by
  classical
  refine ⟨w.val, w.property.1, ?_, ?_⟩
  · intro v hv
    exact w.property.2.1 v (fun hn => hv ((mem_fixedFace H s v).mp hn).1)
  · rw [← w.property.2.2]
    symm
    apply Finset.sum_subset
    · intro v hv
      exact ((mem_fixedFace H s v).mp hv).1
    · intro v _ hn
      exact w.property.2.1 v hn

theorem faceInclusion_isClosedEmbedding (H : Subgroup Γ) (s : LabeledOrbitSimplex Γ) :
    IsClosedEmbedding (faceInclusion H s) := by
  apply Continuous.isClosedEmbedding
  · exact continuous_subtype_val.subtype_mk _
  · intro a b h
    exact Subtype.ext (congrArg (fun z : LabeledSimplexCoordinates Γ s => z.val) h)

/-- A fixed point of an arbitrary chart belongs to that chart's fixed face. -/
theorem coordinates_mem_fixedFace (H : Subgroup Γ) (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ s)
    (hw : chart s w ∈ MulAction.fixedPoints H (LabeledOrbitRealization Γ)) :
    w.val ∈ LabeledSimplexCoordinates Γ (fixedFace H s).val := by
  classical
  have hf := (fixed_iff_support_fixed H (chart s w)).mp hw
  refine ⟨w.property.1, ?_, ?_⟩
  · intro v hv
    by_contra hn
    apply hv
    rw [mem_fixedFace]
    refine ⟨?_, hf v hn⟩
    by_contra hvs
    exact hn (w.property.2.1 v hvs)
  · rw [← w.property.2.2]
    apply Finset.sum_subset
    · intro v hv
      exact ((mem_fixedFace H s v).mp hv).1
    · intro v hv hn
      by_contra hzero
      exact hn ((mem_fixedFace H s v).mpr ⟨hv, hf v hzero⟩)

/-- The fixed simplex atlas maps onto the subgroup-fixed point space. -/
def fixedAtlas (H : Subgroup Γ)
    (p : Σ s : FixedSimplex H, LabeledSimplexCoordinates Γ s.val) :
    FixedPointSpace H (LabeledOrbitRealization Γ) := fixedChart H p.1 p.2

theorem fixedAtlas_surjective (H : Subgroup Γ) : Function.Surjective (fixedAtlas H) := by
  intro x
  obtain ⟨s, hs⟩ := x.val.property
  refine ⟨⟨fixedFace H s, ⟨x.val.val, coordinates_mem_fixedFace H s ⟨x.val.val, hs⟩
    (by change x.val ∈ MulAction.fixedPoints H (LabeledOrbitRealization Γ); exact x.property)⟩⟩, ?_⟩
  rfl

/-- Every arbitrary chart meets a fixed subset in a closed embedded fixed face. -/
theorem chart_preimage_fixed_subset (H : Subgroup Γ)
    (U : Set (FixedPointSpace H (LabeledOrbitRealization Γ))) (s : LabeledOrbitSimplex Γ) :
    (chart s) ⁻¹' (Subtype.val '' U) =
      faceInclusion H s '' ((fixedChart H (fixedFace H s)) ⁻¹' U) := by
  ext w
  constructor
  · rintro ⟨x, hx, he⟩
    have hw : chart s w ∈ MulAction.fixedPoints H (LabeledOrbitRealization Γ) := he ▸ x.property
    refine ⟨⟨w.val, coordinates_mem_fixedFace H s w hw⟩, ?_, rfl⟩
    have hex : fixedChart H (fixedFace H s) ⟨w.val, coordinates_mem_fixedFace H s w hw⟩ = x := by
      apply Subtype.ext
      exact he.symm
    change fixedChart H (fixedFace H s) ⟨w.val, coordinates_mem_fixedFace H s w hw⟩ ∈ U
    rw [hex]
    exact hx
  · rintro ⟨a, ha, rfl⟩
    exact ⟨fixedChart H (fixedFace H s) a, ha, rfl⟩

theorem fixedAtlas_isQuotientMap (H : Subgroup Γ) : IsQuotientMap (fixedAtlas H) := by
  refine ⟨.of_isClosed_preimage_iff_isClosed ?_, fixedAtlas_surjective H⟩
  intro U
  constructor
  · intro hU
    have hface : ∀ s : FixedSimplex H, IsClosed ((fixedChart H s) ⁻¹' U) :=
      isClosed_sigma_iff.mp hU
    have himage : IsClosed (Subtype.val '' U : Set (LabeledOrbitRealization Γ)) := by
      apply (isClosed_iff _).mpr
      intro s
      rw [chart_preimage_fixed_subset]
      exact (faceInclusion_isClosedEmbedding H s).isClosedMap _ (hface (fixedFace H s))
    simpa using himage.preimage (continuous_subtype_val (p :=
      fun x => x ∈ MulAction.fixedPoints H (LabeledOrbitRealization Γ)))
  · intro hU
    exact hU.preimage (continuous_sigma fun s => continuous_fixedChart H s)

theorem continuous_fixed_iff (H : Subgroup Γ) {Y : Type*} [TopologicalSpace Y]
    (f : FixedPointSpace H (LabeledOrbitRealization Γ) → Y) :
    Continuous f ↔ ∀ s : FixedSimplex H, Continuous (f ∘ fixedChart H s) := by
  rw [(fixedAtlas_isQuotientMap H).continuous_iff]
  exact continuous_sigma_iff

/-- Fixed-space homotopies can be checked on fixed finite charts. -/
theorem continuous_fixed_product_iff (H : Subgroup Γ) {T Y : Type*}
    [TopologicalSpace T] [LocallyCompactSpace T] [TopologicalSpace Y]
    (f : FixedPointSpace H (LabeledOrbitRealization Γ) × T → Y) :
    Continuous f ↔ ∀ s : FixedSimplex H,
      Continuous (fun p : LabeledSimplexCoordinates Γ s.val × T =>
        f (fixedChart H s p.1, p.2)) := by
  constructor
  · intro hf s
    exact hf.comp ((continuous_fixedChart H s).prodMap continuous_id)
  · intro hf
    apply (fixedAtlas_isQuotientMap H).continuous_lift_prod_left
    let e := Homeomorph.sigmaProdDistrib (X := fun s : FixedSimplex H =>
      LabeledSimplexCoordinates Γ s.val) (Y := T)
    have hc : Continuous (fun p : Σ s : FixedSimplex H,
        LabeledSimplexCoordinates Γ s.val × T => f (fixedChart H p.1 p.2.1, p.2.2)) :=
      continuous_sigma hf
    exact hc.comp e.continuous

end BC4lean.ProperActions.LabeledOrbitRealization
