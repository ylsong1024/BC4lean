import BC4lean.ClosedStageTelescope
import Mathlib.Topology.LocallyFinite

/-! # Actual closed cylinder embeddings into the geometric telescope -/
noncomputable section
open Set Topology
namespace BC4lean.ClosedStageTelescope
variable {X : Type*} [TopologicalSpace X]

/-- The n-th geometric cylinder, including both attached ends. -/
def cylinder (E : ℕ → Set X) (n : ℕ) :
    E n × Icc (n : ℝ) ((n : ℝ) + 1) → Telescope E :=
  fun p => ⟨(p.1.val, p.2.val), n, p.1.property, p.2.property⟩

theorem cylinder_isEmbedding (E : ℕ → Set X) (n : ℕ) :
    IsEmbedding (cylinder E n) := by
  have hcomp : IsEmbedding (Subtype.val ∘ cylinder E n) :=
    IsEmbedding.subtypeVal.prodMap IsEmbedding.subtypeVal
  exact (IsEmbedding.of_comp_iff IsEmbedding.subtypeVal).mp hcomp

omit [TopologicalSpace X] in
theorem range_cylinder (E : ℕ → Set X) (n : ℕ) :
    range (cylinder E n) =
      {p : Telescope E | p.val.1 ∈ E n ∧ p.val.2 ∈ Icc (n : ℝ) ((n : ℝ) + 1)} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.1.property, q.2.property⟩
  · intro hp
    exact ⟨(⟨p.val.1, hp.1⟩, ⟨p.val.2, hp.2⟩), Subtype.ext rfl⟩

theorem cylinder_isClosedEmbedding (E : ℕ → Set X) (hc : ∀ n, IsClosed (E n))
    (n : ℕ) : IsClosedEmbedding (cylinder E n) := by
  refine ⟨cylinder_isEmbedding E n, ?_⟩
  rw [range_cylinder]
  exact ((hc n).preimage (continuous_fst.comp continuous_subtype_val)).inter
    (isClosed_Icc.preimage (continuous_snd.comp continuous_subtype_val))

omit [TopologicalSpace X] in
theorem cylinders_cover (E : ℕ → Set X) :
    (⋃ n, range (cylinder E n)) = univ := by
  apply eq_univ_of_forall
  intro p
  obtain ⟨n, hn, ht⟩ := p.property
  exact mem_iUnion.mpr ⟨n, (range_cylinder E n).symm ▸ ⟨hn, ht⟩⟩

/-- Bounded height neighborhoods meet only finitely many integer cylinders. -/
theorem cylinders_locallyFinite (E : ℕ → Set X) :
    LocallyFinite (fun n => range (cylinder E n)) := by
  intro p
  obtain ⟨N, hN⟩ := exists_nat_gt p.val.2
  refine ⟨slice E N, (slice_isOpen E N).mem_nhds hN, ?_⟩
  apply (Set.finite_Iio N).subset
  intro n hn
  obtain ⟨q, hqc, hqs⟩ := hn
  change q ∈ range (cylinder E n) at hqc
  rw [range_cylinder E n] at hqc
  exact Nat.cast_lt.mp (lt_of_le_of_lt hqc.2.1 hqs)

/-- The product-subspace telescope has exactly the weak topology of its cylinders. -/
theorem isClosed_iff_cylinders (E : ℕ → Set X) (hc : ∀ n, IsClosed (E n))
    (U : Set (Telescope E)) :
    IsClosed U ↔ ∀ n, IsClosed ((cylinder E n) ⁻¹' U) := by
  constructor
  · intro hU n
    exact hU.preimage (cylinder_isEmbedding E n).continuous
  · intro hU
    have he : U = ⋃ n, cylinder E n '' ((cylinder E n) ⁻¹' U) := by
      ext p
      constructor
      · intro hp
        obtain ⟨n, hn, ht⟩ := p.property
        exact mem_iUnion.mpr ⟨n,
          ⟨(⟨p.val.1, hn⟩, ⟨p.val.2, ht⟩), hp, Subtype.ext rfl⟩⟩
      · intro hp
        obtain ⟨n, hn⟩ := mem_iUnion.mp hp
        obtain ⟨q, hq, rfl⟩ := hn
        exact hq
    rw [he]
    apply ((cylinders_locallyFinite E).subset (fun n => image_subset_range _ _)).isClosed_iUnion
    intro n
    exact (cylinder_isClosedEmbedding E hc n).isClosedMap _ (hU n)

/-- Continuity can be verified on the attached geometric cylinders. -/
theorem continuous_iff_cylinders (E : ℕ → Set X) (hc : ∀ n, IsClosed (E n))
    {Y : Type*} [TopologicalSpace Y] (f : Telescope E → Y) :
    Continuous f ↔ ∀ n, Continuous (f ∘ cylinder E n) := by
  constructor
  · intro hf n
    exact hf.comp (cylinder_isEmbedding E n).continuous
  · intro hf
    apply continuous_iff_isClosed.mpr
    intro U hU
    apply (isClosed_iff_cylinders E hc _).mpr
    intro n
    exact hU.preimage (hf n)


end BC4lean.ClosedStageTelescope
