import BC4lean.LabeledOrbitExhaustion
import Mathlib.Topology.DiscreteSubset

/-! # Compact subsets of the weak realization have finite total vertex support

The weak topology prevents a compact set from meeting infinitely many new
vertex supports. Distinct marked vertices give a sequence whose every subset
is closed, since each finite chart meets only finitely many marked terms.
-/
noncomputable section
open scoped Classical
namespace BC4lean.ProperActions.LabeledOrbitRealization
variable {Γ : Type*} [Group Γ]

/-- All vertices with a nonzero coordinate at some point in a set. -/
def activeVertices (K : Set (LabeledOrbitRealization Γ)) : Set (LabeledOrbitVertex Γ) :=
  {v | ∃ x ∈ K, x.val v ≠ 0}

/-- An injectively marked sequence meets every finite chart in finitely many terms;
hence every subset of its range is closed in the weak topology. -/
theorem isClosed_subset_range_marked
    (v : ℕ → LabeledOrbitVertex Γ) (hv : Function.Injective v)
    (x : ℕ → LabeledOrbitRealization Γ) (hx : ∀ n, (x n).val (v n) ≠ 0)
    {A : Set (LabeledOrbitRealization Γ)} (hA : A ⊆ Set.range x) : IsClosed A := by
  apply (isClosed_iff A).mpr
  intro s
  let I : Set ℕ := v ⁻¹' (s.vertices : Set (LabeledOrbitVertex Γ))
  have hI : I.Finite := s.vertices.finite_toSet.preimage hv.injOn
  have hf : ((chart s) ⁻¹' (x '' I)).Finite :=
    (hI.image x).preimage (chart_isClosedEmbedding s).injective.injOn
  apply (hf.subset ?_).isClosed
  intro w hw
  obtain ⟨n, hn⟩ := hA hw
  have hnI : n ∈ I := by
    change v n ∈ s.vertices
    by_contra hm
    have he : (x n).val (v n) = w.val (v n) :=
      congrArg (fun z : LabeledOrbitRealization Γ => z.val (v n)) hn
    exact hx n (he.trans (w.property.2.1 (v n) hm))
  exact ⟨n, hnI, hn⟩

/-- A compact subset of the weak realization uses only finitely many vertices. -/
theorem finite_activeVertices {K : Set (LabeledOrbitRealization Γ)} (hK : IsCompact K) :
    (activeVertices K).Finite := by
  by_contra hinf
  have hInf : (activeVertices K).Infinite := hinf
  let e : ℕ ↪ activeVertices K := hInf.natEmbedding _
  let v : ℕ → LabeledOrbitVertex Γ := fun n => (e n).val
  have hv : Function.Injective v := Subtype.val_injective.comp e.injective
  have he (n : ℕ) : ∃ x ∈ K, x.val (v n) ≠ 0 := (e n).property
  choose x hxK hxv using he
  let D : Set (LabeledOrbitRealization Γ) := Set.range x
  have hclosed : ∀ A ⊆ D, IsClosed A := fun A hA =>
    isClosed_subset_range_marked v hv x hxv hA
  have hD : IsClosed D := hclosed D (Set.Subset.refl _)
  have hDK : D ⊆ K := by
    rintro _ ⟨n, rfl⟩
    exact hxK n
  have hcompact : IsCompact D := hK.of_isClosed_subset hD hDK
  have hdiscrete : IsDiscrete D :=
    isDiscrete_iff_forall_mem_exists_isClosed.mpr (fun A hA =>
      ⟨A, hclosed A hA, Set.inter_eq_left.mpr hA⟩)
  have hfinite : D.Finite := hcompact.finite hdiscrete
  have hvertices : (⋃ z ∈ D, {v | z.val v ≠ 0}).Finite :=
    hfinite.biUnion (fun z _ => finite_support z)
  have hrange : (Set.range v).Finite := hvertices.subset (by
    rintro _ ⟨n, rfl⟩
    exact Set.mem_iUnion₂.mpr ⟨x n, Set.mem_range_self n, hxv n⟩)
  exact (Set.infinite_range_of_injective hv) hrange

/-- Compact sets are covered by finitely many finite simplex charts. -/
theorem exists_finite_chart_cover {K : Set (LabeledOrbitRealization Γ)} (hK : IsCompact K) :
    ∃ F : Finset (LabeledOrbitSimplex Γ), K ⊆ ⋃ s ∈ (F : Set (LabeledOrbitSimplex Γ)),
      Set.range (chart s) := by
  let V := (finite_activeVertices hK).toFinset
  let Q : Set (LabeledOrbitSimplex Γ) := {s | s.vertices ⊆ V}
  have hQ : Q.Finite := by
    have hp := V.powerset.finite_toSet
    have hf : (LabeledOrbitSimplex.vertices ⁻¹'
        (V.powerset : Set (Finset (LabeledOrbitVertex Γ)))).Finite :=
      hp.preimage (fun _ _ _ _ h => LabeledOrbitSimplex.ext h)
    apply hf.subset
    intro s hs
    exact Finset.mem_powerset.mpr hs
  refine ⟨hQ.toFinset, ?_⟩
  intro x hx
  have hs : supportSimplex x ∈ Q := by
    intro v hv
    exact (finite_activeVertices hK).mem_toFinset.mpr
      ⟨x, hx, (mem_supportSimplex x v).mp hv⟩
  exact Set.mem_iUnion₂.mpr ⟨supportSimplex x, hQ.mem_toFinset.mpr hs,
    ⟨⟨x.val, mem_coordinates_supportSimplex x⟩, rfl⟩⟩

/-- Under countability, every compact subset lies in one finite-orbit exhaustion stage. -/
theorem exists_exhaustion_stage [Countable Γ]
    {K : Set (LabeledOrbitRealization Γ)} (hK : IsCompact K) :
    ∃ N, ∀ x ∈ K, supportSimplex x ∈ LabeledOrbitSimplex.exhaustion N := by
  obtain ⟨F, hF⟩ := exists_finite_chart_cover hK
  let : Fintype ↥(F : Set (LabeledOrbitSimplex Γ)) := F.finite_toSet.fintype
  have hf (s : ↥(F : Set (LabeledOrbitSimplex Γ))) :
      ∃ n, s.val ∈ LabeledOrbitSimplex.exhaustion n := LabeledOrbitSimplex.mem_exhaustion _
  choose n hn using hf
  let N := Finset.univ.sup n
  refine ⟨N, ?_⟩
  intro x hx
  obtain ⟨s, hs, w, hw⟩ := Set.mem_iUnion₂.mp (hF hx)
  have hle : n ⟨s, hs⟩ ≤ N :=
    Finset.le_sup (Finset.mem_univ (⟨s, hs⟩ : ↥(F : Set (LabeledOrbitSimplex Γ))))
  have he : s ∈ LabeledOrbitSimplex.exhaustion N :=
    LabeledOrbitSimplex.exhaustion_mono hle (hn ⟨s, hs⟩)
  apply LabeledOrbitSimplex.orbitFaces_downward he
  rw [← hw]
  intro v hv
  by_contra hm
  exact ((mem_supportSimplex (chart s w) v).mp hv) (w.property.2.1 v hm)

/-- A continuous map from any compact domain has its entire image in one stage. -/
theorem exists_stage_for_compact_domain [Countable Γ]
    {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (f : T → LabeledOrbitRealization Γ) (hf : Continuous f) :
    ∃ N, ∀ t, supportSimplex (f t) ∈ LabeledOrbitSimplex.exhaustion N := by
  obtain ⟨N, hN⟩ := exists_exhaustion_stage (isCompact_range hf)
  exact ⟨N, fun t => hN (f t) (Set.mem_range_self t)⟩

end BC4lean.ProperActions.LabeledOrbitRealization
