import BC4lean.LabeledPrismInverseProjection
import BC4lean.OrderedPrismUniqueness

/-! # Uniqueness of staircase prism coordinates -/
noncomputable section
open scoped BigOperators Classical
namespace BC4lean.ProperActions.LabeledPrismProjection
open LabeledOrbitRealization LabeledTelescopePrisms
variable {Γ : Type*} [Group Γ]

private theorem prism_images_disjoint (n k : ℕ) (s : LabeledOrbitSimplex Γ) :
    Disjoint ((s.vertices.filter (fun v => v.1 ≤ k)).image (vertex n))
      ((s.vertices.filter (fun v => k ≤ v.1)).image (vertex (n + 1))) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hv
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hw
  exact vertex_ne_vertex_succ n a b (ha.trans hb.symm)

private theorem sum_lower_filter (n k : ℕ) (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ (simplex n k s)) :
    (∑ u ∈ s.vertices.filter (fun u => u.1 ≤ k), w.val (vertex n u)) =
      ∑ u ∈ s.vertices, w.val (vertex n u) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _
  split_ifs with hk
  · rfl
  · have hz : w.val (vertex n u) = 0 :=
      w.property.2.1 _ (fun hm => hk ((mem_lower_prism_vertex n k s u).mp hm).2)
    exact hz.symm

private theorem sum_upper_filter (n k : ℕ) (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ (simplex n k s)) :
    (∑ u ∈ s.vertices.filter (fun u => k ≤ u.1), w.val (vertex (n + 1) u)) =
      ∑ u ∈ s.vertices, w.val (vertex (n + 1) u) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _
  split_ifs with hk
  · rfl
  · have hz : w.val (vertex (n + 1) u) = 0 :=
      w.property.2.1 _ (fun hm => hk ((mem_upper_prism_vertex n k s u).mp hm).2)
    exact hz.symm

/-- The lower and upper masses of every whole prism chart sum to one. -/
theorem prism_mass (n k : ℕ) (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ (simplex n k s)) :
    (∑ u ∈ s.vertices, w.val (vertex n u)) +
      (∑ u ∈ s.vertices, w.val (vertex (n + 1) u)) = 1 := by
  have hm := w.property.2.2
  change (∑ v ∈ vertices n k s, w.val v) = 1 at hm
  unfold vertices at hm
  rw [Finset.sum_union (prism_images_disjoint n k s),
    Finset.sum_image (fun _ _ _ _ h => vertex_injective n h),
    Finset.sum_image (fun _ _ _ _ h => vertex_injective (n + 1) h),
    sum_lower_filter, sum_upper_filter] at hm
  exact hm

/-- Height determines the upper mass in each slab. -/
theorem prism_height (n k : ℕ) (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ (simplex n k s)) :
    height (chart _ w) = (n : ℝ) + ∑ u ∈ s.vertices, w.val (vertex (n + 1) u) := by
  rw [height_chart]
  change (∑ v ∈ vertices n k s, w.val v * (heightVertex v : ℝ)) = _
  unfold vertices
  rw [Finset.sum_union (prism_images_disjoint n k s),
    Finset.sum_image (fun _ _ _ _ h => vertex_injective n h),
    Finset.sum_image (fun _ _ _ _ h => vertex_injective (n + 1) h)]
  simp only [height_vertex, Nat.cast_add, Nat.cast_one]
  rw [← Finset.sum_mul, ← Finset.sum_mul, sum_lower_filter, sum_upper_filter]
  calc
    _ = ((∑ u ∈ s.vertices, w.val (vertex n u)) +
      (∑ u ∈ s.vertices, w.val (vertex (n + 1) u))) * n +
        ∑ u ∈ s.vertices, w.val (vertex (n + 1) u) := by ring
    _ = _ := by rw [prism_mass]; simp

@[simp] theorem vertex_height_forget (v : LabeledOrbitVertex Γ) :
    vertex (heightVertex v) (forgetVertex v) = v := by
  apply Prod.ext
  · exact Nat.pair_unpair v.1
  · rfl

/-- Projection-zero old vertices have zero masses in both prism copies. -/
theorem prism_zero_of_base_zero (n k : ℕ) (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ (simplex n k s)) (u : LabeledOrbitVertex Γ)
    (hu : baseCoordinates (chart _ w) u = 0) :
    w.val (vertex n u) = 0 ∧ w.val (vertex (n + 1) u) = 0 := by
  rw [baseCoordinates_whole_prism] at hu
  have hl := w.property.1 (vertex n u)
  have hh := w.property.1 (vertex (n + 1) u)
  constructor <;> linarith

/-- Upper mass may be summed over the actual projected support, avoiding ghost vertices. -/
theorem prism_upper_sum_support (n k : ℕ) (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ (simplex n k s)) (b : LabeledOrbitRealization Γ)
    (hb : ∀ u, b.val u = baseCoordinates (chart _ w) u) :
    (∑ u ∈ (supportSimplex b).vertices, w.val (vertex (n + 1) u)) =
      ∑ u ∈ s.vertices, w.val (vertex (n + 1) u) := by
  have hsub : (supportSimplex b).vertices ⊆ s.vertices := by
    intro u hu
    have hn := (mem_supportSimplex b u).mp hu
    by_contra h
    have hc := base_mem_coordinates (Finset.Subset.refl (simplex n k s).vertices) w
    exact hn ((hb u).trans (hc.2.1 u h))
  apply Finset.sum_subset hsub
  intro u _ hu
  have hz : b.val u = 0 := not_not.mp (fun hn => hu ((mem_supportSimplex b u).mpr hn))
  exact (prism_zero_of_base_zero n k s w u ((hb u).symm.trans hz)).2

/-- The actual staircase cut is inherited by the active projected support. -/
theorem prism_staircase (n k : ℕ) (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ (simplex n k s)) :
    (∀ u, u.1 < k → w.val (vertex (n + 1) u) = 0) ∧
      (∀ u, k < u.1 → w.val (vertex n u) = 0) := by
  constructor
  · intro u hu
    exact w.property.2.1 _ (fun hm => Nat.not_le_of_lt hu ((mem_upper_prism_vertex n k s u).mp hm).2)
  · intro u hu
    exact w.property.2.1 _ (fun hm => Nat.not_le_of_lt hu ((mem_lower_prism_vertex n k s u).mp hm).2)

/-- Two prism charts in the same slab with equal base and height are identical. -/
theorem same_slab_unique (n k k' : ℕ) (s s' : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ (simplex n k s))
    (w' : LabeledSimplexCoordinates Γ (simplex n k' s'))
    (b : LabeledOrbitRealization Γ)
    (hb : ∀ u, b.val u = baseCoordinates (chart _ w) u)
    (hb' : ∀ u, b.val u = baseCoordinates (chart _ w') u)
    (hh : height (chart _ w) = height (chart _ w')) : chart _ w = chart _ w' := by
  let L := (supportSimplex b).vertices
  have hmass : (∑ u ∈ L, w.val (vertex (n + 1) u)) =
      ∑ u ∈ L, w'.val (vertex (n + 1) u) := by
    rw [prism_upper_sum_support n k s w b hb, prism_upper_sum_support n k' s' w' b hb']
    rw [prism_height, prism_height] at hh
    linarith
  have he := BC4lean.OrderedPrismWeights.staircase_split_unique L Prod.fst
    (supportSimplex b).labels_injective
    (fun u => w.val (vertex (n + 1) u)) (fun u => w.val (vertex n u))
    (fun u => w'.val (vertex (n + 1) u)) (fun u => w'.val (vertex n u)) b.val
    (fun u _ => w.property.1 _) (fun u _ => w.property.1 _)
    (fun u _ => w'.property.1 _) (fun u _ => w'.property.1 _)
    (fun u _ => by rw [hb u, baseCoordinates_whole_prism]; ring)
    (fun u _ => by rw [hb' u, baseCoordinates_whole_prism]; ring) k k'
    (fun u _ hu => (prism_staircase n k s w).1 u hu)
    (fun u _ hu => (prism_staircase n k s w).2 u hu)
    (fun u _ hu => (prism_staircase n k' s' w').1 u hu)
    (fun u _ hu => (prism_staircase n k' s' w').2 u hu) hmass
  have hlu (u : LabeledOrbitVertex Γ) : w.val (vertex n u) = w'.val (vertex n u) := by
    by_cases hu : u ∈ L
    · exact (he u hu).2
    · have hz : b.val u = 0 := not_not.mp (fun hn => hu ((mem_supportSimplex b u).mpr hn))
      rw [(prism_zero_of_base_zero n k s w u ((hb u).symm.trans hz)).1,
        (prism_zero_of_base_zero n k' s' w' u ((hb' u).symm.trans hz)).1]
  have hhu (u : LabeledOrbitVertex Γ) :
      w.val (vertex (n + 1) u) = w'.val (vertex (n + 1) u) := by
    by_cases hu : u ∈ L
    · exact (he u hu).1
    · have hz : b.val u = 0 := not_not.mp (fun hn => hu ((mem_supportSimplex b u).mpr hn))
      rw [(prism_zero_of_base_zero n k s w u ((hb u).symm.trans hz)).2,
        (prism_zero_of_base_zero n k' s' w' u ((hb' u).symm.trans hz)).2]
  apply Subtype.ext
  funext v
  by_cases hv : heightVertex v = n
  · rw [← vertex_height_forget v, hv]
    exact hlu _
  · by_cases hv' : heightVertex v = n + 1
    · rw [← vertex_height_forget v, hv']
      exact hhu _
    · have hz : w.val v = 0 := w.property.2.1 v (fun hm => by
        rcases height_mem_prism hm with hm | hm
        · exact hv hm
        · exact hv' hm)
      have hz' : w'.val v = 0 := w'.property.2.1 v (fun hm => by
        rcases height_mem_prism hm with hm | hm
        · exact hv hm
        · exact hv' hm)
      exact hz.trans hz'.symm


/-- Charts in distinct slabs can coincide only on the shared integer face. -/
theorem different_slab_unique (n m k k' : ℕ) (hnm : n < m)
    (s s' : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ (simplex n k s))
    (w' : LabeledSimplexCoordinates Γ (simplex m k' s'))
    (b : LabeledOrbitRealization Γ)
    (hb : ∀ u, b.val u = baseCoordinates (chart _ w) u)
    (hb' : ∀ u, b.val u = baseCoordinates (chart _ w') u)
    (hh : height (chart _ w) = height (chart _ w')) : chart _ w = chart _ w' := by
  let L := (supportSimplex b).vertices
  have hs : (∑ u ∈ L, (w.val (vertex n u) + w.val (vertex (n + 1) u))) = 1 := by
    calc
      _ = ∑ u ∈ L, b.val u := by
        apply Finset.sum_congr rfl
        intro u _
        exact (baseCoordinates_whole_prism n k s w u).symm.trans (hb u).symm
      _ = 1 := (mem_coordinates_supportSimplex b).2.2
  have hs' : (∑ u ∈ L, (w'.val (vertex m u) + w'.val (vertex (m + 1) u))) = 1 := by
    calc
      _ = ∑ u ∈ L, b.val u := by
        apply Finset.sum_congr rfl
        intro u _
        exact (baseCoordinates_whole_prism m k' s' w' u).symm.trans (hb' u).symm
      _ = 1 := (mem_coordinates_supportSimplex b).2.2
  have hH : height (chart _ w) = (n : ℝ) + ∑ u ∈ L, w.val (vertex (n + 1) u) := by
    rw [prism_upper_sum_support n k s w b hb]
    exact prism_height n k s w
  have hH' : height (chart _ w) = (m : ℝ) + ∑ u ∈ L, w'.val (vertex (m + 1) u) := by
    rw [hh, prism_upper_sum_support m k' s' w' b hb']
    exact prism_height m k' s' w'
  obtain ⟨hem, _, he⟩ := BC4lean.OrderedPrismWeights.adjacent_slab_weights L
    (fun u => w.val (vertex n u)) (fun u => w.val (vertex (n + 1) u))
    (fun u => w'.val (vertex m u)) (fun u => w'.val (vertex (m + 1) u))
    (fun u _ => w.property.1 _) (fun u _ => w.property.1 _)
    (fun u _ => w'.property.1 _) (fun u _ => w'.property.1 _) hs hs'
    (fun u _ => by rw [← baseCoordinates_whole_prism n k s w u,
      ← baseCoordinates_whole_prism m k' s' w' u, ← hb u, ← hb' u]) n m hnm _ hH hH'
  have hall (u : LabeledOrbitVertex Γ) : w.val (vertex n u) = 0 ∧
      w'.val (vertex (m + 1) u) = 0 ∧ w.val (vertex (n + 1) u) = w'.val (vertex m u) := by
    by_cases hu : u ∈ L
    · exact he u hu
    · have hz : b.val u = 0 := not_not.mp (fun hn => hu ((mem_supportSimplex b u).mpr hn))
      obtain ⟨hl, hu⟩ := prism_zero_of_base_zero n k s w u ((hb u).symm.trans hz)
      obtain ⟨hl', hu'⟩ := prism_zero_of_base_zero m k' s' w' u ((hb' u).symm.trans hz)
      exact ⟨hl, hu', hu.trans hl'.symm⟩
  apply Subtype.ext
  funext v
  by_cases hv : heightVertex v = m
  · have hm : vertex m (forgetVertex v) = v := by
      rw [← hv]
      exact vertex_height_forget v
    have hn : vertex (n + 1) (forgetVertex v) = v :=
      (congrArg (fun j => vertex j (forgetVertex v)) hem.symm).trans hm
    exact (congrArg w.val hn).symm.trans
      ((hall (forgetVertex v)).2.2.trans (congrArg w'.val hm))
  · have hz : w.val v = 0 := by
      by_cases hm : v ∈ (simplex n k s).vertices
      · rcases height_mem_prism hm with hn | hn
        · rw [← vertex_height_forget v, hn]
          exact (hall _).1
        · exact False.elim (hv (hn.trans hem.symm))
      · exact w.property.2.1 v hm
    have hz' : w'.val v = 0 := by
      by_cases hm : v ∈ (simplex m k' s').vertices
      · rcases height_mem_prism hm with hn | hn
        · exact False.elim (hv hn)
        · rw [← vertex_height_forget v, hn]
          exact (hall _).2.1
      · exact w'.property.2.1 v hm
    exact hz.trans hz'.symm

variable [Countable Γ]

/-- Equal geometric base and height determine every tagged prism coordinate. -/
theorem projection_injective : Function.Injective (projection (Γ := Γ)) := by
  intro x y hxy
  have hb : base x = base y := congrArg (fun p : LabeledOrbitTelescope.Model Γ => p.val.1) hxy
  have hh : height x.val = height y.val :=
    congrArg (fun p : LabeledOrbitTelescope.Model Γ => p.val.2) hxy
  obtain ⟨n, k, s, _, hx⟩ := x.property
  obtain ⟨m, k', s', _, hy⟩ := y.property
  let w : LabeledSimplexCoordinates Γ (simplex n k s) :=
    ⟨x.val.val, mem_coordinates_of_support_subset x.val _ hx⟩
  let w' : LabeledSimplexCoordinates Γ (simplex m k' s') :=
    ⟨y.val.val, mem_coordinates_of_support_subset y.val _ hy⟩
  have hbx : ∀ u, (base x).val u = baseCoordinates (chart _ w) u := fun _ => rfl
  have hby : ∀ u, (base x).val u = baseCoordinates (chart _ w') u := by
    intro u
    rw [hb]
    rfl
  apply Subtype.ext
  rcases lt_trichotomy n m with hnm | hnm | hmn
  · exact different_slab_unique n m k k' hnm s s' w w' (base x) hbx hby hh
  · subst m
    exact same_slab_unique n k k' s s' w w' (base x) hbx hby hh
  · exact (different_slab_unique m n k' k hmn s' s w' w (base x) hby hbx hh.symm).symm

/-- Staircase realization and geometric telescope have the same points. -/
theorem projection_bijective : Function.Bijective (projection (Γ := Γ)) :=
  ⟨projection_injective, LabeledPrismInverse.projection_surjective⟩

end BC4lean.ProperActions.LabeledPrismProjection

