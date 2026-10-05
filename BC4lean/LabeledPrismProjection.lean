import BC4lean.LabeledAllowedRealization
import BC4lean.LabeledAllowedAction
import BC4lean.LabeledTelescopePrisms
import BC4lean.LabeledOrbitTelescope

/-! # Geometric projection of staircase prism coordinates

Integer-height tags are decoded into a barycentric base point and a weighted
height. The forward map uses finite support and the weak chart topology.
-/
noncomputable section
open scoped BigOperators Classical
namespace BC4lean.ProperActions.LabeledPrismProjection
open LabeledOrbitRealization
variable {Γ : Type*} [Group Γ]

/-- Remove the integer height encoded in a prism vertex label. -/
def forgetVertex (v : LabeledOrbitVertex Γ) : LabeledOrbitVertex Γ :=
  ((Nat.unpair v.1).2, v.2)

/-- The integer height encoded in a prism vertex label. -/
def heightVertex (v : LabeledOrbitVertex Γ) : ℕ := (Nat.unpair v.1).1

@[simp] theorem forget_vertex (n : ℕ) (v : LabeledOrbitVertex Γ) :
    forgetVertex (LabeledTelescopePrisms.vertex n v) = v := by
  simp [forgetVertex, LabeledTelescopePrisms.vertex]

@[simp] theorem height_vertex (n : ℕ) (v : LabeledOrbitVertex Γ) :
    heightVertex (LabeledTelescopePrisms.vertex n v) = n := by
  simp [heightVertex, LabeledTelescopePrisms.vertex]

@[simp] theorem forget_smul (g : Γ) (v : LabeledOrbitVertex Γ) :
    forgetVertex (g • v) = g • forgetVertex v := rfl

@[simp] theorem heightVertex_smul (g : Γ) (v : LabeledOrbitVertex Γ) :
    heightVertex (g • v) = heightVertex v := rfl

/-- A support-independent finite weighted sum of vertex functions. -/
def weightedSum (x : LabeledOrbitRealization Γ) (f : LabeledOrbitVertex Γ → ℝ) : ℝ :=
  ∑ v ∈ (supportSimplex x).vertices, x.val v * f v

theorem weightedSum_eq_chart (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ s) (f : LabeledOrbitVertex Γ → ℝ) :
    weightedSum (chart s w) f = ∑ v ∈ s.vertices, w.val v * f v := by
  classical
  apply Finset.sum_subset (support_chart_subset s w)
  intro v _ hv
  have hz : w.val v = 0 := by
    exact not_not.mp (fun hn => hv ((mem_supportSimplex (chart s w) v).mpr hn))
  change w.val v * f v = 0
  rw [hz, zero_mul]

/-- Base coordinates add the masses of the lower and upper copies of each vertex. -/
def baseCoordinates (x : LabeledOrbitRealization Γ) (u : LabeledOrbitVertex Γ) : ℝ :=
  weightedSum x (fun v => if forgetVertex v = u then 1 else 0)

/-- Height is the barycentric average of the encoded integer heights. -/
def height (x : LabeledOrbitRealization Γ) : ℝ :=
  weightedSum x (fun v => (heightVertex v : ℝ))

theorem baseCoordinates_chart (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ s) (u : LabeledOrbitVertex Γ) :
    baseCoordinates (chart s w) u =
      ∑ v ∈ s.vertices, if forgetVertex v = u then w.val v else 0 := by
  classical
  rw [baseCoordinates, weightedSum_eq_chart]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> simp

theorem height_chart (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ s) :
    height (chart s w) = ∑ v ∈ s.vertices, w.val v * (heightVertex v : ℝ) :=
  weightedSum_eq_chart s w _

theorem forget_mem_prism {n k : ℕ} {s : LabeledOrbitSimplex Γ}
    {v : LabeledOrbitVertex Γ} (hv : v ∈ (LabeledTelescopePrisms.simplex n k s).vertices) :
    forgetVertex v ∈ s.vertices := by
  classical
  rcases Finset.mem_union.mp hv with hv | hv
  all_goals
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    simpa using (Finset.mem_filter.mp hw).1


theorem mem_lower_prism_vertex (n k : ℕ) (s : LabeledOrbitSimplex Γ)
    (u : LabeledOrbitVertex Γ) :
    LabeledTelescopePrisms.vertex n u ∈ (LabeledTelescopePrisms.simplex n k s).vertices ↔
      u ∈ s.vertices ∧ u.1 ≤ k := by
  classical
  constructor
  · intro hu
    rcases Finset.mem_union.mp hu with hu | hu
    · obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hu
      have hvu := LabeledTelescopePrisms.vertex_injective n he
      simpa only [hvu] using Finset.mem_filter.mp hv
    · obtain ⟨v, _, he⟩ := Finset.mem_image.mp hu
      exact False.elim ((LabeledTelescopePrisms.vertex_ne_vertex_succ n u v) he.symm)
  · intro hu
    exact Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr hu, rfl⟩)

theorem mem_upper_prism_vertex (n k : ℕ) (s : LabeledOrbitSimplex Γ)
    (u : LabeledOrbitVertex Γ) :
    LabeledTelescopePrisms.vertex (n + 1) u ∈ (LabeledTelescopePrisms.simplex n k s).vertices ↔
      u ∈ s.vertices ∧ k ≤ u.1 := by
  classical
  constructor
  · intro hu
    rcases Finset.mem_union.mp hu with hu | hu
    · obtain ⟨v, _, he⟩ := Finset.mem_image.mp hu
      exact False.elim ((LabeledTelescopePrisms.vertex_ne_vertex_succ n v u) he)
    · obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hu
      have hvu := LabeledTelescopePrisms.vertex_injective (n + 1) he
      simpa only [hvu] using Finset.mem_filter.mp hv
  · intro hu
    exact Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr hu, rfl⟩)

/-- The only two encoded vertices over an old vertex carry its projected mass. -/
theorem baseCoordinates_whole_prism (n k : ℕ) (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ (LabeledTelescopePrisms.simplex n k s))
    (u : LabeledOrbitVertex Γ) :
    baseCoordinates (chart _ w) u =
      w.val (LabeledTelescopePrisms.vertex n u) +
        w.val (LabeledTelescopePrisms.vertex (n + 1) u) := by
  classical
  rw [baseCoordinates_chart]
  change (∑ v ∈ LabeledTelescopePrisms.vertices n k s,
    if forgetVertex v = u then w.val v else 0) = _
  unfold LabeledTelescopePrisms.vertices
  have hd : Disjoint
      ((s.vertices.filter (fun v => v.1 ≤ k)).image (LabeledTelescopePrisms.vertex n))
      ((s.vertices.filter (fun v => k ≤ v.1)).image (LabeledTelescopePrisms.vertex (n + 1))) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hv
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hw
    exact LabeledTelescopePrisms.vertex_ne_vertex_succ n a b (ha.trans hb.symm)
  rw [Finset.sum_union hd,
    Finset.sum_image (fun _ _ _ _ h => LabeledTelescopePrisms.vertex_injective n h),
    Finset.sum_image (fun _ _ _ _ h => LabeledTelescopePrisms.vertex_injective (n + 1) h)]
  simp only [forget_vertex]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  congr 1
  · split_ifs with hu
    · rfl
    · exact (w.property.2.1 _ (by
        intro h
        exact hu (Finset.mem_filter.mpr ((mem_lower_prism_vertex n k s u).mp h)))).symm
  · split_ifs with hu
    · rfl
    · exact (w.property.2.1 _ (by
        intro h
        exact hu (Finset.mem_filter.mpr ((mem_upper_prism_vertex n k s u).mp h)))).symm

theorem height_mem_prism {n k : ℕ} {s : LabeledOrbitSimplex Γ}
    {v : LabeledOrbitVertex Γ} (hv : v ∈ (LabeledTelescopePrisms.simplex n k s).vertices) :
    heightVertex v = n ∨ heightVertex v = n + 1 := by
  classical
  rcases Finset.mem_union.mp hv with hv | hv
  · obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact Or.inl (height_vertex n w)
  · obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact Or.inr (height_vertex (n + 1) w)

/-- Every face of a staircase prism projects into its base simplex. -/
theorem base_mem_coordinates {n k : ℕ} {s t : LabeledOrbitSimplex Γ}
    (ht : t.vertices ⊆ (LabeledTelescopePrisms.simplex n k s).vertices)
    (w : LabeledSimplexCoordinates Γ t) :
    baseCoordinates (chart t w) ∈ LabeledSimplexCoordinates Γ s := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro u
    rw [baseCoordinates_chart]
    apply Finset.sum_nonneg
    intro v _
    split_ifs
    · exact w.property.1 v
    · exact le_rfl
  · intro u hu
    rw [baseCoordinates_chart]
    apply Finset.sum_eq_zero
    intro v hv
    have hne : forgetVertex v ≠ u := fun he => hu (he ▸ forget_mem_prism (ht hv))
    simp [hne]
  · simp_rw [baseCoordinates_chart]
    rw [Finset.sum_comm]
    calc
      (∑ v ∈ t.vertices, ∑ u ∈ s.vertices, if forgetVertex v = u then w.val v else 0) =
          ∑ v ∈ t.vertices, w.val v := by
        apply Finset.sum_congr rfl
        intro v hv
        simp [Finset.sum_ite_eq, forget_mem_prism (ht hv)]
      _ = 1 := w.property.2.2

/-- Every prism chart has height in its closed unit interval. -/
theorem height_bounds {n k : ℕ} {s t : LabeledOrbitSimplex Γ}
    (ht : t.vertices ⊆ (LabeledTelescopePrisms.simplex n k s).vertices)
    (w : LabeledSimplexCoordinates Γ t) :
    (n : ℝ) ≤ height (chart t w) ∧ height (chart t w) ≤ (n : ℝ) + 1 := by
  rw [height_chart]
  have hsum : ∑ v ∈ t.vertices, w.val v = 1 := w.property.2.2
  constructor
  · calc
      (n : ℝ) = (∑ v ∈ t.vertices, w.val v) * n := by rw [hsum]; simp
      _ = ∑ v ∈ t.vertices, w.val v * n := Finset.sum_mul _ _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro v hv
        apply mul_le_mul_of_nonneg_left _ (w.property.1 v)
        rcases height_mem_prism (ht hv) with he | he
        · simpa only [he] using (le_refl (n : ℝ))
        · simpa only [he, Nat.cast_add, Nat.cast_one] using
            (le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1) : (n : ℝ) ≤ n + 1)
  · calc
      (∑ v ∈ t.vertices, w.val v * (heightVertex v : ℝ)) ≤
          ∑ v ∈ t.vertices, w.val v * ((n : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro v hv
        apply mul_le_mul_of_nonneg_left _ (w.property.1 v)
        rcases height_mem_prism (ht hv) with he | he
        · simpa only [he] using
            (le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1) : (n : ℝ) ≤ n + 1)
        · simp only [he, Nat.cast_add, Nat.cast_one, le_refl]
      _ = (∑ v ∈ t.vertices, w.val v) * ((n : ℝ) + 1) := (Finset.sum_mul _ _ _).symm
      _ = (n : ℝ) + 1 := by rw [hsum]; simp


/-- Coordinate averages are continuous on every finite chart. -/
theorem continuous_height : Continuous (height (Γ := Γ)) := by
  apply (continuous_iff _).mpr
  intro t
  change Continuous (fun w : LabeledSimplexCoordinates Γ t => height (chart t w))
  simp_rw [height_chart]
  exact continuous_finsetSum t.vertices (fun v _ =>
    ((continuous_apply v).comp continuous_subtype_val).mul_const _)

/-- The base-coordinate chart factors through the original finite base simplex. -/
def chartBaseCoordinates {n k : ℕ} {s t : LabeledOrbitSimplex Γ}
    (ht : t.vertices ⊆ (LabeledTelescopePrisms.simplex n k s).vertices)
    (w : LabeledSimplexCoordinates Γ t) : LabeledSimplexCoordinates Γ s :=
  ⟨baseCoordinates (chart t w), base_mem_coordinates ht w⟩

theorem continuous_chartBaseCoordinates {n k : ℕ} {s t : LabeledOrbitSimplex Γ}
    (ht : t.vertices ⊆ (LabeledTelescopePrisms.simplex n k s).vertices) :
    Continuous (chartBaseCoordinates ht) := by
  classical
  apply Continuous.subtype_mk
  apply continuous_pi
  intro u
  change Continuous (fun w : LabeledSimplexCoordinates Γ t => baseCoordinates (chart t w) u)
  simp_rw [baseCoordinates_chart]
  apply continuous_finsetSum
  intro v _
  split_ifs
  · exact (continuous_apply v).comp continuous_subtype_val
  · exact continuous_const

theorem baseCoordinates_smul (g : Γ) (x : LabeledOrbitRealization Γ)
    (u : LabeledOrbitVertex Γ) :
    baseCoordinates (g • x) u = baseCoordinates x (g⁻¹ • u) := by
  classical
  rw [baseCoordinates, weightedSum, supportSimplex_smul]
  change (∑ v ∈ (supportSimplex x).vertices.image (fun w => g • w),
    (g • x).val v * (if forgetVertex v = u then 1 else 0)) = _
  rw [Finset.sum_image (fun _ _ _ _ h => (MulAction.injective g) h)]
  apply Finset.sum_congr rfl
  intro v _
  simp only [smul_coordinate, inv_smul_smul, forget_smul]
  have he : g • forgetVertex v = u ↔ forgetVertex v = g⁻¹ • u := by
    constructor
    · intro h
      simpa using congrArg (fun w : LabeledOrbitVertex Γ => g⁻¹ • w) h
    · intro h
      rw [h]
      simp
  simp only [he]

theorem height_smul (g : Γ) (x : LabeledOrbitRealization Γ) : height (g • x) = height x := by
  classical
  rw [height, weightedSum, supportSimplex_smul]
  change (∑ v ∈ (supportSimplex x).vertices.image (fun w => g • w),
    (g • x).val v * (heightVertex v : ℝ)) = _
  rw [Finset.sum_image (fun _ _ _ _ h => (MulAction.injective g) h)]
  simp [height, weightedSum]

section Countable

variable [Countable Γ]

instance : Fact (∀ (g : Γ) (s : LabeledOrbitSimplex Γ),
    s ∈ LabeledTelescopePrisms.allowed → g • s ∈ LabeledTelescopePrisms.allowed) :=
  ⟨fun g _ hs => LabeledTelescopePrisms.allowed_smul hs g⟩

abbrev PrismRealization := AllowedRealization (LabeledTelescopePrisms.allowed (Γ := Γ))

private theorem base_exists (x : PrismRealization (Γ := Γ)) :
    ∃ s, baseCoordinates x.val ∈ LabeledSimplexCoordinates Γ s := by
  obtain ⟨n, k, s, _, ht⟩ := x.property
  exact ⟨s, base_mem_coordinates ht ⟨x.val.val, mem_coordinates_supportSimplex x.val⟩⟩

/-- Forget the height tags by adding barycentric masses. -/
def base (x : PrismRealization (Γ := Γ)) : LabeledOrbitRealization Γ :=
  ⟨baseCoordinates x.val, base_exists x⟩

private theorem base_in_stage (x : PrismRealization (Γ := Γ)) :
    ∃ n, base x ∈ LabeledOrbitTelescope.stage Γ n ∧
      (n : ℝ) ≤ height x.val ∧ height x.val ≤ (n : ℝ) + 1 := by
  obtain ⟨n, k, s, hs, ht⟩ := x.property
  let w : LabeledSimplexCoordinates Γ (supportSimplex x.val) :=
    ⟨x.val.val, mem_coordinates_supportSimplex x.val⟩
  have hc := base_mem_coordinates ht w
  have he : chart s ⟨baseCoordinates x.val, hc⟩ = base x := rfl
  have hb : (supportSimplex (base x)).vertices ⊆ s.vertices :=
    he ▸ support_chart_subset s ⟨baseCoordinates x.val, hc⟩
  exact ⟨n, LabeledOrbitSimplex.orbitFaces_downward hs hb, height_bounds ht w⟩

/-- The actual geometric telescope point determined by prism coordinates. -/
def projection (x : PrismRealization (Γ := Γ)) : LabeledOrbitTelescope.Model Γ :=
  ⟨(base x, height x.val), base_in_stage x⟩


/-- The base projection is continuous for the actual induced allowed topology. -/
theorem continuous_base : Continuous (base (Γ := Γ)) := by
  apply (continuous_iff_allowedCharts _ LabeledTelescopePrisms.allowed_downward _).mpr
  intro t ht
  obtain ⟨n, k, s, _, hts⟩ := ht
  exact (continuous_chart s).comp (continuous_chartBaseCoordinates hts)

/-- Prism coordinates map continuously to the geometric telescope. -/
theorem continuous_projection : Continuous (projection (Γ := Γ)) :=
  (continuous_base.prodMk (continuous_height.comp continuous_subtype_val)).subtype_mk _

/-- The projected coordinates on every allowed face are finite explicit sums. -/
theorem projection_chart_coordinates (t : LabeledOrbitSimplex Γ)
    (ht : t ∈ LabeledTelescopePrisms.allowed) (w : LabeledSimplexCoordinates Γ t)
    (u : LabeledOrbitVertex Γ) :
    (projection (allowedChart _ LabeledTelescopePrisms.allowed_downward t ht w)).val.1.val u =
      ∑ v ∈ t.vertices, if forgetVertex v = u then w.val v else 0 :=
  baseCoordinates_chart t w u

theorem projection_chart_height (t : LabeledOrbitSimplex Γ)
    (ht : t ∈ LabeledTelescopePrisms.allowed) (w : LabeledSimplexCoordinates Γ t) :
    (projection (allowedChart _ LabeledTelescopePrisms.allowed_downward t ht w)).val.2 =
      ∑ v ∈ t.vertices, w.val v * (heightVertex v : ℝ) :=
  height_chart t w


/-- The geometric projection respects the actual group actions. -/
theorem projection_smul (g : Γ) (x : PrismRealization (Γ := Γ)) :
    projection (g • x) = g • projection x := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    funext u
    exact baseCoordinates_smul g x.val u
  · exact height_smul g x.val

/-- The continuous equivariant map onto the geometric telescope. -/
def equivariantProjection : EquivariantMap Γ (PrismRealization (Γ := Γ))
    (LabeledOrbitTelescope.Model Γ) where
  toFun := projection
  continuous_toFun := continuous_projection
  map_smul' := projection_smul

end Countable

end BC4lean.ProperActions.LabeledPrismProjection
