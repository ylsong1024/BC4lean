import BC4lean.LabeledSkeletalTopology
import BC4lean.LabeledOrbitCells
import BC4lean.LabeledSimplexOrbits

/-! # Continuous descent across all top-dimensional simplex charts

This is the actual topological gluing statement for the skeletal filtration.
It does not by itself identify the equivariant chart coproduct with orbit disks.
-/
noncomputable section
namespace BC4lean.ProperActions.LabeledOrbitRealization
variable {Γ : Type*} [Group Γ]
variable {Y : Type*} [TopologicalSpace Y]

/-- Agreement after identifying equal simplex vertex sets. -/
theorem chartMap_congr (n : ℕ)
    (u : ∀ s : LabeledOrbitSimplex Γ, s.vertices.card = n + 1 →
      C(LabeledSimplexCoordinates Γ s, Y))
    {s t : LabeledOrbitSimplex Γ} (hs : s.vertices.card = n + 1)
    (ht : t.vertices.card = n + 1) (he : s = t)
    (w : LabeledSimplexCoordinates Γ s) (z : LabeledSimplexCoordinates Γ t)
    (hw : w.val = z.val) : u s hs w = u t ht z := by
  subst t
  have hz : w = z := Subtype.ext hw
  subst z
  rfl

/-- Set-theoretic descent: use the old skeleton on the boundary and the unique
support simplex in each newly attached interior. -/
def skeletalGlue (n : ℕ) (f : C(SkeletalSpace (Γ := Γ) n, Y))
    (u : ∀ s : LabeledOrbitSimplex Γ, s.vertices.card = n + 1 →
      C(LabeledSimplexCoordinates Γ s, Y))
    (x : SkeletalSpace (Γ := Γ) (n + 1)) : Y := by
  classical
  exact if hx : x.val ∈ skeletalCarrier n then f ⟨x.val,hx⟩ else
    u (supportSimplex x.val) (by
      have hl := x.property
      change (supportSimplex x.val).vertices.card ≤ n + 1 at hl
      change ¬ (supportSimplex x.val).vertices.card ≤ n at hx
      omega) ⟨x.val.val,mem_coordinates_supportSimplex x.val⟩

/-- Descent restricts to the prescribed map on the old skeleton. -/
theorem skeletalGlue_old (n : ℕ) (f : C(SkeletalSpace (Γ := Γ) n, Y))
    (u : ∀ s : LabeledOrbitSimplex Γ, s.vertices.card = n + 1 →
      C(LabeledSimplexCoordinates Γ s, Y)) (x : SkeletalSpace (Γ := Γ) n) :
    skeletalGlue n f u (skeletalMap (Nat.le_succ n) x) = f x := by
  simp only [skeletalGlue]
  split_ifs with hx
  · rfl
  · exact False.elim (hx x.property)

/-- On a top-dimensional chart, boundary agreement yields exactly the prescribed
continuous chart map, including all proper faces. -/
theorem skeletalGlue_chart (n : ℕ) (f : C(SkeletalSpace (Γ := Γ) n, Y))
    (u : ∀ s : LabeledOrbitSimplex Γ, s.vertices.card = n + 1 →
      C(LabeledSimplexCoordinates Γ s, Y))
    (hb : ∀ s (hs : s.vertices.card = n + 1) w
      (hw : w ∈ chartBoundary s),
      u s hs w = f ⟨chart s w, by
        have he : s.vertices.card - 1 = n := by omega
        exact he ▸ labeledChartBoundary_mem_skeletal s w hw⟩)
    (s : LabeledOrbitSimplex Γ) (hs : s.vertices.card = n + 1)
    (w : LabeledSimplexCoordinates Γ s) :
    skeletalGlue n f u (boundedSkeletalChart (n + 1) s (by omega) w) = u s hs w := by
  classical
  have hne : s.vertices.Nonempty := Finset.card_pos.mp (by omega)
  simp only [skeletalGlue]
  split_ifs with hx
  · have hw : w ∈ chartBoundary s :=
      (labeledChart_boundary_iff_skeletal s hne w).mpr (by
        have he : s.vertices.card - 1 = n := by omega
        exact he.symm ▸ hx)
    exact (hb s hs w hw).symm
  · have hw : ∀ v ∈ s.vertices, w.val v ≠ 0 := by
      intro v hv hz
      apply hx
      have he : s.vertices.card - 1 = n := by omega
      exact he ▸ labeledChartBoundary_mem_skeletal s w ⟨v,hv,hz⟩
    have he := (supportSimplex_chart_eq_iff s w).mpr hw
    exact chartMap_congr n u _ hs he _ w rfl

/-- The gluing map is continuous in the actual induced topology of the next
skeleton; no separate continuity assumption on the descended map is needed. -/
theorem continuous_skeletalGlue (n : ℕ) (f : C(SkeletalSpace (Γ := Γ) n, Y))
    (u : ∀ s : LabeledOrbitSimplex Γ, s.vertices.card = n + 1 →
      C(LabeledSimplexCoordinates Γ s, Y))
    (hb : ∀ s (hs : s.vertices.card = n + 1) w
      (hw : w ∈ chartBoundary s),
      u s hs w = f ⟨chart s w, by
        have he : s.vertices.card - 1 = n := by omega
        exact he ▸ labeledChartBoundary_mem_skeletal s w hw⟩) :
    Continuous (skeletalGlue n f u) := by
  apply (continuous_iff_boundedSkeletalCharts (n + 1) _).mpr
  intro s hs
  by_cases hl : s.vertices.card ≤ n
  · have he : skeletalGlue n f u ∘ boundedSkeletalChart (n + 1) s hs =
        f ∘ boundedSkeletalChart n s hl := by
      funext w
      simp only [Function.comp_apply, skeletalGlue]
      split_ifs with hx
      · rfl
      · exact False.elim (hx ((mem_skeletalCarrier_iff n _).mpr ⟨s,hl,w.property⟩))
    rw [he]
    exact f.continuous.comp (continuous_boundedSkeletalChart n s hl)
  · have hc : s.vertices.card = n + 1 := by omega
    have he : skeletalGlue n f u ∘ boundedSkeletalChart (n + 1) s hs = u s hc := by
      funext w
      exact skeletalGlue_chart n f u hb s hc w
    rw [he]
    exact (u s hc).continuous

omit [TopologicalSpace Y] in
/-- Maps out of the next skeleton are determined by the preceding skeleton and
all newly attached simplex charts. -/
theorem skeletal_hom_ext (n : ℕ) {f g : SkeletalSpace (Γ := Γ) (n + 1) → Y}
    (hold : ∀ x, f (skeletalMap (Nat.le_succ n) x) =
      g (skeletalMap (Nat.le_succ n) x))
    (hchart : ∀ s (hs : s.vertices.card = n + 1) w,
      f (boundedSkeletalChart (n + 1) s (by omega) w) =
        g (boundedSkeletalChart (n + 1) s (by omega) w)) : f = g := by
  funext x
  by_cases hx : x.val ∈ skeletalCarrier n
  · exact hold ⟨x.val,hx⟩
  · let s := supportSimplex x.val
    have hs : s.vertices.card = n + 1 := by
      have hl := x.property
      change s.vertices.card ≤ n + 1 at hl
      change ¬ s.vertices.card ≤ n at hx
      omega
    exact hchart s hs ⟨x.val.val,mem_coordinates_supportSimplex x.val⟩

/-- Equivariant old-skeleton and chart data descend equivariantly. The only
extra condition is the prescribed covariance of the individual chart maps. -/
theorem skeletalGlue_map_smul [MulAction Γ Y] [ContinuousConstSMul Γ Y]
    (n : ℕ) (f : EquivariantMap Γ (SkeletalSpace (Γ := Γ) n) Y)
    (u : ∀ s : LabeledOrbitSimplex Γ, s.vertices.card = n + 1 →
      C(LabeledSimplexCoordinates Γ s, Y))
    (hb : ∀ s (hs : s.vertices.card = n + 1) w
      (hw : w ∈ chartBoundary s),
      u s hs w = f ⟨chart s w, by
        have he : s.vertices.card - 1 = n := by omega
        exact he ▸ labeledChartBoundary_mem_skeletal s w hw⟩)
    (hu : ∀ s (hs : s.vertices.card = n + 1) w g,
      u (g • s) ((LabeledOrbitSimplex.card_smul g s).trans hs) (translateCoordinates g s w) =
        g • u s hs w)
    (g : Γ) (x : SkeletalSpace (Γ := Γ) (n + 1)) :
    skeletalGlue n f.toContinuousMap u (g • x) =
      g • skeletalGlue n f.toContinuousMap u x := by
  have he : (fun x => skeletalGlue n f.toContinuousMap u (g • x)) =
      (fun x => g • skeletalGlue n f.toContinuousMap u x) := by
    apply skeletal_hom_ext n
    · intro y
      have hy : g • skeletalMap (Nat.le_succ n) y = skeletalMap (Nat.le_succ n) (g • y) := rfl
      rw [hy, skeletalGlue_old, skeletalGlue_old]
      exact f.map_smul g y
    · intro s hs w
      have hc : (g • s).vertices.card = n + 1 := (LabeledOrbitSimplex.card_smul g s).trans hs
      have ht : g • boundedSkeletalChart (n + 1) s (by omega) w =
          boundedSkeletalChart (n + 1) (g • s) (by omega) (translateCoordinates g s w) := rfl
      rw [ht, skeletalGlue_chart n f.toContinuousMap u hb _ hc,
        skeletalGlue_chart n f.toContinuousMap u hb _ hs]
      exact hu s hs w g
  exact congrFun he x

end BC4lean.ProperActions.LabeledOrbitRealization
