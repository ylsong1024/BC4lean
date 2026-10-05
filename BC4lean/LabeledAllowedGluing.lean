import BC4lean.LabeledAllowedSkeletalColimit
import BC4lean.LabeledSkeletalGluing

/-! # Actual finite-chart descent on invariant face subcomplexes -/
noncomputable section
namespace BC4lean.ProperActions.LabeledOrbitRealization
variable {Γ : Type*} [Group Γ]
variable {Y : Type*} [TopologicalSpace Y]
variable (A : Set (LabeledOrbitSimplex Γ))
variable [Fact (∀ (g : Γ) (s : LabeledOrbitSimplex Γ), s ∈ A → g • s ∈ A)]
variable (hA : ∀ {s t : LabeledOrbitSimplex Γ}, s ∈ A → t.vertices ⊆ s.vertices → t ∈ A)

/-- The actual boundary point in the old allowed skeleton. -/
def allowedBoundaryPoint (n : ℕ) (s : LabeledOrbitSimplex Γ) (ha : s ∈ A)
    (hs : s.vertices.card = n + 1) (w : LabeledSimplexCoordinates Γ s)
    (hw : w ∈ chartBoundary s) : allowedSkeletalCarrier A n :=
  ⟨allowedChart A hA s ha w, by
    have he : s.vertices.card - 1 = n := by omega
    exact he ▸ labeledChartBoundary_mem_skeletal s w hw⟩

/-- Use the old stage at boundary points and the unique support chart elsewhere. -/
def allowedGlue (n : ℕ) (f : C(allowedSkeletalCarrier A n,Y))
    (u : ∀ s : LabeledOrbitSimplex Γ, s ∈ A → s.vertices.card = n + 1 →
      C(LabeledSimplexCoordinates Γ s,Y))
    (x : allowedSkeletalCarrier A (n + 1)) : Y := by
  classical
  exact if hx : x.val ∈ allowedSkeletalCarrier A n then f ⟨x.val,hx⟩ else
    u (supportSimplex x.val.val) x.val.property (by
      have hl := x.property
      change (supportSimplex x.val.val).vertices.card ≤ n + 1 at hl
      change ¬(supportSimplex x.val.val).vertices.card ≤ n at hx
      omega) ⟨x.val.val.val,mem_coordinates_supportSimplex x.val.val⟩

theorem allowedGlue_old (n : ℕ) (f : C(allowedSkeletalCarrier A n,Y))
    (u : ∀ s : LabeledOrbitSimplex Γ, s ∈ A → s.vertices.card = n + 1 →
      C(LabeledSimplexCoordinates Γ s,Y)) (x : allowedSkeletalCarrier A n) :
    allowedGlue A n f u (allowedSkeletalMap A (Nat.le_succ n) x) = f x := by
  simp only [allowedGlue]
  split_ifs with hx
  · rfl
  · exact False.elim (hx x.property)

omit [Fact (∀ (g : Γ) (s : LabeledOrbitSimplex Γ), s ∈ A → g • s ∈ A)] in
private theorem allowedChartMap_congr (n : ℕ)
    (u : ∀ s : LabeledOrbitSimplex Γ, s ∈ A → s.vertices.card = n + 1 →
      C(LabeledSimplexCoordinates Γ s,Y))
    {s t : LabeledOrbitSimplex Γ} (ha : s ∈ A) (hb : t ∈ A)
    (hs : s.vertices.card = n + 1) (ht : t.vertices.card = n + 1)
    (he : s = t) (w : LabeledSimplexCoordinates Γ s) (z : LabeledSimplexCoordinates Γ t)
    (hw : w.val = z.val) : u s ha hs w = u t hb ht z := by
  subst t
  have hz : w = z := Subtype.ext hw
  subst z
  rfl

omit [Fact (∀ (g : Γ) (s : LabeledOrbitSimplex Γ), s ∈ A → g • s ∈ A)] in
theorem allowedGlue_chart (n : ℕ) (f : C(allowedSkeletalCarrier A n,Y))
    (u : ∀ s : LabeledOrbitSimplex Γ, s ∈ A → s.vertices.card = n + 1 →
      C(LabeledSimplexCoordinates Γ s,Y))
    (hb : ∀ s (ha : s ∈ A) (hs : s.vertices.card = n + 1) w (hw : w ∈ chartBoundary s),
      u s ha hs w = f (allowedBoundaryPoint A hA n s ha hs w hw))
    (s : LabeledOrbitSimplex Γ) (ha : s ∈ A) (hs : s.vertices.card = n + 1)
    (w : LabeledSimplexCoordinates Γ s) :
    allowedGlue A n f u (boundedAllowedSkeletalChart A hA (n + 1) s ha (by omega) w) =
      u s ha hs w := by
  classical
  have hne : s.vertices.Nonempty := Finset.card_pos.mp (by omega)
  simp only [allowedGlue]
  split_ifs with hx
  · have hw : w ∈ chartBoundary s :=
      (labeledChart_boundary_iff_skeletal s hne w).mpr (by
        have he : s.vertices.card - 1 = n := by omega
        exact he.symm ▸ hx)
    exact (hb s ha hs w hw).symm
  · have hw : ∀ v ∈ s.vertices, w.val v ≠ 0 := by
      intro v hv hz
      apply hx
      have he : s.vertices.card - 1 = n := by omega
      exact he ▸ labeledChartBoundary_mem_skeletal s w ⟨v,hv,hz⟩
    have he := (supportSimplex_chart_eq_iff s w).mpr hw
    exact allowedChartMap_congr A n u _ ha _ hs he _ w rfl

omit [Fact (∀ (g : Γ) (s : LabeledOrbitSimplex Γ), s ∈ A → g • s ∈ A)] in
theorem continuous_allowedGlue (n : ℕ) (f : C(allowedSkeletalCarrier A n,Y))
    (u : ∀ s : LabeledOrbitSimplex Γ, s ∈ A → s.vertices.card = n + 1 →
      C(LabeledSimplexCoordinates Γ s,Y))
    (hb : ∀ s (ha : s ∈ A) (hs : s.vertices.card = n + 1) w (hw : w ∈ chartBoundary s),
      u s ha hs w = f (allowedBoundaryPoint A hA n s ha hs w hw)) :
    Continuous (allowedGlue A n f u) := by
  apply (continuous_iff_allowedSkeletalCharts A hA (n + 1) _).mpr
  intro s ha hs
  by_cases hl : s.vertices.card ≤ n
  · have he : allowedGlue A n f u ∘ boundedAllowedSkeletalChart A hA (n + 1) s ha hs =
        f ∘ boundedAllowedSkeletalChart A hA n s ha hl := by
      funext w
      simp only [Function.comp_apply,allowedGlue]
      split_ifs with hx
      · rfl
      · exact False.elim (hx ((mem_skeletalCarrier_iff n _).mpr ⟨s,hl,w.property⟩))
    rw [he]
    exact f.continuous.comp (continuous_boundedAllowedSkeletalChart A hA n s ha hl)
  · have hc : s.vertices.card = n + 1 := by omega
    have he : allowedGlue A n f u ∘ boundedAllowedSkeletalChart A hA (n + 1) s ha hs =
        u s ha hc := by
      funext w
      exact allowedGlue_chart A hA n f u hb s ha hc w
    rw [he]
    exact (u s ha hc).continuous

end BC4lean.ProperActions.LabeledOrbitRealization
