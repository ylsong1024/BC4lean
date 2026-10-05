import BC4lean.LabeledOrbitRealization
import Mathlib.Topology.Algebra.ConstMulAction

noncomputable section
namespace BC4lean.ProperActions.LabeledOrbitRealization
variable {Γ : Type*} [Group Γ]

/-- Transport finite barycentric coordinates along a group element. -/
def translateCoordinates (g : Γ) (s : LabeledOrbitSimplex Γ)
    (w : LabeledSimplexCoordinates Γ s) :
    LabeledSimplexCoordinates Γ (s.translate g) := by
  classical
  refine ⟨fun v => w.val (g⁻¹ • v), ?_, ?_, ?_⟩
  · intro v
    exact w.property.1 _
  · intro v hv
    apply w.property.2.1
    intro hw
    apply hv
    exact Finset.mem_image.mpr ⟨g⁻¹ • v, hw, by simp⟩
  · change ∑ v ∈ s.vertices.image (fun v => g • v), w.val (g⁻¹ • v) = 1
    rw [Finset.sum_image]
    · simpa using w.property.2.2
    · intro a _ b _ h
      exact (MulAction.injective g) h

/-- The action permutes barycentric coordinates and keeps the factor labels. -/
def translate (g : Γ) (x : LabeledOrbitRealization Γ) : LabeledOrbitRealization Γ := by
  refine ⟨fun v => x.val (g⁻¹ • v), ?_⟩
  obtain ⟨s, hs⟩ := x.property
  exact ⟨s.translate g, (translateCoordinates g s ⟨x.val, hs⟩).property⟩

instance : MulAction Γ (LabeledOrbitRealization Γ) where
  smul := translate
  one_smul x := by
    apply Subtype.ext
    funext v
    change x.val ((1 : Γ)⁻¹ • v) = x.val v
    simp
  mul_smul g h x := by
    apply Subtype.ext
    funext v
    change x.val ((g * h)⁻¹ • v) = x.val (h⁻¹ • (g⁻¹ • v))
    simp [mul_smul]

@[simp] theorem smul_coordinate (g : Γ) (x : LabeledOrbitRealization Γ)
    (v : LabeledOrbitVertex Γ) : (g • x).val v = x.val (g⁻¹ • v) := rfl

theorem continuous_translateCoordinates (g : Γ) (s : LabeledOrbitSimplex Γ) :
    Continuous (translateCoordinates g s) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  exact (continuous_apply (g⁻¹ • v)).comp continuous_subtype_val

theorem continuous_smul (g : Γ) :
    Continuous (fun x : LabeledOrbitRealization Γ => g • x) := by
  apply (continuous_iff _).mpr
  intro s
  exact (continuous_chart (s.translate g)).comp (continuous_translateCoordinates g s)

instance : ContinuousConstSMul Γ (LabeledOrbitRealization Γ) where
  continuous_const_smul := continuous_smul

/-- Label injectivity forces a point stabilizer to fix every active vertex. -/
theorem fixes_vertex_of_smul_eq {g : Γ} {x : LabeledOrbitRealization Γ}
    (hg : g • x = x) {v : LabeledOrbitVertex Γ} (hv : x.val v ≠ 0) : g • v = v := by
  have he : x.val (g • v) = x.val v := by
    have h := congrArg (fun y : LabeledOrbitRealization Γ => y.val (g • v)) hg
    simpa using h.symm
  exact x.labels_injective_support (by simpa [he] using hv) hv rfl

/-- Every realization point has finite isotropy. -/
theorem finite_fixing (x : LabeledOrbitRealization Γ) :
    ({g : Γ | g • x = x} : Set Γ).Finite := by
  obtain ⟨v, hv⟩ := x.exists_nonzero
  apply (FiniteOrbitVertex.finite_fixing Γ v.2).subset
  intro g hg
  exact congrArg Prod.snd (fixes_vertex_of_smul_eq hg hv)

theorem stabilizer_finite (x : LabeledOrbitRealization Γ) :
    Finite (MulAction.stabilizer Γ x) := by
  exact (finite_fixing x).to_subtype


/-- Fixed realization points have precisely pointwise-fixed active vertices. -/
theorem fixed_iff_support_fixed (H : Subgroup Γ) (x : LabeledOrbitRealization Γ) :
    (∀ h : H, (h : Γ) • x = x) ↔
      ∀ v, x.val v ≠ 0 → ∀ h : H, (h : Γ) • v = v := by
  constructor
  · intro hx v hv h
    exact fixes_vertex_of_smul_eq (hx h) hv
  · intro hv h
    apply Subtype.ext
    funext v
    change x.val ((h : Γ)⁻¹ • v) = x.val v
    by_cases hn : x.val v ≠ 0
    · have he : (h : Γ)⁻¹ • v = v := by simpa using hv v hn h⁻¹
      rw [he]
    · by_cases hi : x.val ((h : Γ)⁻¹ • v) ≠ 0
      · have he := hv ((h : Γ)⁻¹ • v) hi h
        have hvfix : (h : Γ)⁻¹ • v = v := by simpa using he.symm
        rw [hvfix]
      · simp_all

/-- The finite simplex consisting exactly of nonzero coordinates. -/
def supportSimplex (x : LabeledOrbitRealization Γ) : LabeledOrbitSimplex Γ := by
  classical
  let s := x.property.choose
  exact s.ofSubset (s.vertices.filter (fun v => x.val v ≠ 0)) (Finset.filter_subset _ _)

@[simp] theorem mem_supportSimplex (x : LabeledOrbitRealization Γ)
    (v : LabeledOrbitVertex Γ) : v ∈ (supportSimplex x).vertices ↔ x.val v ≠ 0 := by
  classical
  change v ∈ x.property.choose.vertices.filter (fun v => x.val v ≠ 0) ↔ _
  rw [Finset.mem_filter]
  constructor
  · exact And.right
  · intro hv
    refine ⟨?_, hv⟩
    by_contra hn
    exact hv (x.property.choose_spec.2.1 v hn)


/-- Removing zero coordinates gives a chart for the same point. -/
theorem mem_coordinates_supportSimplex (x : LabeledOrbitRealization Γ) :
    x.val ∈ LabeledSimplexCoordinates Γ (supportSimplex x) := by
  classical
  refine ⟨x.property.choose_spec.1, ?_, ?_⟩
  · intro v hv
    simpa using hv
  · change ∑ v ∈ x.property.choose.vertices.filter (fun v => x.val v ≠ 0), x.val v = 1
    rw [Finset.sum_filter]
    calc
      (∑ v ∈ x.property.choose.vertices, if x.val v ≠ 0 then x.val v else 0) =
          ∑ v ∈ x.property.choose.vertices, x.val v := by
        apply Finset.sum_congr rfl
        intro v _
        split_ifs with hv
        · rfl
        · simp_all
      _ = 1 := x.property.choose_spec.2.2

theorem supportSimplex_fixed (H : Subgroup Γ) (x : LabeledOrbitRealization Γ)
    (hx : ∀ h : H, (h : Γ) • x = x) :
    ∀ h : H, (h : Γ) • supportSimplex x = supportSimplex x := by
  intro h
  apply ((supportSimplex x).stabilizes_iff_smul_eq (h : Γ)).mp
  intro v
  simp only [mem_supportSimplex]
  constructor
  · intro hv
    rw [fixes_vertex_of_smul_eq (hx h) hv]
    exact hv
  · intro hv
    have he := fixes_vertex_of_smul_eq (hx h⁻¹) hv
    have he' : v = (h : Γ) • v := by simpa using he
    rw [he']
    exact hv


theorem fixed_iff_supportSimplex_fixed (H : Subgroup Γ) (x : LabeledOrbitRealization Γ) :
    (∀ h : H, (h : Γ) • x = x) ↔
      ∀ h : H, (h : Γ) • supportSimplex x = supportSimplex x := by
  constructor
  · exact supportSimplex_fixed H x
  · intro hx
    apply (fixed_iff_support_fixed H x).mpr
    intro v hv h
    exact (supportSimplex x).fixes_vertex_of_stabilizes
      (((supportSimplex x).stabilizes_iff_smul_eq (h : Γ)).mpr (hx h))
      ((mem_supportSimplex x v).mpr hv)

/-- Each subgroup-fixed point is represented by a subgroup-fixed finite chart. -/
theorem exists_fixed_chart (H : Subgroup Γ) (x : LabeledOrbitRealization Γ)
    (hx : ∀ h : H, (h : Γ) • x = x) :
    ∃ s : LabeledOrbitSimplex Γ, (∀ h : H, (h : Γ) • s = s) ∧
      ∃ w : LabeledSimplexCoordinates Γ s, chart s w = x := by
  refine ⟨supportSimplex x, supportSimplex_fixed H x hx,
    ⟨x.val, mem_coordinates_supportSimplex x⟩, ?_⟩
  rfl

end BC4lean.ProperActions.LabeledOrbitRealization



