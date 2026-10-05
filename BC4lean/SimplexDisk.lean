import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Full-dimensional coordinates for a standard simplex -/
noncomputable section
namespace BC4lean.ProperActions
variable (ι : Type*) [Fintype ι]

/-- Omit one vertex: the remaining coordinates are nonnegative with sum at most one. -/
def TruncatedSimplex : Set (EuclideanSpace ℝ ι) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

/-- The omitted coordinate is one minus the sum of all remaining coordinates. -/
def truncatedToSimplex (x : TruncatedSimplex ι) : stdSimplex ℝ (Option ι) := by
  refine ⟨fun i => i.elim (1 - ∑ j, x.val j) (fun j => x.val j), ?_, ?_⟩
  · intro i
    cases i with
    | none => exact sub_nonneg.mpr x.property.2
    | some j => exact x.property.1 j
  · simp

/-- Projection away from the distinguished vertex. -/
def simplexToTruncated (x : stdSimplex ℝ (Option ι)) : TruncatedSimplex ι := by
  refine ⟨WithLp.toLp 2 (fun i => x.val (some i)), ?_, ?_⟩
  · intro i
    exact x.property.1 (some i)
  · have hs := x.property.2
    simp only [Fintype.sum_option] at hs
    have hn := x.property.1 none
    change ∑ i, x.val (some i) ≤ 1
    linarith

/-- A finite standard simplex is a convex body in its affine dimension. -/
def simplexTruncatedHomeomorph : stdSimplex ℝ (Option ι) ≃ₜ TruncatedSimplex ι where
  toFun := simplexToTruncated ι
  invFun := truncatedToSimplex ι
  left_inv x := by
    apply Subtype.ext
    funext i
    cases i with
    | none =>
      have hs := x.property.2
      simp only [Fintype.sum_option] at hs
      change 1 - ∑ j, x.val (some j) = x.val none
      linarith
    | some j => rfl
  right_inv x := by
    apply Subtype.ext
    apply (WithLp.equiv 2 (ι → ℝ)).injective
    rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).comp
      (continuous_pi (fun i => (continuous_apply (some i)).comp continuous_subtype_val))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    cases i with
    | none =>
      exact continuous_const.sub (continuous_finsetSum Finset.univ (fun j _ =>
        (PiLp.continuous_apply 2 (fun _ : ι => ℝ) j).comp continuous_subtype_val))
    | some j =>
      exact (PiLp.continuous_apply 2 (fun _ : ι => ℝ) j).comp continuous_subtype_val

/-- Nonnegative coordinates and the sum inequality define a convex body. -/
theorem convex_truncatedSimplex : Convex ℝ (TruncatedSimplex ι) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    change 0 ≤ a * x i + b * y i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · change ∑ i, (a * x i + b * y i) ≤ 1
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    calc
      a * ∑ i, x i + b * ∑ i, y i ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
          (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = 1 := by simpa using hab

/-- The truncated simplex is compact in its Euclidean affine coordinates. -/
theorem isCompact_truncatedSimplex : IsCompact (TruncatedSimplex ι) := by
  let : CompactSpace (TruncatedSimplex ι) := (simplexTruncatedHomeomorph ι).compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

/-- Strictly positive coordinates with sum less than one form an open set. -/
theorem isOpen_truncatedSimplex_strict :
    IsOpen {x : EuclideanSpace ℝ ι | (∀ i, 0 < x i) ∧ ∑ i, x i < 1} := by
  have he : {x : EuclideanSpace ℝ ι | (∀ i, 0 < x i) ∧ ∑ i, x i < 1} =
      (⋂ i, {x : EuclideanSpace ℝ ι | 0 < x i}) ∩
      {x : EuclideanSpace ℝ ι | ∑ i, x i < 1} := by
    ext x
    simp
  rw [he]
  exact (isOpen_iInter_of_finite (fun i =>
    isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i))).inter
    (isOpen_lt (continuous_finsetSum Finset.univ (fun i _ =>
      PiLp.continuous_apply 2 (fun _ : ι => ℝ) i)) continuous_const)

/-- The affine-coordinate convex body has a nonempty interior, also in dimension zero. -/
theorem truncatedSimplex_interior_nonempty :
    (interior (TruncatedSimplex ι)).Nonempty := by
  let c : ℝ := 1 / ((Fintype.card ι : ℝ) + 1)
  have hd : (0 : ℝ) < (Fintype.card ι : ℝ) + 1 := by positivity
  have hc : 0 < c := div_pos zero_lt_one hd
  have hsum : (Fintype.card ι : ℝ) * c < 1 := by
    dsimp [c]
    rw [← mul_div_assoc, mul_one]
    apply (div_lt_one hd).mpr
    linarith
  let x : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun _ => c)
  have hx : x ∈ {x : EuclideanSpace ℝ ι | (∀ i, 0 < x i) ∧ ∑ i, x i < 1} := by
    refine ⟨fun _ => hc, ?_⟩
    change ∑ _ : ι, c < 1
    simpa using hsum
  have hsub : {x : EuclideanSpace ℝ ι | (∀ i, 0 < x i) ∧ ∑ i, x i < 1} ⊆
      TruncatedSimplex ι := fun _ h => ⟨fun i => le_of_lt (h.1 i), le_of_lt h.2⟩
  exact ⟨x, interior_mono hsub ((isOpen_truncatedSimplex_strict ι).interior_eq.symm ▸ hx)⟩

/-- The coordinate sum is a linear functional. -/
def euclideanCoordinateSum : EuclideanSpace ℝ ι →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' a x := by simp [← Finset.mul_sum]

/-- In positive dimension the coordinate sum is open. -/
theorem isOpenMap_euclideanCoordinateSum [Nonempty ι] :
    IsOpenMap (euclideanCoordinateSum ι) := by
  apply LinearMap.isOpenMap_of_finiteDimensional
  intro a
  classical
  let i : ι := Classical.choice inferInstance
  refine ⟨WithLp.toLp 2 (Pi.single i a), ?_⟩
  simp [euclideanCoordinateSum]

/-- The interior is exactly where every barycentric coordinate is positive. -/
theorem interior_truncatedSimplex :
    interior (TruncatedSimplex ι) =
      {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1} := by
  apply Set.Subset.antisymm
  · intro x hx
    constructor
    · intro i
      have hsub : TruncatedSimplex ι ⊆
          (fun x : EuclideanSpace ℝ ι => x i) ⁻¹' Set.Ici (0 : ℝ) :=
        fun _ h => h.1 i
      have hi := (PiLp.isOpenMap_apply 2 (fun _ : ι => ℝ) i).interior_preimage_subset_preimage_interior (interior_mono hsub hx)
      simpa only [Set.mem_preimage, interior_Ici, Set.mem_Ioi] using hi
    · cases isEmpty_or_nonempty ι with
      | inl hi =>
        let := hi
        simp
      | inr hi =>
        let := hi
        have hsub : TruncatedSimplex ι ⊆
            (euclideanCoordinateSum ι) ⁻¹' Set.Iic (1 : ℝ) := fun _ h => h.2
        have hs := (isOpenMap_euclideanCoordinateSum ι).interior_preimage_subset_preimage_interior (interior_mono hsub hx)
        simpa only [Set.mem_preimage, interior_Iic, Set.mem_Iio,
          euclideanCoordinateSum, LinearMap.coe_mk, AddHom.coe_mk] using hs
  · intro x hx
    have hsub : {x : EuclideanSpace ℝ ι | (∀ i, 0 < x i) ∧ ∑ i, x i < 1} ⊆
        TruncatedSimplex ι := fun _ h => ⟨fun i => le_of_lt (h.1 i), le_of_lt h.2⟩
    exact interior_mono hsub ((isOpen_truncatedSimplex_strict ι).interior_eq.symm ▸ hx)

/-- Vanishing barycentric coordinates are exactly the Euclidean frontier. -/
theorem mem_frontier_truncatedSimplex_iff (x : TruncatedSimplex ι) :
    x.val ∈ frontier (TruncatedSimplex ι) ↔
      ∃ i : Option ι, (truncatedToSimplex ι x).val i = 0 := by
  classical
  rw [frontier, (isCompact_truncatedSimplex ι).isClosed.closure_eq]
  simp only [Set.mem_sdiff, x.property, true_and, interior_truncatedSimplex,
    Set.mem_ofPred_eq]
  constructor
  · intro hn
    by_cases he : ∑ i, x.val i = 1
    · refine ⟨none, ?_⟩
      change 1 - ∑ i, x.val i = 0
      rw [he, sub_self]
    · have hs : ∑ i, x.val i < 1 := lt_of_le_of_ne x.property.2 he
      have hp : ¬ ∀ i, 0 < x.val i := fun hp => hn ⟨hp, hs⟩
      obtain ⟨i, hi⟩ := not_forall.mp hp
      exact ⟨some i, le_antisymm (le_of_not_gt hi) (x.property.1 i)⟩
  · rintro ⟨i, hi⟩ hp
    cases i with
    | none =>
      change 1 - ∑ i, x.val i = 0 at hi
      linarith [hp.2]
    | some i =>
      have hz : x.val i = 0 := hi
      have hpos := hp.1 i
      linarith

/-- Radial rescaling sends the simplex body to the Euclidean closed disk and its
frontier to the Euclidean sphere. This is an actual ambient homeomorphism. -/
theorem exists_truncatedSimplex_disk_homeomorph :
    ∃ h : EuclideanSpace ℝ ι ≃ₜ EuclideanSpace ℝ ι,
      h '' interior (TruncatedSimplex ι) = Metric.ball 0 1 ∧
      h '' TruncatedSimplex ι = Metric.closedBall 0 1 ∧
      h '' frontier (TruncatedSimplex ι) = Metric.sphere 0 1 := by
  obtain ⟨h, hi, hc, hf⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (convex_truncatedSimplex ι) (truncatedSimplex_interior_nonempty ι)
    (isCompact_truncatedSimplex ι).isBounded
  exact ⟨h, hi, (isCompact_truncatedSimplex ι).isClosed.closure_eq ▸ hc, hf⟩

/-- A standard simplex and its barycentric boundary are a Euclidean disk pair. -/
theorem exists_simplexDiskHomeomorph :
    ∃ e : stdSimplex ℝ (Option ι) ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ ι) 1,
      ∀ x, (∃ i, x.val i = 0) ↔ (e x).val ∈ Metric.sphere (0 : EuclideanSpace ℝ ι) 1 := by
  obtain ⟨h, _, hc, hf⟩ := exists_truncatedSimplex_disk_homeomorph ι
  let e := (simplexTruncatedHomeomorph ι).trans
    ((h.image (TruncatedSimplex ι)).trans (Homeomorph.setCongr hc))
  refine ⟨e, ?_⟩
  intro x
  have hleft : truncatedToSimplex ι (simplexToTruncated ι x) = x :=
    (simplexTruncatedHomeomorph ι).left_inv x
  have hz : (∃ i, x.val i = 0) ↔
      (simplexToTruncated ι x).val ∈ frontier (TruncatedSimplex ι) := by
    rw [mem_frontier_truncatedSimplex_iff, hleft]
  rw [hz]
  change (simplexToTruncated ι x).val ∈ frontier (TruncatedSimplex ι) ↔
    h (simplexToTruncated ι x).val ∈ Metric.sphere (0 : EuclideanSpace ℝ ι) 1
  rw [← hf]
  constructor
  · intro hx
    exact ⟨_, hx, rfl⟩
  · rintro ⟨y, hy, he⟩
    exact h.injective he ▸ hy

/-- Reindexing finite vertices preserves the simplex topology. -/
def simplexReindexHomeomorph {κ : Type*} [Fintype κ] (e : ι ≃ κ) :
    stdSimplex ℝ ι ≃ₜ stdSimplex ℝ κ where
  toFun x := ⟨fun i => x.val (e.symm i), fun i => x.property.1 (e.symm i),
    by rw [e.symm.sum_comp]; exact x.property.2⟩
  invFun x := ⟨fun i => x.val (e i), fun i => x.property.1 (e i),
    by rw [e.sum_comp]; exact x.property.2⟩
  left_inv x := by apply Subtype.ext; funext i; simp
  right_inv x := by apply Subtype.ext; funext i; simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi (fun i => (continuous_apply (e.symm i)).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi (fun i => (continuous_apply (e i)).comp continuous_subtype_val)

/-- Reindexing also preserves the barycentric boundary. -/
theorem simplexReindex_boundary {κ : Type*} [Fintype κ] (e : ι ≃ κ)
    (x : stdSimplex ℝ ι) :
    (∃ i, x.val i = 0) ↔ ∃ j, (simplexReindexHomeomorph ι e x).val j = 0 := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨e i, by simpa [simplexReindexHomeomorph] using hi⟩
  · rintro ⟨j, hj⟩
    exact ⟨e.symm j, hj⟩

/-- A nonempty finite simplex is a disk of its actual dimension, with its full
barycentric boundary sent to the sphere. -/
theorem exists_finiteSimplexDiskHomeomorph (v : ι) :
    ∃ e : stdSimplex ℝ ι ≃ₜ
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin (Fintype.card ι - 1))) 1,
      ∀ x, (∃ i, x.val i = 0) ↔
        (e x).val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (Fintype.card ι - 1))) 1 := by
  classical
  let κ := {j : ι // j ≠ v}
  let r := simplexReindexHomeomorph ι (Equiv.optionSubtypeNe v).symm
  obtain ⟨q, hq⟩ := exists_simplexDiskHomeomorph κ
  have hk : Fintype.card κ = Fintype.card ι - 1 := by
    have hc := Fintype.card_congr (Equiv.optionSubtypeNe v)
    simp only [Fintype.card_option] at hc
    change Fintype.card κ + 1 = Fintype.card ι at hc
    omega
  let L := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFinOfCardEq hk)
  let d : Metric.closedBall (0 : EuclideanSpace ℝ κ) 1 ≃ₜ
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin (Fintype.card ι - 1))) 1 :=
    L.toHomeomorph.subtype (fun x => by
      simp only [Metric.mem_closedBall, dist_zero_right]
      change ‖x‖ ≤ 1 ↔ ‖L x‖ ≤ 1
      rw [L.norm_map])
  refine ⟨r.trans (q.trans d), ?_⟩
  intro x
  rw [simplexReindex_boundary ι (Equiv.optionSubtypeNe v).symm x, hq]
  change (q (r x)).val ∈ Metric.sphere (0 : EuclideanSpace ℝ κ) 1 ↔
    L (q (r x)).val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (Fintype.card ι - 1))) 1
  simp only [Metric.mem_sphere, dist_zero_right, L.norm_map]

end BC4lean.ProperActions
