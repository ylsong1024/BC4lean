import BC4lean.CocompactPieceRepresentatives
import BC4lean.ProperActions
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Real.Sqrt

/-! # Cutoff functions for proper cocompact discrete actions

The construction starts with a compactly supported function that is positive
somewhere on each orbit and divides it by the square root of its orbitwise
sum of squares. Properness makes that sum locally finite. No countability
assumption is needed for this construction.
-/

noncomputable section

open Topology Filter Function
open scoped Pointwise CompactlySupported

namespace BC4lean.ProperActions.Cutoff

variable {Γ X : Type*} [Group Γ] [TopologicalSpace X] [MulAction Γ X]

/-- A nonnegative compactly supported continuous function whose translates
have sum of squares one. -/
structure CutoffFunction (Γ X : Type*) [Group Γ] [TopologicalSpace X] [MulAction Γ X]
    extends CompactlySupportedContinuousMap X ℝ where
  nonneg : ∀ x, 0 ≤ toFun x
  normalized : ∀ x, ∑ᶠ g : Γ, toFun (g⁻¹ • x) ^ 2 = 1

instance : FunLike (CutoffFunction Γ X) X ℝ where
  coe c := c.toCompactlySupportedContinuousMap
  coe_injective := by
    rintro ⟨c, hc, hn⟩ ⟨d, hd, hm⟩ h
    have hcd : c = d := DFunLike.coe_injective h
    cases hcd
    rfl

instance : CompactlySupportedContinuousMapClass (CutoffFunction Γ X) X ℝ where
  map_continuous c := c.toCompactlySupportedContinuousMap.continuous
  hasCompactSupport c := c.toCompactlySupportedContinuousMap.hasCompactSupport

@[simp] theorem coe_toCompactlySupportedContinuousMap (c : CutoffFunction Γ X) :
    ⇑c.toCompactlySupportedContinuousMap = c := rfl

omit [TopologicalSpace X] in
/-- The finite orbitwise sum used for normalization. -/
def orbitSquareSum (f : X → ℝ) (x : X) : ℝ := ∑ᶠ g : Γ, f (g⁻¹ • x) ^ 2

variable [TopologicalSpace Γ] [DiscreteTopology Γ] [ProperSMul Γ X]

/-- Properness implies local finiteness of the translates of a compact set. -/
theorem locallyFinite_smul_of_isCompact [LocallyCompactSpace X]
    {K : Set X} (hK : IsCompact K) : LocallyFinite (fun g : Γ => g • K) := by
  intro x
  obtain ⟨L, hL, hLx⟩ := exists_compact_mem_nhds x
  exact ⟨L, hLx, finite_transporter hK hL⟩

/-- The translated supports of a compactly supported function are locally finite. -/
theorem locallyFinite_translated_support [LocallyCompactSpace X]
    (f : C_c(X, ℝ)) : LocallyFinite (fun g : Γ => support (fun x => f (g⁻¹ • x) ^ 2)) := by
  apply (locallyFinite_smul_of_isCompact (Γ := Γ) f.hasCompactSupport).subset
  intro g x hx
  refine ⟨g⁻¹ • x, subset_tsupport _ ?_, ?_⟩
  · simpa only [mem_support, ne_eq, pow_eq_zero_iff (by decide : 2 ≠ 0)] using hx
  · exact smul_inv_smul g x

/-- Every orbitwise square sum has finite support in the group variable. -/
theorem finite_orbitSquareSupport [LocallyCompactSpace X] (f : C_c(X, ℝ)) (x : X) :
    HasFiniteSupport (fun g : Γ => f (g⁻¹ • x) ^ 2) :=
  (locallyFinite_translated_support f).point_finite x

/-- The orbitwise square sum is continuous. -/
theorem continuous_orbitSquareSum [LocallyCompactSpace X] [ContinuousConstSMul Γ X]
    (f : C_c(X, ℝ)) : Continuous (orbitSquareSum (Γ := Γ) f) := by
  apply continuous_finsum (fun g => (f.continuous.comp (continuous_const_smul g⁻¹)).pow 2)
  exact locallyFinite_translated_support f

omit [TopologicalSpace X] [TopologicalSpace Γ] [DiscreteTopology Γ] [ProperSMul Γ X] in
/-- Reindexing the orbit sum shows that it is invariant. -/
theorem orbitSquareSum_inv_smul (f : X → ℝ) (h : Γ) (x : X) :
    orbitSquareSum (Γ := Γ) f (h⁻¹ • x) = orbitSquareSum (Γ := Γ) f x := by
  unfold orbitSquareSum
  calc
    (∑ᶠ g : Γ, f (g⁻¹ • (h⁻¹ • x)) ^ 2) =
        ∑ᶠ g : Γ, f ((h * g)⁻¹ • x) ^ 2 := by
      apply finsum_congr
      intro g
      rw [mul_inv_rev, mul_smul]
    _ = _ := finsum_comp_equiv (f := fun g : Γ => f (g⁻¹ • x) ^ 2) (Equiv.mulLeft h)

/-- An orbit-positive seed has a strictly positive orbit sum. -/
theorem orbitSquareSum_pos [LocallyCompactSpace X] (f : C_c(X, ℝ))
    (hpos : ∀ x, ∃ g : Γ, 0 < f (g⁻¹ • x)) (x : X) :
    0 < orbitSquareSum (Γ := Γ) f x := by
  apply finsum_pos (fun g => sq_nonneg _) ?_ (finite_orbitSquareSupport f x)
  obtain ⟨g, hg⟩ := hpos x
  exact ⟨g, sq_pos_of_pos hg⟩

omit [TopologicalSpace Γ] [DiscreteTopology Γ] [ProperSMul Γ X] in
/-- Compactness of the orbit space supplies a compactly supported nonnegative
seed positive somewhere on every orbit. -/
theorem exists_orbitPositive_seed [LocallyCompactSpace X] [T2Space X]
    [ContinuousConstSMul Γ X] [CompactSpace (Quotient (MulAction.orbitRel Γ X))] :
    ∃ f : C_c(X, ℝ), (∀ x, 0 ≤ f x) ∧ ∀ x, ∃ g : Γ, 0 < f (g⁻¹ • x) := by
  obtain ⟨K, hK, hrep⟩ := exists_compact_orbit_representatives (Γ := Γ) (X := X)
  obtain ⟨f, hfK, _, hfc, hfr⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
  refine ⟨⟨f, hfc⟩, fun x => (hfr x).1, ?_⟩
  intro x
  obtain ⟨g, y, hy, rfl⟩ := hrep x
  refine ⟨g, ?_⟩
  simpa only [CompactlySupportedContinuousMap.coe_mk, inv_smul_smul,
    hfK hy, Pi.one_apply] using (zero_lt_one : (0 : ℝ) < 1)

/-- Normalize an orbit-positive compactly supported seed. -/
def normalize [LocallyCompactSpace X] [ContinuousConstSMul Γ X]
    (f : C_c(X, ℝ)) (hnonneg : ∀ x, 0 ≤ f x)
    (hpos : ∀ x, ∃ g : Γ, 0 < f (g⁻¹ • x)) : CutoffFunction Γ X where
  toFun x := f x / Real.sqrt (orbitSquareSum (Γ := Γ) f x)
  continuous_toFun := f.continuous.div
    (Real.continuous_sqrt.comp (continuous_orbitSquareSum f))
    (fun x => (Real.sqrt_pos.mpr (orbitSquareSum_pos f hpos x)).ne')
  hasCompactSupport' := by
    have hc := f.hasCompactSupport.mul_right
      (f' := fun x => (Real.sqrt (orbitSquareSum (Γ := Γ) f x))⁻¹)
    change HasCompactSupport (fun x => f x * (Real.sqrt (orbitSquareSum (Γ := Γ) f x))⁻¹) at hc
    simpa only [div_eq_mul_inv] using hc
  nonneg x := div_nonneg (hnonneg x) (Real.sqrt_nonneg _)
  normalized x := by
    simp_rw [orbitSquareSum_inv_smul, div_pow, Real.sq_sqrt (orbitSquareSum_pos f hpos x).le,
      div_eq_mul_inv]
    rw [← finsum_mul]
    exact mul_inv_cancel₀ (orbitSquareSum_pos f hpos x).ne'

/-- A proper discrete action on a locally compact Hausdorff space with compact
orbit space admits a cutoff function. -/
theorem exists_cutoffFunction [LocallyCompactSpace X] [T2Space X]
    [ContinuousConstSMul Γ X] [CompactSpace (Quotient (MulAction.orbitRel Γ X))] :
    Nonempty (CutoffFunction Γ X) := by
  obtain ⟨f, hnonneg, hpos⟩ := exists_orbitPositive_seed (Γ := Γ) (X := X)
  exact ⟨normalize f hnonneg hpos⟩

/-- The same normalization identity written as a convergent topological sum. -/
theorem normalized_tsum [LocallyCompactSpace X] (c : CutoffFunction Γ X) (x : X) :
    (∑' g : Γ, c (g⁻¹ • x) ^ 2) = 1 := by
  exact (tsum_eq_finsum (L := SummationFilter.unconditional Γ)
    (finite_orbitSquareSupport c.toCompactlySupportedContinuousMap x)).trans (c.normalized x)

/-- The coefficient formula has finite group support because only finitely
many translates of the compact support can meet the compact support itself. -/
theorem finite_mixedCoefficient_support (f h : C_c(X, ℝ)) :
    HasFiniteSupport (fun g : Γ => fun x : X => f x * h (g⁻¹ • x)) := by
  classical
  apply (finite_transporter (Γ := Γ) h.hasCompactSupport f.hasCompactSupport).subset
  intro g hg
  obtain ⟨x, hx⟩ : ∃ x : X, f x * h (g⁻¹ • x) ≠ 0 := by
    simpa only [mem_support, ne_eq, funext_iff, Pi.zero_apply, not_forall] using hg
  obtain ⟨hx₁, hx₂⟩ := mul_ne_zero_iff.mp hx
  refine ⟨x, ?_, subset_tsupport f hx₁⟩
  exact ⟨g⁻¹ • x, subset_tsupport h hx₂, smul_inv_smul g x⟩

/-- The cutoff projection formula is finitely supported in the group variable. -/
theorem finite_coefficient_support (f : C_c(X, ℝ)) :
    HasFiniteSupport (fun g : Γ => fun x : X => f x * f (g⁻¹ • x)) :=
  finite_mixedCoefficient_support f f

/-- Each real projection coefficient is compactly supported and continuous. -/
def coefficient [ContinuousConstSMul Γ X] (c : CutoffFunction Γ X) (g : Γ) : C_c(X, ℝ) where
  toFun x := c x * c (g⁻¹ • x)
  continuous_toFun := (map_continuous c).mul
    ((map_continuous c).comp (continuous_const_smul g⁻¹))
  hasCompactSupport' := (CompactlySupportedContinuousMapClass.hasCompactSupport c).mul_right

omit [TopologicalSpace Γ] [DiscreteTopology Γ] [ProperSMul Γ X] in
@[simp] theorem coefficient_apply [ContinuousConstSMul Γ X]
    (c : CutoffFunction Γ X) (g : Γ) (x : X) : coefficient c g x = c x * c (g⁻¹ • x) := rfl

end BC4lean.ProperActions.Cutoff
