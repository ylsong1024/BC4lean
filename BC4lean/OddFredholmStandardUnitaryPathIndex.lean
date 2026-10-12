import BC4lean.OddFredholmCutoffIndependence
import Mathlib.Order.Filter.Finite

/-! # Genuine norm-homotopy invariance of the standard compact unitary index

A finite open cover of the compact parameter space and the actual cutoff
contraction estimate give one concrete polar criterion for the entire path.
Actual finite compact coefficient extraction is continuous. The existing K1
quotient and proved cutoff independence give equality of the chosen indices.
-/

noncomputable section
namespace BC4lean.KKTheory

open Filter unitInterval
open scoped Topology CStarAlgebra
open BC4lean.OperatorKTheory

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

local instance oddContinuationOddFredholmStandardUnitaryPathIndexLocalInstance01 : PartialOrder (Unitization ℂ B) := CStarAlgebra.spectralOrder _
local instance oddContinuationOddFredholmStandardUnitaryPathIndexLocalInstance02 : StarOrderedRing (Unitization ℂ B) := CStarAlgebra.spectralOrderedRing _
local instance oddContinuationOddFredholmStandardUnitaryPathIndexLocalInstance03 : PartialOrder (OddFredholmStandardOperator B) := CStarAlgebra.spectralOrder _
local instance oddContinuationOddFredholmStandardUnitaryPathIndexLocalInstance04 : StarOrderedRing (OddFredholmStandardOperator B) := CStarAlgebra.spectralOrderedRing _

theorem oddFredholmUnitaryCutoff_norm_sub_le
    (U V : unitary (OddFredholmStandardOperator B)) (n : ℕ) :
    ‖oddFredholmUnitaryCutoff U n - oddFredholmUnitaryCutoff V n‖ ≤
      ‖(U : OddFredholmStandardOperator B) - (V : OddFredholmStandardOperator B)‖ := by
  have he : oddFredholmUnitaryCutoff U n - oddFredholmUnitaryCutoff V n =
      standardCountableCutoff n * ((U : OddFredholmStandardOperator B) - (V : OddFredholmStandardOperator B)) * standardCountableCutoff n := by
    unfold oddFredholmUnitaryCutoff
    noncomm_ring
  rw [he]
  calc
    _ ≤ ‖standardCountableCutoff (B := B) n * ((U : OddFredholmStandardOperator B) - (V : OddFredholmStandardOperator B))‖ *
        ‖standardCountableCutoff (B := B) n‖ := norm_mul_le _ _
    _ ≤ ‖standardCountableCutoff (B := B) n‖ * ‖(U : OddFredholmStandardOperator B) - (V : OddFredholmStandardOperator B)‖ *
        ‖standardCountableCutoff (B := B) n‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ 1 * ‖(U : OddFredholmStandardOperator B) - (V : OddFredholmStandardOperator B)‖ * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right (norm_standardCountableCutoff_le n) (norm_nonneg _))
        (norm_standardCountableCutoff_le n) (norm_nonneg _) (by positivity)
    _ = _ := by simp only [one_mul, mul_one]

theorem oddFredholmUnitaryCutoff_eventually_near_uniform
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (U : X → unitary (OddFredholmStandardOperator B)) (hContinuous : Continuous U)
    (hCompact : ∀ x, IsModuleCompact ((U x : OddFredholmStandardOperator B) - 1)) :
    ∀ᶠ n in atTop, ∀ x, ‖oddFredholmUnitaryCutoff (U x) n - (U x : _)‖ < 1 := by
  classical
  let O : X → Set X := fun a => {x | ‖(U x : OddFredholmStandardOperator B) - (U a : OddFredholmStandardOperator B)‖ < 1 / 8}
  have hopen (a : X) : IsOpen (O a) :=
    isOpen_lt (((continuous_subtype_val.comp hContinuous).sub continuous_const).norm) continuous_const
  have hcover : (Set.univ : Set X) ⊆ ⋃ a, O a := by
    intro x _
    apply Set.mem_iUnion.mpr
    refine ⟨x, ?_⟩
    change ‖(U x : OddFredholmStandardOperator B) - (U x : OddFredholmStandardOperator B)‖ < 1 / 8
    simp only [sub_self, norm_zero]
    norm_num
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover O hopen hcover
  have he : ∀ᶠ n in atTop, ∀ a ∈ s,
      ‖oddFredholmUnitaryCutoff (U a) n - (U a : _)‖ < 1 / 2 := by
    apply (Filter.eventually_all_finset s).mpr
    intro a _
    have h := ((oddFredholmUnitaryCutoff_tendsto (U a) (hCompact a)).sub_const (U a : _)).norm
    have h' : Tendsto (fun n => ‖oddFredholmUnitaryCutoff (U a) n - (U a : _)‖)
        atTop (𝓝 (0 : ℝ)) := by simpa only [sub_self, norm_zero] using h
    exact h'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [he] with n hn
  intro x
  obtain ⟨a, ha, hxa⟩ := (by simpa only [Set.mem_iUnion] using hs (Set.mem_univ x) :
    ∃ a, ∃ ha : a ∈ s, x ∈ O a)
  have hball : ‖(U x : OddFredholmStandardOperator B) - (U a : OddFredholmStandardOperator B)‖ < 1 / 8 := hxa
  have hcenter := hn a ha
  calc
    _ ≤ ‖oddFredholmUnitaryCutoff (U x) n - oddFredholmUnitaryCutoff (U a) n‖ +
        ‖oddFredholmUnitaryCutoff (U a) n - (U x : _)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖(U x : OddFredholmStandardOperator B) - (U a : OddFredholmStandardOperator B)‖ +
        (‖oddFredholmUnitaryCutoff (U a) n - (U a : _)‖ +
          ‖(U a : OddFredholmStandardOperator B) - (U x : OddFredholmStandardOperator B)‖) :=
      add_le_add (oddFredholmUnitaryCutoff_norm_sub_le (U x) (U a) n) (norm_sub_le_norm_sub_add_norm_sub _ _ _)
    _ < 1 := by
      rw [norm_sub_rev (U a : OddFredholmStandardOperator B) (U x : OddFredholmStandardOperator B)]
      linarith

theorem continuous_oddFredholmStandardCutoffPolarUnitary
    {X : Type*} [TopologicalSpace X] (U : X → unitary (OddFredholmStandardOperator B))
    (hContinuous : Continuous U) (n : ℕ)
    (hn : ∀ x, ‖oddFredholmUnitaryCutoff (U x) n - (U x : _)‖ < 1) :
    Continuous (fun x => oddFredholmStandardCutoffPolarUnitary (U x) n (hn x)) :=
  (continuousOn_oddFredholmPolarElement.comp_continuous
    (by unfold oddFredholmUnitaryCutoff; fun_prop)
    (fun x => oddFredholmIsUnit_of_norm_sub_unitary_lt_one_all _ (U x) (hn x))).subtype_mk _

theorem continuous_oddFredholmStandardFiniteIndexUnitary
    {X : Type*} [TopologicalSpace X] (U : X → unitary (OddFredholmStandardOperator B))
    (hContinuous : Continuous U)
    (hCompact : ∀ x, IsModuleCompact ((U x : OddFredholmStandardOperator B) - 1)) (n : ℕ)
    (hn : ∀ x, ‖oddFredholmUnitaryCutoff (U x) n - (U x : _)‖ < 1) :
    Continuous (fun x => oddFredholmStandardFiniteIndexUnitary (U x) (hCompact x) n (hn x)) := by
  change Continuous (fun x => oddFredholmSupportedFiniteUnitary
    (oddFredholmStandardCutoffPolarUnitary (U x) n (hn x))
    (oddFredholmStandardCutoffPolarUnitary_sub_one_isModuleCompact (U x) (hCompact x) n (hn x)) n
    (oddFredholmStandardCutoffPolarUnitary_right_tail (U x) n (hn x)))
  exact continuous_oddFredholmSupportedFiniteUnitary _ _ _ _
    (continuous_oddFredholmStandardCutoffPolarUnitary U hContinuous n hn)

/-- Every actual norm-continuous path of compact standard-module unitaries
has equal chosen index endpoints in the project's actual OperatorK1(B). -/
theorem oddFredholmStandardUnitaryIndex_path
    {U V : unitary (OddFredholmStandardOperator B)} (p : Path U V)
    (hCompact : ∀ t : I, IsModuleCompact ((p t : OddFredholmStandardOperator B) - 1)) :
    oddFredholmStandardUnitaryIndex U (by simpa only [Path.source] using hCompact 0) =
      oddFredholmStandardUnitaryIndex V (by simpa only [Path.target] using hCompact 1) := by
  obtain ⟨n, hn⟩ := (oddFredholmUnitaryCutoff_eventually_near_uniform p p.continuous hCompact).exists
  let q : Path
      (oddFredholmStandardFiniteIndexUnitary (p 0) (hCompact 0) n (hn 0))
      (oddFredholmStandardFiniteIndexUnitary (p 1) (hCompact 1) n (hn 1)) :=
    { toFun t := oddFredholmStandardFiniteIndexUnitary (p t) (hCompact t) n (hn t)
      continuous_toFun := continuous_oddFredholmStandardFiniteIndexUnitary p p.continuous hCompact n hn
      source' := rfl
      target' := rfl }
  have he : oddFredholmScalarIdentityUnitaryIndex
      (oddFredholmStandardFiniteIndexUnitary (p 0) (hCompact 0) n (hn 0))
      (oddFredholmStandardFiniteIndexUnitary_scalar (p 0) (hCompact 0) n (hn 0)) =
      oddFredholmScalarIdentityUnitaryIndex
        (oddFredholmStandardFiniteIndexUnitary (p 1) (hCompact 1) n (hn 1))
        (oddFredholmStandardFiniteIndexUnitary_scalar (p 1) (hCompact 1) n (hn 1)) := by
    apply Subtype.ext
    exact K1.of_homotopic ⟨q⟩
  have h0 := oddFredholmStandardUnitaryIndex_eq_cutoff (p 0) (hCompact 0) n (hn 0)
  have h1 := oddFredholmStandardUnitaryIndex_eq_cutoff (p 1) (hCompact 1) n (hn 1)
  simpa only [Path.source, Path.target] using h0.trans (he.trans h1.symm)

/-- Actual selfadjoint Fredholm norm paths on H_B have equal genuine
exponential index values, with compactness verified along the whole path. -/
theorem oddFredholmStandardIndex_path
    {F G : selfAdjoint (OddFredholmStandardOperator B)} (p : Path F G)
    (hCompact : ∀ t : I, IsModuleCompact ((p t : OddFredholmStandardOperator B) ^ 2 - 1)) :
    oddFredholmStandardIndex F (by simpa only [Path.source] using hCompact 0) =
      oddFredholmStandardIndex G (by simpa only [Path.target] using hCompact 1) := by
  let q : Path (oddFredholmExponential F) (oddFredholmExponential G) :=
    { toFun t := oddFredholmExponential (p t)
      continuous_toFun := continuous_oddFredholmExponential.comp p.continuous
      source' := by rw [Path.source]
      target' := by rw [Path.target] }
  have h := oddFredholmStandardUnitaryIndex_path q
    (fun t => oddFredholmExponential_sub_one_isModuleCompact (p t) (hCompact t))
  exact h

private theorem oddFredholmScalarIdentityUnitaryIndex_finZero
    {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (v : unitary (CStarMatrix (Fin 0) (Fin 0) (Unitization ℂ B)))
    (hv : unitizationScalarMatrix
      (v : CStarMatrix (Fin 0) (Fin 0) (Unitization ℂ B)) = 1) :
    oddFredholmScalarIdentityUnitaryIndex v hv = 0 := by
  apply Subtype.ext
  change K1.of (FiniteUnitary.ofUnitary v) = 0
  have hu : v = (1 : unitary (CStarMatrix (Fin 0) (Fin 0) (Unitization ℂ B))) := by
    apply Subtype.ext
    ext i j <;> exact Fin.elim0 i
  rw [hu]
  exact K1.of_identity (Fin 0)

set_option maxHeartbeats 2400000 in
theorem oddFredholmStandardUnitaryIndex_one
    (hCompact : IsModuleCompact ((1 : OddFredholmStandardOperator B) - 1)) :
    oddFredholmStandardUnitaryIndex (1 : unitary (OddFredholmStandardOperator B)) hCompact = 0 := by
  have hn : ‖oddFredholmUnitaryCutoff (1 : unitary (OddFredholmStandardOperator B)) 0 - 1‖ < 1 := by
    change ‖(1 : OddFredholmStandardOperator B) +
      standardCountableCutoff (B := B) 0 * ((1 : OddFredholmStandardOperator B) - 1) *
        standardCountableCutoff (B := B) 0 - 1‖ < 1
    simp only [sub_self, mul_zero, zero_mul, add_zero, norm_zero]
    norm_num
  refine (oddFredholmStandardUnitaryIndex_eq_cutoff (B := B)
    (1 : unitary (OddFredholmStandardOperator B)) hCompact 0 hn).trans ?_
  exact oddFredholmScalarIdentityUnitaryIndex_finZero (B := B)
    (oddFredholmStandardFiniteIndexUnitary
      (1 : unitary (OddFredholmStandardOperator B)) hCompact 0 hn)
    (oddFredholmStandardFiniteIndexUnitary_scalar
      (1 : unitary (OddFredholmStandardOperator B)) hCompact 0 hn)

/-- Exact selfadjoint involutions have zero actual exponential index. -/
theorem oddFredholmStandardIndex_involution
    (F : selfAdjoint (OddFredholmStandardOperator B))
    (hSquare : (F : OddFredholmStandardOperator B) ^ 2 = 1) :
    oddFredholmStandardIndex F (by rw [hSquare, sub_self]; exact IsModuleCompact.zero) = 0 := by
  have he : oddFredholmExponential F = 1 := by
    apply Subtype.ext
    apply sub_eq_zero.mp
    change (oddFredholmExponential F : OddFredholmStandardOperator B) -
      (1 : OddFredholmStandardOperator B) = 0
    rw [oddFredholmExponential_sub_one_factor, hSquare, sub_self, zero_mul]
  let P : unitary (OddFredholmStandardOperator B) → Prop := fun U =>
    ∀ hCompact : IsModuleCompact ((U : OddFredholmStandardOperator B) - 1),
      oddFredholmStandardUnitaryIndex U hCompact = 0
  have hOne : P 1 := by
    intro hCompact
    exact oddFredholmStandardUnitaryIndex_one hCompact
  have hExp : P (oddFredholmExponential F) := Eq.mpr (congrArg P he) hOne
  unfold oddFredholmStandardIndex
  exact hExp _

end BC4lean.KKTheory
