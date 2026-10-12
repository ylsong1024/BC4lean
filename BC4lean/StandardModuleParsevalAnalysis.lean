import BC4lean.StandardModuleFrameResolution
import BC4lean.CountableModuleSequence

/-! # Constructed Parseval analysis from dense adjointable synthesis

For a dense-range adjointable map `T : F → E`, the actual coordinate analyses
are `T* fₙ(TT*) : E → F`. Their coefficient-square partial sums telescope to
`⟪y, eₙ(TT*)y⟫`, which converge to `⟪y,y⟫`. The already constructed countable
module sum realizes the coordinate sequence in its true coefficient norm.
This produces an actual complex-linear isometry preserving the complete
coefficient inner product. No summability of real coordinate norm squares,
range complement or stabilization is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped InnerProductSpace Topology

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

local instance standardModuleParsevalAnalysisLocalInstance1 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance standardModuleParsevalAnalysisLocalInstance2 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _

/-- The actual adjointable n-th Parseval analysis coordinate. -/
def standardFrameBandAnalysis (T : AdjointableMap B F E) (n : ℕ) : AdjointableMap B E F :=
  T.adjoint.comp (standardFrameOperatorBand (T.comp T.adjoint) n)

/-- Every mixed coordinate square equals the corresponding spectral band form. -/
theorem standardFrameBandAnalysis_inner (T : AdjointableMap B F E) (n : ℕ) (y z : E) :
    ⟪standardFrameBandAnalysis T n y, standardFrameBandAnalysis T n z⟫_(Bᵐᵒᵖ) =
      ⟪y, (standardFrameOperatorCutoff (T.comp T.adjoint) (n + 1) -
        standardFrameOperatorCutoff (T.comp T.adjoint) n) z⟫_(Bᵐᵒᵖ) := by
  let h := T.comp T.adjoint
  let K := standardFrameOperatorBand h n
  have hh : 0 ≤ h := (rectangular_adjoint_squares_nonneg T).1
  have hK : K.adjoint = K :=
    (cfc_nonneg (fun t _ => standardFrameBand_nonneg n t)).isSelfAdjoint.star_eq
  change ⟪T.adjoint (K y), T.adjoint (K z)⟫_(Bᵐᵒᵖ) = _
  rw [T.adjoint.adjoint_identity]
  change ⟪K y, h (K z)⟫_(Bᵐᵒᵖ) = _
  rw [K.adjoint_identity]
  change ⟪y, K.adjoint (h (K z))⟫_(Bᵐᵒᵖ) = _
  rw [hK]
  change ⟪y, (K * h * K) z⟫_(Bᵐᵒᵖ) = _
  rw [standardFrameOperatorBand_square h hh n]

/-- The finite coordinate forms telescope exactly; there is no limiting assumption here. -/
theorem standardFrameBandAnalysis_partial_inner (T : AdjointableMap B F E)
    (N : ℕ) (y z : E) :
    (∑ n ∈ Finset.range N,
      ⟪standardFrameBandAnalysis T n y, standardFrameBandAnalysis T n z⟫_(Bᵐᵒᵖ)) =
      ⟪y, standardFrameOperatorCutoff (T.comp T.adjoint) N z⟫_(Bᵐᵒᵖ) := by
  induction N with
  | zero =>
    have hzero : standardFrameCutoff 0 = (0 : ℝ → ℝ) := by
      funext t
      exact standardFrameCutoff_zero t
    simp only [Finset.range_zero, Finset.sum_empty]
    change 0 = ⟪y, (cfc (standardFrameCutoff 0) (T.comp T.adjoint)) z⟫_(Bᵐᵒᵖ)
    rw [hzero, cfc_zero]
    change 0 = ⟪y, (0 : E)⟫_(Bᵐᵒᵖ)
    rw [CStarModule.inner_zero_right]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, standardFrameBandAnalysis_inner]
    simp only [AdjointableMap.coe_sub_apply, CStarModule.inner_sub_right]
    abel

/-- Actual dense synthesis supplies convergence of all mixed coefficient sums. -/
theorem standardFrameBandAnalysis_partial_inner_tendsto
    (T : AdjointableMap B F E) (hT : DenseRange T) (y z : E) :
    Tendsto (fun N => ∑ n ∈ Finset.range N,
      ⟪standardFrameBandAnalysis T n y, standardFrameBandAnalysis T n z⟫_(Bᵐᵒᵖ))
      atTop (𝓝 ⟪y, z⟫_(Bᵐᵒᵖ)) := by
  have hlim := (CStarModule.innerSL (A := Bᵐᵒᵖ) y).continuous.tendsto z |>.comp
    (standardFrameOperatorCutoff_tendsto T hT z)
  change Tendsto (fun N : ℕ =>
      ⟪y, standardFrameOperatorCutoff (T.comp T.adjoint) (N + 1) z⟫_(Bᵐᵒᵖ))
    atTop (𝓝 ⟪y, z⟫_(Bᵐᵒᵖ)) at hlim
  have hshift : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1),
      ⟪standardFrameBandAnalysis T n y, standardFrameBandAnalysis T n z⟫_(Bᵐᵒᵖ))
      atTop (𝓝 ⟪y, z⟫_(Bᵐᵒᵖ)) := by
    simpa only [standardFrameBandAnalysis_partial_inner] using hlim
  exact (tendsto_add_atTop_iff_nat 1).mp hshift

/-- The actual limit in the constructed countable module sum. -/
def standardFrameParsevalAnalysisSum (T : AdjointableMap B F E) (y : E) :
    CountableHilbertModuleSum B F :=
  countableModuleSequenceSum (fun n => standardFrameBandAnalysis T n y)

theorem standardFrameParsevalAnalysisSum_tendsto
    (T : AdjointableMap B F E) (hT : DenseRange T) (y : E) :
    Tendsto (countableModuleTruncation (B := B) (fun n => standardFrameBandAnalysis T n y))
      atTop (𝓝 (standardFrameParsevalAnalysisSum T y)) :=
  countableModuleTruncation_tendsto _ (standardFrameBandAnalysis_partial_inner_tendsto T hT y y)

/-- The analysis sum preserves the actual coefficient inner product. -/
theorem standardFrameParsevalAnalysisSum_inner
    (T : AdjointableMap B F E) (hT : DenseRange T) (y z : E) :
    ⟪standardFrameParsevalAnalysisSum T y, standardFrameParsevalAnalysisSum T z⟫_(Bᵐᵒᵖ) =
      ⟪y, z⟫_(Bᵐᵒᵖ) :=
  countableModuleSequenceSum_inner _ _
    (standardFrameBandAnalysis_partial_inner_tendsto T hT y y)
    (standardFrameBandAnalysis_partial_inner_tendsto T hT z z)
    (standardFrameBandAnalysis_partial_inner_tendsto T hT y z)

theorem standardFrameParsevalAnalysisSum_add
    (T : AdjointableMap B F E) (hT : DenseRange T) (y z : E) :
    standardFrameParsevalAnalysisSum T (y + z) =
      standardFrameParsevalAnalysisSum T y + standardFrameParsevalAnalysisSum T z := by
  apply tendsto_nhds_unique (standardFrameParsevalAnalysisSum_tendsto T hT (y + z))
  have heq : (fun n => standardFrameBandAnalysis T n (y + z)) =
      (fun n => standardFrameBandAnalysis T n y) + (fun n => standardFrameBandAnalysis T n z) := by
    funext n
    exact (standardFrameBandAnalysis T n).toCLM.map_add y z
  rw [heq]
  have htrunc : countableModuleTruncation (B := B)
      ((fun n => standardFrameBandAnalysis T n y) +
        (fun n => standardFrameBandAnalysis T n z)) =
      (fun N => countableModuleTruncation (B := B)
        (fun n => standardFrameBandAnalysis T n y) N +
        countableModuleTruncation (B := B) (fun n => standardFrameBandAnalysis T n z) N) := by
    funext N
    exact countableModuleTruncation_add _ _ N
  rw [htrunc]
  exact (standardFrameParsevalAnalysisSum_tendsto T hT y).add
    (standardFrameParsevalAnalysisSum_tendsto T hT z)

theorem standardFrameParsevalAnalysisSum_smul
    (T : AdjointableMap B F E) (hT : DenseRange T) (c : ℂ) (y : E) :
    standardFrameParsevalAnalysisSum T (c • y) = c • standardFrameParsevalAnalysisSum T y := by
  apply tendsto_nhds_unique (standardFrameParsevalAnalysisSum_tendsto T hT (c • y))
  have heq : (fun n => standardFrameBandAnalysis T n (c • y)) =
      c • (fun n => standardFrameBandAnalysis T n y) := by
    funext n
    exact (standardFrameBandAnalysis T n).toCLM.map_smul c y
  rw [heq]
  have htrunc : countableModuleTruncation (B := B)
      (c • (fun n => standardFrameBandAnalysis T n y)) =
      (fun N => c • countableModuleTruncation (B := B)
        (fun n => standardFrameBandAnalysis T n y) N) := by
    funext N
    exact countableModuleTruncation_smul c _ N
  rw [htrunc]
  exact (standardFrameParsevalAnalysisSum_tendsto T hT y).const_smul c

theorem standardFrameParsevalAnalysisSum_norm
    (T : AdjointableMap B F E) (hT : DenseRange T) (y : E) :
    ‖standardFrameParsevalAnalysisSum T y‖ = ‖y‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ),
    standardFrameParsevalAnalysisSum_inner T hT,
    ← CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ)]

/-- The actual constructed Parseval analysis isometry. Its range is not assumed complemented. -/
def standardFrameParsevalAnalysis (T : AdjointableMap B F E) (hT : DenseRange T) :
    E →ₗᵢ[ℂ] CountableHilbertModuleSum B F where
  toLinearMap :=
    { toFun := standardFrameParsevalAnalysisSum T
      map_add' := standardFrameParsevalAnalysisSum_add T hT
      map_smul' := standardFrameParsevalAnalysisSum_smul T hT }
  norm_map' := standardFrameParsevalAnalysisSum_norm T hT

@[simp] theorem standardFrameParsevalAnalysis_apply
    (T : AdjointableMap B F E) (hT : DenseRange T) (y : E) :
    standardFrameParsevalAnalysis T hT y = standardFrameParsevalAnalysisSum T y := rfl

/-- A countably generated module admits a constructed coefficient-inner-product
isometry into the actual countable sum of copies of H_B. -/
theorem exists_standardFrameParsevalAnalysis
    (hE : IsCountablyGeneratedModule B E) :
    ∃ V : E →ₗᵢ[ℂ] CountableHilbertModuleSum B (StandardCountableHilbertModule B),
      ∀ y z, ⟪V y, V z⟫_(Bᵐᵒᵖ) = ⟪y, z⟫_(Bᵐᵒᵖ) := by
  obtain ⟨T, hT⟩ := exists_standardModuleSynthesis_denseRange hE
  exact ⟨standardFrameParsevalAnalysis T hT, standardFrameParsevalAnalysisSum_inner T hT⟩

end BC4lean.KKTheory
