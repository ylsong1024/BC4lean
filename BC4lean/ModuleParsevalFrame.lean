import BC4lean.StandardModuleParsevalFrame

/-! # Genuine countable Parseval frames over possibly nonunital coefficients

The coordinates of the constructed spectral-band analysis are the inner
products with the actual vectors `fₙ(TT*)ηₘ`. Interleaving the two countable
indices gives a genuine Parseval frame. Its analysis and adjoint are actual
bounded adjointable maps on H_B; the inner-product identity and reconstruction
are proved. No unit in B, abstract frame completion, or real square-norm
summability is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped InnerProductSpace Topology

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

local instance moduleParsevalFrameLocalInstance1 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance moduleParsevalFrameLocalInstance2 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _

/-- A Parseval frame records actual analysis into the constructed H_B and
its genuine adjoint, rather than an assumed formal coefficient completion. -/
structure ModuleParsevalFrame (ξ : ℕ → E) where
  analysis : AdjointableMap B E (StandardCountableHilbertModule B)
  coordinate : ∀ n y, standardCountableEvaluation n (analysis y) = ⟪ξ n, y⟫_(Bᵐᵒᵖ)
  adjoint_comp_self : analysis.adjoint.comp analysis = AdjointableMap.id

private theorem standardCountableEvaluation_other_row
    (n m k : ℕ) (hkn : k ≠ n) (x : StandardCountableHilbertModule B) :
    standardCountableEvaluation (Nat.pair n m)
      (standardCountableEmbedding (standardCountableRowEmbedding k) x) = 0 := by
  have he := (standardCountableMk_denseRange (B := B)).equalizer
    ((standardCountableEvaluation (B := B) (Nat.pair n m)).toCLM.continuous.comp
      (standardCountableEmbedding (B := B) (standardCountableRowEmbedding k)).toCLM.continuous)
    (continuous_const (y := (0 : Bᵐᵒᵖ))) (by
      funext v
      change standardCountableEvaluation (B := B) (Nat.pair n m)
        (standardCountableEmbedding (B := B) (standardCountableRowEmbedding k)
          (standardCountableMk (B := B) v)) = 0
      rw [standardCountableEmbedding_mk, standardCountableEvaluation_mk,
        standardCountableEmbeddingLinear_apply]
      exact Finsupp.embDomain_of_notMem_range _ _ _
        (standardCountableRowEmbedding_disjoint hkn.symm m))
  exact congrFun he x

/-- Flattening recovers the actual two-index coordinate in the completed sum. -/
theorem standardCountableEvaluation_pair_flatten
    (n m : ℕ) (x : CountableHilbertModuleSum B (StandardCountableHilbertModule B)) :
    standardCountableEvaluation (Nat.pair n m) (standardCountableFlattenCLM x) =
      standardCountableEvaluation m (countableModuleEvaluation (B := B) n x) := by
  classical
  have he := (countableModuleMk_denseRange (B := B) (E := StandardCountableHilbertModule B)).equalizer
    ((standardCountableEvaluation (B := B) (Nat.pair n m)).toCLM.continuous.comp
      (standardCountableFlattenCLM (B := B)).continuous)
    ((standardCountableEvaluation (B := B) m).toCLM.continuous.comp
      (countableModuleEvaluation (B := B) (E := StandardCountableHilbertModule B) n).toCLM.continuous) (by
      funext u
      change standardCountableEvaluation (B := B) (Nat.pair n m)
          (standardCountableFlattenCLM (B := B) (countableModuleMk (B := B) u)) =
        standardCountableEvaluation (B := B) m
          (countableModuleEvaluation (B := B) n (countableModuleMk (B := B) u))
      rw [standardCountableFlattenCLM_mk, countableModuleEvaluation_mk,
        standardCountableFlattenLinear_apply, Finsupp.sum]
      rw [map_sum]
      rw [Finset.sum_eq_single n]
      · exact standardCountableEvaluation_embedding (standardCountableRowEmbedding n) (u n) m
      · intro k _ hkn
        exact standardCountableEvaluation_other_row n m k hkn (u k)
      · intro hn
        rw [Finsupp.notMem_support_iff.mp hn, map_zero, map_zero])
  exact congrFun he x

/-- The explicit single-index family of actual spectral-band frame vectors. -/
def moduleSpectralParsevalVector (η : ℕ → E) (k : ℕ) : E :=
  standardFrameBandVector (B := B) η (Nat.unpair k).1 (Nat.unpair k).2

/-- The actual flattened spectral Parseval analysis, with its genuine adjoint. -/
def moduleSpectralParsevalAnalysis (η : ℕ → E)
    (hT : DenseRange (standardModuleSynthesis (B := B) η)) :
    AdjointableMap B E (StandardCountableHilbertModule B) :=
  (standardCountableInfiniteSumEquiv (B := B)).toAdjointable.comp
    (standardFrameParsevalSynthesis (standardModuleSynthesis η) hT).adjoint

/-- The constructed analysis coordinates are inner products with actual module vectors. -/
theorem moduleSpectralParsevalAnalysis_coordinate (η : ℕ → E)
    (hη : Summable (fun m => ‖η m‖))
    (hT : DenseRange (standardModuleSynthesis (B := B) η)) (k : ℕ) (y : E) :
    standardCountableEvaluation k (moduleSpectralParsevalAnalysis η hT y) =
      ⟪moduleSpectralParsevalVector (B := B) η k, y⟫_(Bᵐᵒᵖ) := by
  let n := (Nat.unpair k).1
  let m := (Nat.unpair k).2
  have hk : Nat.pair n m = k := Nat.pair_unpair k
  rw [← hk]
  simp only [moduleSpectralParsevalVector, Nat.unpair_pair]
  let T := standardModuleSynthesis (B := B) η
  let K := standardFrameOperatorBand (T.comp T.adjoint) n
  have hK : K.adjoint = K :=
    (cfc_nonneg (fun t _ => standardFrameBand_nonneg n t)).isSelfAdjoint.star_eq
  change standardCountableEvaluation (Nat.pair n m)
    (standardCountableFlattenCLM (standardFrameParsevalAnalysisSum T y)) = _
  rw [standardCountableEvaluation_pair_flatten, standardFrameParsevalAnalysisSum,
    countableModuleEvaluation_sequenceSum _
    (standardFrameBandAnalysis_partial_inner_tendsto T hT y y)]
  change standardCountableEvaluation m (T.adjoint (K y)) = _
  rw [standardModuleSynthesis_evaluation_adjoint η hη]
  change ⟪η m, K y⟫_(Bᵐᵒᵖ) = ⟪K (η m), y⟫_(Bᵐᵒᵖ)
  rw [K.adjoint_identity]
  change ⟪η m, K y⟫_(Bᵐᵒᵖ) = ⟪η m, K.adjoint y⟫_(Bᵐᵒᵖ)
  rw [hK]

/-- The explicit spectral vector family is a genuine Parseval frame. -/
def moduleSpectralParsevalFrame (η : ℕ → E)
    (hη : Summable (fun m => ‖η m‖))
    (hT : DenseRange (standardModuleSynthesis (B := B) η)) :
    ModuleParsevalFrame (B := B) (moduleSpectralParsevalVector (B := B) η) where
  analysis := moduleSpectralParsevalAnalysis η hT
  coordinate := moduleSpectralParsevalAnalysis_coordinate η hη hT
  adjoint_comp_self := by
    let T := standardModuleSynthesis (B := B) η
    let U := standardCountableInfiniteSumEquiv (B := B)
    let S := standardFrameParsevalSynthesis T hT
    rw [moduleSpectralParsevalAnalysis, AdjointableMap.adjoint_comp]
    ext y
    change S (U.toAdjointable.adjoint (U.toAdjointable (S.adjoint y))) = y
    rw [U.toAdjointable_adjoint, U.toAdjointable_apply, U.symm.toAdjointable_apply,
      U.symm_apply_apply]
    exact congrArg (fun R : AdjointableMap B E E => R y)
      (standardFrameParsevalSynthesis_comp_adjoint T hT)

/-- Every actual countably generated complete module admits a genuine
countable Parseval frame, including when its coefficient algebra has no unit. -/
theorem exists_moduleParsevalFrame (hE : IsCountablyGeneratedModule B E) :
    ∃ ξ : ℕ → E, Nonempty (ModuleParsevalFrame (B := B) ξ) := by
  obtain ⟨η, hη⟩ := hE
  let ζ := standardFrameRescale η
  exact ⟨moduleSpectralParsevalVector (B := B) ζ,
    ⟨moduleSpectralParsevalFrame ζ (standardFrameRescale_norm_summable η)
      (standardFrameSynthesis_denseRange η hη)⟩⟩

namespace ModuleParsevalFrame

variable {ξ : ℕ → E} (P : ModuleParsevalFrame (B := B) ξ)

omit [CompleteSpace E] in
/-- The constructed frame analysis preserves the actual coefficient inner product. -/
theorem inner_analysis (y z : E) :
    ⟪P.analysis y, P.analysis z⟫_(Bᵐᵒᵖ) = ⟪y, z⟫_(Bᵐᵒᵖ) := by
  rw [P.analysis.adjoint_identity]
  change ⟪y, P.analysis.adjoint (P.analysis z)⟫_(Bᵐᵒᵖ) = ⟪y, z⟫_(Bᵐᵒᵖ)
  rw [← AdjointableMap.comp_apply, P.adjoint_comp_self]; rfl

omit [CompleteSpace E] in
/-- The finite frame coefficients converge in the actual coefficient norm. -/
theorem coefficient_partial_tendsto (P : ModuleParsevalFrame (B := B) ξ) (y : E) :
    Tendsto (fun N => ∑ n ∈ Finset.range N,
      ⟪⟪ξ n, y⟫_(Bᵐᵒᵖ), ⟪ξ n, y⟫_(Bᵐᵒᵖ)⟫_(Bᵐᵒᵖ)) atTop (𝓝 ⟪y, y⟫_(Bᵐᵒᵖ)) := by
  have ht := standardCountableCutoff_tendsto (P.analysis y)
  have hi := (CStarModule.continuous_inner (A := Bᵐᵒᵖ)
    (E := StandardCountableHilbertModule B)).tendsto (P.analysis y, P.analysis y) |>.comp
    (ht.prodMk_nhds ht)
  change Tendsto (fun N =>
    ⟪standardCountableCutoff N (P.analysis y), standardCountableCutoff N (P.analysis y)⟫_(Bᵐᵒᵖ))
    atTop (𝓝 ⟪P.analysis y, P.analysis y⟫_(Bᵐᵒᵖ)) at hi
  simpa only [standardCountableCutoff_inner_self, P.coordinate, P.inner_analysis] using hi

omit [CompleteSpace E] in
/-- A coefficient coordinate synthesizes exactly its frame-vector multiple. -/
theorem adjoint_inclusion (n : ℕ) (b : Bᵐᵒᵖ) :
    P.analysis.adjoint (standardCountableInclusion n b) = b • ξ n := by
  apply module_inner_ext_left (B := B)
  intro y
  rw [P.analysis.adjoint.adjoint_identity]
  change ⟪standardCountableInclusion (B := B) n b, P.analysis y⟫_(Bᵐᵒᵖ) =
    ⟪b • ξ n, y⟫_(Bᵐᵒᵖ)
  rw [(standardCountableInclusion (B := B) n).adjoint_identity]
  change ⟪b, standardCountableEvaluation (B := B) n (P.analysis y)⟫_(Bᵐᵒᵖ) =
    ⟪b • ξ n, y⟫_(Bᵐᵒᵖ)
  rw [P.coordinate]
  rw [CStarModule.inner_op_smul_left]
  rfl

omit [CompleteSpace E] in
/-- The actual finite frame reconstruction converges to every module vector. -/
theorem reconstruction_tendsto (P : ModuleParsevalFrame (B := B) ξ) (y : E) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, ⟪ξ n, y⟫_(Bᵐᵒᵖ) • ξ n)
      atTop (𝓝 y) := by
  have ht := (P.analysis.adjoint.toCLM).continuous.tendsto (P.analysis y) |>.comp
    (standardCountableCutoff_tendsto (P.analysis y))
  change Tendsto (fun N => P.analysis.adjoint (standardCountableCutoff N (P.analysis y)))
    atTop (𝓝 (P.analysis.adjoint (P.analysis y))) at ht
  have hid : P.analysis.adjoint (P.analysis y) = y :=
    congrArg (fun R : AdjointableMap B E E => R y) P.adjoint_comp_self
  simpa only [standardCountableCutoff_apply, map_sum, P.coordinate, P.adjoint_inclusion, hid] using ht

end ModuleParsevalFrame
end BC4lean.KKTheory
