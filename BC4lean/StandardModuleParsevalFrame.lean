import BC4lean.StandardModuleParsevalAnalysis
import BC4lean.StandardCountableFlatten
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! # The genuine adjoint and coisometry of Parseval analysis

The finite row of the actual band operators is bounded by one. Its bound is
proved from its genuine finite-versus-infinite coefficient adjoint identity
and the already constructed analysis isometry. Descending to the actual
finite-vector quotient and extending to its completion constructs the row
adjoint. Thus the Parseval analysis is genuinely adjointable and its adjoint
is a coisometry. Applying this to the constructed standard-module synthesis
and the proved countable flattening gives an actual complemented isometric
embedding of every countably generated Hilbert module into H_B.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

/-- The actual finite row of the adjoint band operators. -/
def standardFrameParsevalFiniteRow (T : AdjointableMap B F E) :
    CountableModuleVectors F →ₗ[ℂ] E :=
  Finsupp.lsum ℂ (fun n => (standardFrameBandAnalysis T n).adjoint.toCLM.toLinearMap)

/-- The finite row and actual analysis column satisfy the coefficient adjoint identity. -/
theorem standardFrameParsevalFiniteRow_inner
    (T : AdjointableMap B F E) (hT : DenseRange T)
    (u : CountableModuleVectors F) (y : E) :
    ⟪standardFrameParsevalFiniteRow T u, y⟫_(Bᵐᵒᵖ) =
      ⟪countableModuleMk (B := B) u, standardFrameParsevalAnalysisSum T y⟫_(Bᵐᵒᵖ) := by
  classical
  rw [standardFrameParsevalFiniteRow, Finsupp.lsum_apply, Finsupp.sum,
    CStarModule.inner_sum_left, standardFrameParsevalAnalysisSum,
    countableModuleMk_inner_sequenceSum _ _
      (standardFrameBandAnalysis_partial_inner_tendsto T hT y y)]
  exact Finset.sum_congr rfl (fun n _ => (standardFrameBandAnalysis T n).adjoint.adjoint_identity _ _)

/-- The actual finite row is contractive in the coefficient-form module norm. -/
theorem standardFrameParsevalFiniteRow_norm_le
    (T : AdjointableMap B F E) (hT : DenseRange T) (u : CountableModuleVectors F) :
    ‖standardFrameParsevalFiniteRow T u‖ ≤ ‖countableModuleMk (B := B) u‖ := by
  let y := standardFrameParsevalFiniteRow T u
  have hsq : ‖y‖ ^ 2 ≤ ‖countableModuleMk (B := B) u‖ * ‖y‖ := by
    rw [CStarModule.norm_sq_eq (Bᵐᵒᵖ), standardFrameParsevalFiniteRow_inner T hT]
    have hi := CStarModule.norm_inner_le (A := Bᵐᵒᵖ) (CountableHilbertModuleSum B F)
      (x := countableModuleMk (B := B) u) (y := standardFrameParsevalAnalysisSum T y)
    simpa only [standardFrameParsevalAnalysisSum_norm T hT] using hi
  by_cases hy : ‖y‖ = 0
  · change ‖y‖ ≤ _
    rw [hy]
    exact norm_nonneg (countableModuleMk (B := B) u)
  · exact le_of_mul_le_mul_right (by simpa only [pow_two] using hsq)
      (lt_of_le_of_ne (norm_nonneg y) (Ne.symm hy))

/-- Descend the actual row through the proved zero finite-vector radical. -/
def standardFrameParsevalRowQuotientLinear (T : AdjointableMap B F E) :
    CountableHilbertModulePreSum B F →ₗ[ℂ] E :=
  (PositiveModuleForm.nullRadical (B := B) (E := CountableModuleVectors F)).liftQ
    (standardFrameParsevalFiniteRow T) (fun u hu => by
      rw [countableModuleFinite_nullRadical_eq_bot, Submodule.mem_bot] at hu
      simp [hu])

omit [CompleteSpace F] in
@[simp] theorem standardFrameParsevalRowQuotientLinear_mk
    (T : AdjointableMap B F E) (u : CountableModuleVectors F) :
    standardFrameParsevalRowQuotientLinear T (positiveModuleQuotientMk (B := B) u) =
      standardFrameParsevalFiniteRow T u := rfl

def standardFrameParsevalRowQuotientCLM (T : AdjointableMap B F E) (hT : DenseRange T) :
    CountableHilbertModulePreSum B F →L[ℂ] E :=
  (standardFrameParsevalRowQuotientLinear T).mkContinuous 1 (fun q => by
    obtain ⟨u, rfl⟩ := positiveModuleQuotientMk_surjective q
    have h := standardFrameParsevalFiniteRow_norm_le T hT u
    simpa only [standardFrameParsevalRowQuotientLinear_mk, countableModuleMk_apply,
      UniformSpace.Completion.norm_coe, one_mul] using h)

/-- The actual bounded row on the complete countable module sum. -/
def standardFrameParsevalRowCLM (T : AdjointableMap B F E) (hT : DenseRange T) :
    CountableHilbertModuleSum B F →L[ℂ] E :=
  (standardFrameParsevalRowQuotientCLM T hT).fromCompletion

@[simp] theorem standardFrameParsevalRowCLM_mk
    (T : AdjointableMap B F E) (hT : DenseRange T) (u : CountableModuleVectors F) :
    standardFrameParsevalRowCLM T hT (countableModuleMk (B := B) u) =
      standardFrameParsevalFiniteRow T u := by
  rw [standardFrameParsevalRowCLM, countableModuleMk_apply,
    ContinuousLinearMap.fromCompletion_apply_coe]
  rfl

/-- The genuine synthesis coisometry, with the proved analysis column as adjoint. -/
def standardFrameParsevalSynthesis (T : AdjointableMap B F E) (hT : DenseRange T) :
    AdjointableMap B (CountableHilbertModuleSum B F) E where
  toCLM := standardFrameParsevalRowCLM T hT
  adjointCLM := (standardFrameParsevalAnalysis T hT).toContinuousLinearMap
  adjoint_identity u y := by
    change ⟪standardFrameParsevalRowCLM T hT u, y⟫_(Bᵐᵒᵖ) =
      ⟪u, standardFrameParsevalAnalysisSum T y⟫_(Bᵐᵒᵖ)
    have he := (countableModuleMk_denseRange (B := B) (E := F)).equalizer
      ((CStarModule.continuous_inner (A := Bᵐᵒᵖ) (E := E)).comp
        ((standardFrameParsevalRowCLM T hT).continuous.prodMk (continuous_const (y := y))))
      ((CStarModule.continuous_inner (A := Bᵐᵒᵖ) (E := CountableHilbertModuleSum B F)).comp
        (continuous_id.prodMk
          (continuous_const (y := standardFrameParsevalAnalysisSum T y)))) (by
            funext v
            change ⟪standardFrameParsevalRowCLM T hT (countableModuleMk (B := B) v), y⟫_(Bᵐᵒᵖ) =
              ⟪countableModuleMk (B := B) v, standardFrameParsevalAnalysisSum T y⟫_(Bᵐᵒᵖ)
            rw [standardFrameParsevalRowCLM_mk]
            exact standardFrameParsevalFiniteRow_inner T hT v y)
    exact congrFun he u

@[simp] theorem standardFrameParsevalSynthesis_adjoint_apply
    (T : AdjointableMap B F E) (hT : DenseRange T) (y : E) :
    (standardFrameParsevalSynthesis T hT).adjoint y = standardFrameParsevalAnalysisSum T y := rfl

@[simp] theorem standardFrameParsevalSynthesis_mk
    (T : AdjointableMap B F E) (hT : DenseRange T) (u : CountableModuleVectors F) :
    standardFrameParsevalSynthesis T hT (countableModuleMk (B := B) u) =
      standardFrameParsevalFiniteRow T u := standardFrameParsevalRowCLM_mk T hT u

/-- The constructed synthesis is an actual coisometry; no range complement is assumed. -/
theorem standardFrameParsevalSynthesis_comp_adjoint
    (T : AdjointableMap B F E) (hT : DenseRange T) :
    (standardFrameParsevalSynthesis T hT).comp (standardFrameParsevalSynthesis T hT).adjoint =
      AdjointableMap.id := by
  ext y
  apply module_inner_ext_left (B := B)
  intro z
  change ⟪standardFrameParsevalSynthesis T hT
      ((standardFrameParsevalSynthesis T hT).adjoint y), z⟫_(Bᵐᵒᵖ) = ⟪y, z⟫_(Bᵐᵒᵖ)
  rw [(standardFrameParsevalSynthesis T hT).adjoint_identity]
  change ⟪standardFrameParsevalAnalysisSum T y, standardFrameParsevalAnalysisSum T z⟫_(Bᵐᵒᵖ) =
    ⟪y, z⟫_(Bᵐᵒᵖ)
  exact standardFrameParsevalAnalysisSum_inner T hT y z

/-- Every countably generated complete module has an actual adjointable
isometric embedding into H_B, constructed from its genuine generating family. -/
theorem exists_adjointable_standardFrameParsevalEmbedding
    (hE : IsCountablyGeneratedModule B E) :
    ∃ V : AdjointableMap B E (StandardCountableHilbertModule B),
      V.adjoint.comp V = AdjointableMap.id ∧
      ∀ y z, ⟪V y, V z⟫_(Bᵐᵒᵖ) = ⟪y, z⟫_(Bᵐᵒᵖ) := by
  obtain ⟨T, hT⟩ := exists_standardModuleSynthesis_denseRange hE
  let U := standardCountableInfiniteSumEquiv (B := B)
  let S := standardFrameParsevalSynthesis T hT
  let V := U.toAdjointable.comp S.adjoint
  refine ⟨V, ?_, ?_⟩
  · rw [AdjointableMap.adjoint_comp]
    ext y
    change S (U.toAdjointable.adjoint (U.toAdjointable (S.adjoint y))) = y
    rw [U.toAdjointable_adjoint, U.toAdjointable_apply, U.symm.toAdjointable_apply,
      U.symm_apply_apply]
    exact congrArg (fun R : AdjointableMap B E E => R y)
      (standardFrameParsevalSynthesis_comp_adjoint T hT)
  · intro y z
    change ⟪U (S.adjoint y), U (S.adjoint z)⟫_(Bᵐᵒᵖ) = _
    rw [U.inner_map]
    exact standardFrameParsevalAnalysisSum_inner T hT y z

end BC4lean.KKTheory
