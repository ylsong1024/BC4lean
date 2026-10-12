import BC4lean.OddFredholmSumOperatorHom
import BC4lean.OddScalarKasparovIndexIso
import BC4lean.OddKTheoryStandardPrefixEquiv

/-! # The actual raw Fredholm index of a unital scalar cycle

For the actual scalar representation the support range is genuinely the
whole module. Compression intertwines through its coefficient-form unitary.
The proved normalization path is selfadjoint when the original operator is,
so its actual stabilized exponential index agrees with the raw one.
-/

noncomputable section
namespace BC4lean.KKTheory
open unitInterval
open scoped CStarAlgebra

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E] [TopologicalSpace.SeparableSpace B]

local instance oddContinuationOddFredholmScalarCycleRawIndexLocalInstance01 : CompleteSpace (HilbertModuleSum B E (StandardCountableHilbertModule B)) :=
  hilbertModuleSum_complete

def oddFredholmStabilizedSelfAdjointPath (hE : IsCountablyGeneratedModule B E)
    {F G : selfAdjoint (AdjointableMap B E E)} (p : Path F G) :
    Path (oddFredholmStandardStabilizedOperator hE F) (oddFredholmStandardStabilizedOperator hE G) where
  toFun t := oddFredholmStandardStabilizedOperator hE (p t)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (standardModuleStabilization hE).transportStarAlgEquiv.isometry.continuous.comp
      ((map_continuous oddFredholmSumOperatorHom).comp
        ((continuous_subtype_val.comp p.continuous).prodMk continuous_const))
  source' := congrArg (oddFredholmStandardStabilizedOperator hE) p.source
  target' := congrArg (oddFredholmStandardStabilizedOperator hE) p.target

theorem oddFredholmStabilizedIndex_selfAdjointPath (hE : IsCountablyGeneratedModule B E)
    {F G : selfAdjoint (AdjointableMap B E E)} (p : Path F G)
    (hCompact : ∀ t, IsModuleCompact ((p t : AdjointableMap B E E) * p t - 1)) :
    oddFredholmStabilizedIndex hE F (by simpa only [p.source] using hCompact 0) =
      oddFredholmStabilizedIndex hE G (by simpa only [p.target] using hCompact 1) := by
  apply oddFredholmStandardIndex_path (oddFredholmStabilizedSelfAdjointPath hE p)
  intro t
  simpa only [oddFredholmStabilizedSelfAdjointPath, pow_two] using
    oddFredholmStandardStabilizedOperator_square_compact hE (p t) (hCompact t)

local notation "α₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
local notation "β₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B)

def oddFredholmUnitalScalarSupportEquiv (c : OddKasparovCycle α₁ β₁ E)
    (hc : c.scalarSupportProjection = 1) :
    HilbertModuleEquiv B (ProjectionModule c.scalarSupportProjection) E where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun x := (x : E)
          invFun x := ⟨x, by rw [hc]; rfl⟩
          left_inv _ := rfl
          right_inv _ := rfl
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      norm_map' _ := rfl }
  inner_map _ _ := rfl

theorem oddFredholmUnitalScalarSupportEquiv_compression (c : OddKasparovCycle α₁ β₁ E)
    (hc : c.scalarSupportProjection = 1) :
    (oddFredholmUnitalScalarSupportEquiv c hc).transport c.scalarSupportCompression = c.operator := by
  ext x
  change (c.scalarSupportCompression ((oddFredholmUnitalScalarSupportEquiv c hc).symm x) : E) = _
  rw [c.scalarSupportCompression_coe]
  change c.scalarSupportBlockOperator x = c.operator x
  simp only [OddKasparovCycle.scalarSupportBlockOperator, hc, one_mul, mul_one, sub_self,
    zero_mul, mul_zero, add_zero]

theorem oddFredholmUnitalScalarSupportEquiv_normalized (c : OddKasparovCycle α₁ β₁ E)
    (hc : c.scalarSupportProjection = 1) :
    (oddFredholmUnitalScalarSupportEquiv c hc).transport c.scalarSupportNormalizedCycle.operator =
      c.normalized.operator := by
  change (oddFredholmUnitalScalarSupportEquiv c hc).transportStarAlgEquiv.toStarAlgHom
    (oddFredholmNormalizedElement c.scalarSupportCompression) = oddFredholmNormalizedElement c.operator
  rw [oddFredholmNormalizedElement_map, oddFredholmUnitalScalarSupportEquiv_compression]

def oddFredholmSelfAdjointNormalizationPath (c : OddKasparovCycle α₁ β₁ E)
    (hc : IsSelfAdjoint c.operator) :
    Path (⟨c.operator, hc⟩ : selfAdjoint (AdjointableMap B E E))
      ⟨c.normalized.operator, c.normalized_selfadjoint⟩ where
  toFun t := ⟨c.normalizationHomotopy.path t, by
    change star (affineKasparovOperator c.operator c.normalized.operator (t : ℝ)) = _
    simp only [affineKasparovOperator, star_add, star_smul, star_sub, star_one,
      Complex.star_def, Complex.conj_ofReal, hc.star_eq, c.normalized_selfadjoint.star_eq]⟩
  continuous_toFun := c.normalizationHomotopy.path.continuous.subtype_mk _
  source' := Subtype.ext c.normalizationHomotopy.path.source
  target' := Subtype.ext c.normalizationHomotopy.path.target

theorem oddFredholmSelfAdjointNormalizationPath_square_compact (c : OddKasparovCycle α₁ β₁ E)
    (hc : IsSelfAdjoint c.operator) (hrep : c.scalarSupportProjection = 1) (t : I) :
    IsModuleCompact (((oddFredholmSelfAdjointNormalizationPath c hc t :
      AdjointableMap B E E) * oddFredholmSelfAdjointNormalizationPath c hc t) - 1) := by
  have h := (c.normalizationHomotopy.conditions t).square_mod_compact 1
  change IsModuleCompact ((_ * _ - 1) * c.scalarSupportProjection) at h
  simpa only [hrep, mul_one] using h

theorem oddFredholmScalarCycle_operatorK1Index
    (hE : IsCountablyGeneratedModule B E) (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) * F - 1)) :
    (oddKTheoryScalarFredholmCycle (Γ := PUnit) hE F F.property hF).operatorK1Index =
      oddFredholmStabilizedIndex hE F hF := by
  let c := oddKTheoryScalarFredholmCycle (Γ := PUnit) hE F F.property hF
  have hrep : c.scalarSupportProjection = 1 := by
    change scalarModuleRepresentation (1 : ℂ) = 1
    rw [scalarModuleRepresentation_eq_smul_one, one_smul]
  let u := oddFredholmUnitalScalarSupportEquiv c hrep
  have hnorm := oddFredholmStabilizedIndex_intertwine u
    c.scalarSupportNormalizedCycle.countablyGenerated hE c.scalarSupportFredholmSelfAdjoint
    ⟨c.normalized.operator, c.normalized_selfadjoint⟩
    c.scalarSupportNormalizedCycle_square_isModuleCompact
    (by
      have hh := c.operatorConditions_normalized.square_mod_compact 1
      change IsModuleCompact ((_ * _ - 1) * c.scalarSupportProjection) at hh
      simpa only [hrep, mul_one] using hh)
    (by
      intro x
      have hh := congrArg (fun T => T (u x))
        (oddFredholmUnitalScalarSupportEquiv_normalized c hrep)
      simpa only [u, HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply,
        OddKasparovCycle.scalarSupportFredholmSelfAdjoint] using hh)
  have hp := oddFredholmStabilizedIndex_selfAdjointPath hE
    (oddFredholmSelfAdjointNormalizationPath c F.property)
    (oddFredholmSelfAdjointNormalizationPath_square_compact c F.property hrep)
  exact hnorm.trans hp.symm

end BC4lean.KKTheory
