import BC4lean.HilbertModuleJuliaSurjective
import BC4lean.StandardCountableFlatten
import BC4lean.StandardModuleFrame
import BC4lean.KasparovDirectSumIso

/-! # Actual stabilization by the standard coefficient Hilbert module

The actual summable generating frame supplies a dense adjointable synthesis
H_B → E. A nonzero scalar normalizes it to a contraction. The proved countable
Julia unitary absorbs E into H_B^∞, and the genuine coefficient reindexing
H_B^∞ ≅ H_B yields E ⊕ H_B ≅ H_B. No surjectivity of the generating synthesis,
orthogonal-range converse, scalar l² model, or assumed stabilization is used.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

namespace AdjointableMap

/-- A nonzero scalar contraction of any bounded adjointable map. -/
def contractiveNormalization (T : AdjointableMap B F E) : AdjointableMap B F E :=
  (((1 + ‖T‖)⁻¹ : ℝ) : ℂ) • T

omit [StarOrderedRing B] in
theorem norm_contractiveNormalization_le (T : AdjointableMap B F E) :
    ‖T.contractiveNormalization‖ ≤ 1 := by
  have hp : 0 < 1 + ‖T‖ := by positivity
  change ‖(((1 + ‖T‖)⁻¹ : ℝ) : ℂ) • T‖ ≤ 1
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
  have he : (1 + ‖T‖)⁻¹ * ‖T‖ = ‖T‖ / (1 + ‖T‖) := by rw [div_eq_mul_inv, mul_comm]
  rw [he]
  exact (div_le_one hp).mpr (by linarith)

omit [StarOrderedRing B] in
theorem contractiveNormalization_denseRange (T : AdjointableMap B F E) (hT : DenseRange T) :
    DenseRange T.contractiveNormalization := by
  have hp : 0 < 1 + ‖T‖ := by positivity
  have hc : ((((1 + ‖T‖)⁻¹ : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (inv_ne_zero (ne_of_gt hp))
  have hr : Set.range T.contractiveNormalization = Set.range T := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨((((1 + ‖T‖)⁻¹ : ℝ) : ℂ)) • x, ?_⟩
      rw [map_smul]
      rfl
    · rintro ⟨x, rfl⟩
      refine ⟨(((((1 + ‖T‖)⁻¹ : ℝ) : ℂ))⁻¹) • x, ?_⟩
      change ((((1 + ‖T‖)⁻¹ : ℝ) : ℂ)) • T (((((1 + ‖T‖)⁻¹ : ℝ) : ℂ))⁻¹ • x) = T x
      rw [map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]
  change Dense (Set.range T.contractiveNormalization)
  rw [hr]
  exact hT

end AdjointableMap

variable [CompleteSpace E]

/-- Stabilization built from an actual dense synthesis, via the countable Julia
unitary and genuine coefficient flattening. -/
def standardModuleAbsorptionOfDenseSynthesis
    (T : AdjointableMap B (StandardCountableHilbertModule B) E) (hT : DenseRange T) :
    HilbertModuleEquiv B (HilbertModuleSum B E (StandardCountableHilbertModule B))
      (StandardCountableHilbertModule B) :=
  ((HilbertModuleEquiv.refl (B := B) (E := E)).sum standardCountableInfiniteSumEquiv.symm).trans
    ((countableJuliaEquiv T.contractiveNormalization T.norm_contractiveNormalization_le
      (T.contractiveNormalization_denseRange hT)).trans standardCountableInfiniteSumEquiv)

/-- Every complete countably generated Hilbert B-module is actually absorbed by
the standard coefficient Hilbert module. -/
theorem exists_standardModuleStabilization (hE : IsCountablyGeneratedModule B E) :
    Nonempty (HilbertModuleEquiv B (HilbertModuleSum B E (StandardCountableHilbertModule B))
      (StandardCountableHilbertModule B)) := by
  obtain ⟨T, hT⟩ := exists_standardModuleSynthesis_denseRange hE
  exact ⟨standardModuleAbsorptionOfDenseSynthesis T hT⟩

/-- A chosen actual standard-module stabilization unitary. -/
def standardModuleStabilization (hE : IsCountablyGeneratedModule B E) :
    HilbertModuleEquiv B (HilbertModuleSum B E (StandardCountableHilbertModule B))
      (StandardCountableHilbertModule B) := (exists_standardModuleStabilization hE).some

end BC4lean.KKTheory
