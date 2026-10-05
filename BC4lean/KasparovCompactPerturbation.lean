import BC4lean.KasparovOperatorHomotopy
import BC4lean.EquivariantCompactOperator
import Mathlib.Tactic.Module

/-! # Linear operator homotopies for locally compact perturbations

On one fixed graded, represented equivariant Hilbert module, two admissible
Kasparov operators joined by a locally compact perturbation have an explicit
norm-continuous linear operator homotopy. Local compactness means that the
operator difference becomes compact after right multiplication by each
represented algebra element. Neither global compactness of the difference nor
commutation of the two operators is assumed.

The square defect is controlled by the exact noncommutative identity below.
This constructs a fixed-module operator homotopy; identification with homotopies
over interval coefficient algebras is a separate construction.
-/

noncomputable section
namespace BC4lean.KKTheory

open unitInterval

variable {Γ A B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

/-- The real affine interpolation of two adjointable operators. -/
def affineKasparovOperator (F₀ F₁ : AdjointableMap B E E) (t : ℝ) :
    AdjointableMap B E E :=
  (1 - (t : ℂ)) • F₀ + (t : ℂ) • F₁

/-- Affine interpolation is continuous in the actual operator norm. -/
theorem continuous_affineKasparovOperator (F₀ F₁ : AdjointableMap B E E) :
    Continuous (affineKasparovOperator F₀ F₁) := by
  exact ((continuous_const.sub Complex.continuous_ofReal).smul continuous_const).add
    (Complex.continuous_ofReal.smul continuous_const)

/-- The affine operator path has the indicated endpoints. -/
def affineKasparovOperatorPath (F₀ F₁ : AdjointableMap B E E) : Path F₀ F₁ where
  toFun t := affineKasparovOperator F₀ F₁ (t : ℝ)
  continuous_toFun := (continuous_affineKasparovOperator F₀ F₁).comp continuous_subtype_val
  source' := by simp [affineKasparovOperator]
  target' := by simp [affineKasparovOperator]

@[simp] theorem affineKasparovOperatorPath_apply (F₀ F₁ : AdjointableMap B E E) (t : I) :
    affineKasparovOperatorPath F₀ F₁ t = (1 - ((t : ℝ) : ℂ)) • F₀ + ((t : ℝ) : ℂ) • F₁ := rfl

/-- Exact square-defect identity; no commutation of the operators is required. -/
theorem affineKasparovOperator_square_defect (F₀ F₁ : AdjointableMap B E E) (t : ℝ) :
    affineKasparovOperator F₀ F₁ t * affineKasparovOperator F₀ F₁ t - 1 =
      (1 - (t : ℂ)) • (F₀ * F₀ - 1) + (t : ℂ) • (F₁ * F₁ - 1) -
        ((t : ℂ) * (1 - (t : ℂ))) • ((F₁ - F₀) * (F₁ - F₀)) := by
  simp only [affineKasparovOperator, add_mul, mul_add, sub_mul, mul_sub,
    smul_mul_assoc, mul_smul_comm]
  module

/-- The selfadjointness defect interpolates linearly because the coefficients are real. -/
theorem affineKasparovOperator_selfadjoint_defect
    (F₀ F₁ R : AdjointableMap B E E) (t : ℝ) :
    (affineKasparovOperator F₀ F₁ t - star (affineKasparovOperator F₀ F₁ t)) * R =
      (1 - (t : ℂ)) • ((F₀ - star F₀) * R) + (t : ℂ) • ((F₁ - star F₁) * R) := by
  have hs : star (1 - (t : ℂ)) = 1 - (t : ℂ) := by simp
  have ht : star (t : ℂ) = (t : ℂ) := by simp
  simp only [affineKasparovOperator, star_add, star_smul, hs, ht,
    sub_mul, add_mul, smul_mul_assoc]
  module

/-- The commutator defect interpolates linearly. -/
theorem affineKasparovOperator_commutator (F₀ F₁ R : AdjointableMap B E E) (t : ℝ) :
    affineKasparovOperator F₀ F₁ t * R - R * affineKasparovOperator F₀ F₁ t =
      (1 - (t : ℂ)) • (F₀ * R - R * F₀) + (t : ℂ) • (F₁ * R - R * F₁) := by
  simp only [affineKasparovOperator, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  module

/-- Compatible group conjugation respects the affine interpolation. -/
theorem conjugate_affineKasparovOperator (U : EquivariantHilbertModule β E)
    (g : Γ) (F₀ F₁ : AdjointableMap B E E) (t : ℝ) :
    U.conjugateOperator g (affineKasparovOperator F₀ F₁ t) =
      (1 - (t : ℂ)) • U.conjugateOperator g F₀ + (t : ℂ) • U.conjugateOperator g F₁ := by
  let L := U.conjugateMapContinuousLinearMap U g
  change L ((1 - (t : ℂ)) • F₀ + (t : ℂ) • F₁) =
    (1 - (t : ℂ)) • L F₀ + (t : ℂ) • L F₁
  simp only [map_add, map_smul]

/-- The equivariance defect interpolates linearly. -/
theorem affineKasparovOperator_equivariance_defect (U : EquivariantHilbertModule β E)
    (g : Γ) (F₀ F₁ R : AdjointableMap B E E) (t : ℝ) :
    (U.conjugateOperator g (affineKasparovOperator F₀ F₁ t) -
      affineKasparovOperator F₀ F₁ t) * R =
      (1 - (t : ℂ)) • ((U.conjugateOperator g F₀ - F₀) * R) +
        (t : ℂ) • ((U.conjugateOperator g F₁ - F₁) * R) := by
  rw [conjugate_affineKasparovOperator]
  simp only [affineKasparovOperator, sub_mul, add_mul, smul_mul_assoc]
  module

variable [StarOrderedRing B] [CompleteSpace E]

namespace KasparovCycle

/-- Every real affine combination remains admissible when the perturbation is
locally compact with respect to the fixed representation. -/
theorem operatorConditions_affine_compactPerturbation (c : KasparovCycle α β E)
    (F₁ : AdjointableMap B E E) (hF₁ : c.OperatorConditions F₁)
    (hδ : ∀ a, IsModuleCompact ((F₁ - c.operator) * c.representation a)) (t : ℝ) :
    c.OperatorConditions (affineKasparovOperator c.operator F₁ t) where
  operator_odd := by
    exact (c.operator_odd.smul (1 - (t : ℂ))).add (hF₁.operator_odd.smul (t : ℂ))
  selfadjoint_mod_compact a := by
    rw [affineKasparovOperator_selfadjoint_defect]
    exact ((c.selfadjoint_mod_compact a).smul (1 - (t : ℂ))).add
      ((hF₁.selfadjoint_mod_compact a).smul (t : ℂ))
  square_mod_compact a := by
    have hδsq : IsModuleCompact ((F₁ - c.operator) * (F₁ - c.operator) *
        c.representation a) := by
      rw [mul_assoc]
      exact mul_mem_moduleCompact_left (F₁ - c.operator) (hδ a)
    rw [affineKasparovOperator_square_defect, sub_mul, add_mul]
    simp only [smul_mul_assoc]
    exact (((c.square_mod_compact a).smul (1 - (t : ℂ))).add
      ((hF₁.square_mod_compact a).smul (t : ℂ))).sub
        (hδsq.smul ((t : ℂ) * (1 - (t : ℂ))))
  commutator_compact a := by
    rw [affineKasparovOperator_commutator]
    exact ((c.commutator_compact a).smul (1 - (t : ℂ))).add
      ((hF₁.commutator_compact a).smul (t : ℂ))
  equivariance_mod_compact g a := by
    rw [affineKasparovOperator_equivariance_defect]
    exact ((c.equivariance_mod_compact g a).smul (1 - (t : ℂ))).add
      ((hF₁.equivariance_mod_compact g a).smul (t : ℂ))

end KasparovCycle

namespace KasparovOperatorHomotopy

/-- The actual norm-continuous operator homotopy associated to a locally compact
perturbation, keeping the complete module, grading, representation and action fixed. -/
def compactPerturbation (c : KasparovCycle α β E) (F₁ : AdjointableMap B E E)
    (hF₁ : c.OperatorConditions F₁)
    (hδ : ∀ a, IsModuleCompact ((F₁ - c.operator) * c.representation a)) :
    KasparovOperatorHomotopy c c.operator F₁ where
  path := affineKasparovOperatorPath c.operator F₁
  conditions t := c.operatorConditions_affine_compactPerturbation F₁ hF₁ hδ (t : ℝ)

@[simp] theorem compactPerturbation_path_apply (c : KasparovCycle α β E)
    (F₁ : AdjointableMap B E E) (hF₁ : c.OperatorConditions F₁)
    (hδ : ∀ a, IsModuleCompact ((F₁ - c.operator) * c.representation a)) (t : I) :
    (compactPerturbation c F₁ hF₁ hδ).path t =
      (1 - ((t : ℝ) : ℂ)) • c.operator + ((t : ℝ) : ℂ) • F₁ := rfl

end KasparovOperatorHomotopy
end BC4lean.KKTheory
