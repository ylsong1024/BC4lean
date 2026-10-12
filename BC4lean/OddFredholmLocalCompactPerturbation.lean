import BC4lean.KasparovCompactPerturbation
import BC4lean.OddKasparovOperatorHomotopy
import Mathlib.Tactic.NoncommRing

/-! # Genuine local compact perturbations and symmetrization for odd cycles

Every endpoint condition is derived from the original four Kasparov defects.
The explicit affine operator path realizes each two-sided locally compact
perturbation, including selfadjoint averaging, on the original actual module.
-/

noncomputable section
namespace BC4lean.KKTheory

open unitInterval

variable {Γ A B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace OddKasparovCycle

/-- Every real affine combination remains admissible when the perturbation is
locally compact with respect to the fixed representation. -/
theorem operatorConditions_affine_compactPerturbation (c : OddKasparovCycle α β E)
    (F₁ : AdjointableMap B E E) (hF₁ : c.OperatorConditions F₁)
    (hδ : ∀ a, IsModuleCompact ((F₁ - c.operator) * c.representation a)) (t : ℝ) :
    c.OperatorConditions (affineKasparovOperator c.operator F₁ t) where
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

end OddKasparovCycle

namespace OddKasparovOperatorHomotopy

/-- The actual norm-continuous operator homotopy associated to a locally compact
perturbation, keeping the complete module, representation and action fixed. -/
def compactPerturbation (c : OddKasparovCycle α β E) (F₁ : AdjointableMap B E E)
    (hF₁ : c.OperatorConditions F₁)
    (hδ : ∀ a, IsModuleCompact ((F₁ - c.operator) * c.representation a)) :
    OddKasparovOperatorHomotopy c c.operator F₁ where
  path := affineKasparovOperatorPath c.operator F₁
  conditions t := c.operatorConditions_affine_compactPerturbation F₁ hF₁ hδ (t : ℝ)

@[simp] theorem compactPerturbation_path_apply (c : OddKasparovCycle α β E)
    (F₁ : AdjointableMap B E E) (hF₁ : c.OperatorConditions F₁)
    (hδ : ∀ a, IsModuleCompact ((F₁ - c.operator) * c.representation a)) (t : I) :
    (compactPerturbation c F₁ hF₁ hδ).path t =
      (1 - ((t : ℝ) : ℂ)) • c.operator + ((t : ℝ) : ℂ) • F₁ := rfl

end OddKasparovOperatorHomotopy

namespace OddKasparovCycle

/-- Right local compactness of the adjoint gives left local compactness. -/
theorem locallyCompact_left_of_adjoint (c : OddKasparovCycle α β E)
    (δ : AdjointableMap B E E)
    (hδ : ∀ a, IsModuleCompact (star δ * c.representation a)) (a : A) :
    IsModuleCompact (c.representation a * δ) := by
  have h := (hδ (star a)).adjoint
  change IsModuleCompact (star (star δ * c.representation (star a))) at h
  simpa only [star_mul, map_star, star_star] using h

/-- Group conjugation preserves local compactness for an equivariant representation. -/
theorem locallyCompact_conjugate (c : OddKasparovCycle α β E)
    (δ : AdjointableMap B E E)
    (hδ : ∀ a, IsModuleCompact (δ * c.representation a)) (g : Γ) (a : A) :
    IsModuleCompact (c.groupAction.conjugateOperator g δ * c.representation a) := by
  have h := (hδ (α.automorphism g⁻¹ a)).conjugateOperator c.groupAction g
  change IsModuleCompact (c.groupAction.conjugateMap c.groupAction g
    (δ.comp (c.representation (α.automorphism g⁻¹ a)))) at h
  rw [EquivariantHilbertModule.conjugateMap_comp] at h
  change IsModuleCompact (c.groupAction.conjugateOperator g δ *
    c.groupAction.conjugateOperator g (c.representation (α.automorphism g⁻¹ a))) at h
  simpa only [c.representation_equivariant, CStarAlgebraAction.apply_inv_apply] using h

/-- All four cycle conditions persist under an actual odd two-sided locally
compact perturbation. No admissibility of the new endpoint is assumed. -/
theorem operatorConditions_add_locallyCompact (c : OddKasparovCycle α β E)
    (δ : AdjointableMap B E E)
    (hδ : ∀ a, IsModuleCompact (δ * c.representation a))
    (hδstar : ∀ a, IsModuleCompact (star δ * c.representation a)) :
    c.OperatorConditions (c.operator + δ) where
  selfadjoint_mod_compact a := by
    have heq : (c.operator + δ - star (c.operator + δ)) * c.representation a =
        (c.operator - star c.operator) * c.representation a +
        (δ * c.representation a - star δ * c.representation a) := by
      rw [star_add]
      noncomm_ring
    rw [heq]
    exact (c.selfadjoint_mod_compact a).add ((hδ a).sub (hδstar a))
  square_mod_compact a := by
    have heq : ((c.operator + δ) * (c.operator + δ) - 1) * c.representation a =
        (c.operator * c.operator - 1) * c.representation a +
        c.operator * (δ * c.representation a) +
        δ * (c.operator * c.representation a - c.representation a * c.operator) +
        (δ * c.representation a) * c.operator + δ * (δ * c.representation a) := by
      noncomm_ring
    rw [heq]
    exact ((((c.square_mod_compact a).add
      (mul_mem_moduleCompact_left c.operator (hδ a))).add
        (mul_mem_moduleCompact_left δ (c.commutator_compact a))).add
          (mul_mem_moduleCompact_right (hδ a) c.operator)).add
            (mul_mem_moduleCompact_left δ (hδ a))
  commutator_compact a := by
    have heq : (c.operator + δ) * c.representation a -
        c.representation a * (c.operator + δ) =
        (c.operator * c.representation a - c.representation a * c.operator) +
        (δ * c.representation a - c.representation a * δ) := by noncomm_ring
    rw [heq]
    exact (c.commutator_compact a).add
      ((hδ a).sub (c.locallyCompact_left_of_adjoint δ hδstar a))
  equivariance_mod_compact g a := by
    let L := c.groupAction.conjugateMapContinuousLinearMap c.groupAction g
    have hadd : c.groupAction.conjugateOperator g (c.operator + δ) =
        c.groupAction.conjugateOperator g c.operator + c.groupAction.conjugateOperator g δ :=
      L.map_add c.operator δ
    rw [hadd]
    have heq : (c.groupAction.conjugateOperator g c.operator +
        c.groupAction.conjugateOperator g δ - (c.operator + δ)) * c.representation a =
        (c.groupAction.conjugateOperator g c.operator - c.operator) * c.representation a +
        (c.groupAction.conjugateOperator g δ * c.representation a - δ * c.representation a) := by
      noncomm_ring
    rw [heq]
    exact (c.equivariance_mod_compact g a).add
      ((c.locallyCompact_conjugate δ hδ g a).sub (hδ a))

/-- The explicitly locally compact difference between an operator and its symmetrization. -/
def symmetrizingPerturbation (c : OddKasparovCycle α β E) : AdjointableMap B E E :=
  (2 : ℂ)⁻¹ • (star c.operator - c.operator)

/-- Symmetrizing perturbations have skew-adjoint sign. -/
theorem star_symmetrizingPerturbation (c : OddKasparovCycle α β E) :
    star c.symmetrizingPerturbation = -c.symmetrizingPerturbation := by
  simp only [symmetrizingPerturbation, star_smul, star_inv₀, star_ofNat,
    star_sub, star_star, ← smul_neg, neg_sub]

/-- The perturbation is locally compact by the original selfadjointness defect. -/
theorem symmetrizingPerturbation_locallyCompact (c : OddKasparovCycle α β E) (a : A) :
    IsModuleCompact (c.symmetrizingPerturbation * c.representation a) := by
  have h := ((c.selfadjoint_mod_compact a).neg).smul (2 : ℂ)⁻¹
  simpa only [symmetrizingPerturbation, smul_mul_assoc, ← neg_mul, neg_sub] using h

/-- Symmetrization supplies a verified selfadjoint admissible operator. -/
theorem operatorConditions_symmetrization (c : OddKasparovCycle α β E) :
    c.OperatorConditions (c.operator + c.symmetrizingPerturbation) :=
  c.operatorConditions_add_locallyCompact c.symmetrizingPerturbation
    c.symmetrizingPerturbation_locallyCompact
    (fun a => by
      rw [star_symmetrizingPerturbation, neg_mul]
      exact (c.symmetrizingPerturbation_locallyCompact a).neg)

/-- The symmetrized endpoint is exactly selfadjoint. -/
theorem symmetrizedOperator_selfadjoint (c : OddKasparovCycle α β E) :
    star (c.operator + c.symmetrizingPerturbation) = c.operator + c.symmetrizingPerturbation := by
  simp only [symmetrizingPerturbation, star_add, star_smul, star_sub, star_star]
  norm_num
  module

/-- The actual selfadjoint average, on the original represented module. -/
def symmetrized (c : OddKasparovCycle α β E) : OddKasparovCycle α β E :=
  c.withOperator (c.operator + c.symmetrizingPerturbation) c.operatorConditions_symmetrization

theorem symmetrized_selfadjoint (c : OddKasparovCycle α β E) :
    IsSelfAdjoint c.symmetrized.operator := c.symmetrizedOperator_selfadjoint

/-- The actual affine operator homotopy from the original cycle to its selfadjoint symmetrization. -/
def symmetrizationHomotopy (c : OddKasparovCycle α β E) :
    OddKasparovOperatorHomotopy c c.operator (c.operator + c.symmetrizingPerturbation) :=
  OddKasparovOperatorHomotopy.compactPerturbation c (c.operator + c.symmetrizingPerturbation)
    c.operatorConditions_symmetrization
    (fun a => by
      rw [add_sub_cancel_left]
      exact c.symmetrizingPerturbation_locallyCompact a)

end OddKasparovCycle
end BC4lean.KKTheory
