import BC4lean.KasparovCompactPerturbation
import Mathlib.Tactic.NoncommRing

/-! # Admissibility of locally compact perturbations

An odd perturbation which is locally compact together with its adjoint gives
an actual new Kasparov operator and an affine operator homotopy. In particular
symmetrization gives a selfadjoint representative on the same module.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ A B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace KasparovCycle

/-- Right local compactness of the adjoint gives left local compactness. -/
theorem locallyCompact_left_of_adjoint (c : KasparovCycle α β E)
    (δ : AdjointableMap B E E)
    (hδ : ∀ a, IsModuleCompact (star δ * c.representation a)) (a : A) :
    IsModuleCompact (c.representation a * δ) := by
  have h := (hδ (star a)).adjoint
  change IsModuleCompact (star (star δ * c.representation (star a))) at h
  simpa only [star_mul, map_star, star_star] using h

/-- Group conjugation preserves local compactness for an equivariant representation. -/
theorem locallyCompact_conjugate (c : KasparovCycle α β E)
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
theorem operatorConditions_add_locallyCompact (c : KasparovCycle α β E)
    (δ : AdjointableMap B E E) (hodd : c.grading.IsOdd c.grading δ)
    (hδ : ∀ a, IsModuleCompact (δ * c.representation a))
    (hδstar : ∀ a, IsModuleCompact (star δ * c.representation a)) :
    c.OperatorConditions (c.operator + δ) where
  operator_odd := c.operator_odd.add hodd
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
def symmetrizingPerturbation (c : KasparovCycle α β E) : AdjointableMap B E E :=
  (2 : ℂ)⁻¹ • (star c.operator - c.operator)

/-- Symmetrizing perturbations have skew-adjoint sign. -/
theorem star_symmetrizingPerturbation (c : KasparovCycle α β E) :
    star c.symmetrizingPerturbation = -c.symmetrizingPerturbation := by
  simp only [symmetrizingPerturbation, star_smul, star_inv₀, star_ofNat,
    star_sub, star_star, ← smul_neg, neg_sub]

/-- The perturbation is locally compact by the original selfadjointness defect. -/
theorem symmetrizingPerturbation_locallyCompact (c : KasparovCycle α β E) (a : A) :
    IsModuleCompact (c.symmetrizingPerturbation * c.representation a) := by
  have h := ((c.selfadjoint_mod_compact a).neg).smul (2 : ℂ)⁻¹
  simpa only [symmetrizingPerturbation, smul_mul_assoc, ← neg_mul, neg_sub] using h

/-- Symmetrization respects odd degree. -/
theorem symmetrizingPerturbation_isOdd (c : KasparovCycle α β E) :
    c.grading.IsOdd c.grading c.symmetrizingPerturbation := by
  have h := c.operator_odd.adjoint.add (c.operator_odd.smul (-1))
  change c.grading.IsOdd c.grading
    (c.operator.adjoint + (-1 : ℂ) • c.operator) at h
  have hh : c.grading.IsOdd c.grading (star c.operator - c.operator) := by
    simpa only [AdjointableMap.star_eq_adjoint, neg_one_smul, sub_eq_add_neg] using h
  exact hh.smul (2 : ℂ)⁻¹

/-- Symmetrization supplies a verified selfadjoint admissible operator. -/
theorem operatorConditions_symmetrization (c : KasparovCycle α β E) :
    c.OperatorConditions (c.operator + c.symmetrizingPerturbation) :=
  c.operatorConditions_add_locallyCompact c.symmetrizingPerturbation
    c.symmetrizingPerturbation_isOdd c.symmetrizingPerturbation_locallyCompact
    (fun a => by
      rw [star_symmetrizingPerturbation, neg_mul]
      exact (c.symmetrizingPerturbation_locallyCompact a).neg)

/-- The symmetrized endpoint is exactly selfadjoint. -/
theorem symmetrizedOperator_selfadjoint (c : KasparovCycle α β E) :
    star (c.operator + c.symmetrizingPerturbation) = c.operator + c.symmetrizingPerturbation := by
  simp only [symmetrizingPerturbation, star_add, star_smul, star_sub, star_star]
  norm_num
  module

/-- The actual affine operator homotopy from the original cycle to its selfadjoint symmetrization. -/
def symmetrizationHomotopy (c : KasparovCycle α β E) :
    KasparovOperatorHomotopy c c.operator (c.operator + c.symmetrizingPerturbation) :=
  KasparovOperatorHomotopy.compactPerturbation c (c.operator + c.symmetrizingPerturbation)
    c.operatorConditions_symmetrization
    (fun a => by
      rw [add_sub_cancel_left]
      exact c.symmetrizingPerturbation_locallyCompact a)

end KasparovCycle
end BC4lean.KKTheory
