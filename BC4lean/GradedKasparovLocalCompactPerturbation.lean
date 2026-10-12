import BC4lean.GradedKasparovCycle
import BC4lean.KasparovCompactPerturbation
import Mathlib.Tactic.NoncommRing

/-! # Locally compact perturbations of genuinely graded cycles

Both algebra gradings may be nontrivial. The square calculation uses the
graded source commutator twice, and the module grading is used only as its
actual complex-linear isometry. Every point of the affine operator path is
proved to satisfy the genuine localized cycle conditions.
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
  {δA : CStarGrading A} {δB : CStarGrading B}

namespace GradedKasparovCycle

/-- The full genuine graded conditions on the fixed represented module. -/
structure OperatorConditions (c : GradedKasparovCycle α β δA δB E)
    (T : AdjointableMap B E E) : Prop where
  operator_odd : c.grading.IsOdd c.grading T
  selfadjoint_mod_compact : ∀ a,
    IsModuleCompact ((T - star T) * c.representation a)
  square_mod_compact : ∀ a,
    IsModuleCompact ((T * T - 1) * c.representation a)
  commutator_compact : ∀ a,
    IsModuleCompact (T * c.representation a -
      c.representation (δA.automorphism a) * T)
  equivariance_mod_compact : ∀ g a,
    IsModuleCompact ((c.groupAction.conjugateOperator g T - T) * c.representation a)

theorem operatorConditions (c : GradedKasparovCycle α β δA δB E) :
    c.OperatorConditions c.operator where
  operator_odd := c.operator_odd
  selfadjoint_mod_compact := c.selfadjoint_mod_compact
  square_mod_compact := c.square_mod_compact
  commutator_compact := c.commutator_compact
  equivariance_mod_compact := c.equivariance_mod_compact

/-- Replace only the Fredholm operator, retaining all actual module data. -/
def withOperator (c : GradedKasparovCycle α β δA δB E)
    (T : AdjointableMap B E E) (hT : c.OperatorConditions T) :
    GradedKasparovCycle α β δA δB E :=
  { c with
    operator := T
    operator_odd := hT.operator_odd
    selfadjoint_mod_compact := hT.selfadjoint_mod_compact
    square_mod_compact := hT.square_mod_compact
    commutator_compact := hT.commutator_compact
    equivariance_mod_compact := hT.equivariance_mod_compact }

@[simp] theorem withOperator_operator (c : GradedKasparovCycle α β δA δB E)
    (T : AdjointableMap B E E) (hT : c.OperatorConditions T) :
    (c.withOperator T hT).operator = T := rfl

@[simp] theorem withOperator_self (c : GradedKasparovCycle α β δA δB E) :
    c.withOperator c.operator c.operatorConditions = c := by
  cases c
  rfl

/-- Adjoint local compactness implies left local compactness. -/
theorem locallyCompact_left_of_adjoint (c : GradedKasparovCycle α β δA δB E)
    (K : AdjointableMap B E E)
    (hK : ∀ a, IsModuleCompact (star K * c.representation a)) (a : A) :
    IsModuleCompact (c.representation a * K) := by
  have h := (hK (star a)).adjoint
  change IsModuleCompact (star (star K * c.representation (star a))) at h
  simpa only [star_mul, map_star, star_star] using h

/-- Equivariant conjugation preserves actual localized compactness. -/
theorem locallyCompact_conjugate (c : GradedKasparovCycle α β δA δB E)
    (K : AdjointableMap B E E)
    (hK : ∀ a, IsModuleCompact (K * c.representation a)) (g : Γ) (a : A) :
    IsModuleCompact (c.groupAction.conjugateOperator g K * c.representation a) := by
  have h := (hK (α.automorphism g⁻¹ a)).conjugateOperator c.groupAction g
  change IsModuleCompact (c.groupAction.conjugateMap c.groupAction g
    (K.comp (c.representation (α.automorphism g⁻¹ a)))) at h
  rw [EquivariantHilbertModule.conjugateMap_comp] at h
  change IsModuleCompact (c.groupAction.conjugateOperator g K *
    c.groupAction.conjugateOperator g (c.representation (α.automorphism g⁻¹ a))) at h
  simpa only [c.representation_equivariant, CStarAlgebraAction.apply_inv_apply] using h

/-- Actual odd perturbations locally compact together with their adjoints
preserve all four graded Kasparov defects. -/
theorem operatorConditions_add_locallyCompact (c : GradedKasparovCycle α β δA δB E)
    (K : AdjointableMap B E E) (hodd : c.grading.IsOdd c.grading K)
    (hK : ∀ a, IsModuleCompact (K * c.representation a))
    (hKstar : ∀ a, IsModuleCompact (star K * c.representation a)) :
    c.OperatorConditions (c.operator + K) where
  operator_odd := c.operator_odd.add hodd
  selfadjoint_mod_compact a := by
    have heq : (c.operator + K - star (c.operator + K)) * c.representation a =
        (c.operator - star c.operator) * c.representation a +
        (K * c.representation a - star K * c.representation a) := by
      rw [star_add]
      noncomm_ring
    rw [heq]
    exact (c.selfadjoint_mod_compact a).add ((hK a).sub (hKstar a))
  square_mod_compact a := by
    have heq : ((c.operator + K) * (c.operator + K) - 1) * c.representation a =
        (c.operator * c.operator - 1) * c.representation a +
        c.operator * (K * c.representation a) +
        K * (c.operator * c.representation a -
          c.representation (δA.automorphism a) * c.operator) +
        (K * c.representation (δA.automorphism a)) * c.operator +
        K * (K * c.representation a) := by noncomm_ring
    rw [heq]
    exact ((((c.square_mod_compact a).add
      (mul_mem_moduleCompact_left c.operator (hK a))).add
        (mul_mem_moduleCompact_left K (c.commutator_compact a))).add
          (mul_mem_moduleCompact_right (hK (δA.automorphism a)) c.operator)).add
            (mul_mem_moduleCompact_left K (hK a))
  commutator_compact a := by
    have heq : (c.operator + K) * c.representation a -
        c.representation (δA.automorphism a) * (c.operator + K) =
        (c.operator * c.representation a -
          c.representation (δA.automorphism a) * c.operator) +
        (K * c.representation a - c.representation (δA.automorphism a) * K) := by
      noncomm_ring
    rw [heq]
    exact (c.commutator_compact a).add ((hK a).sub
      (c.locallyCompact_left_of_adjoint K hKstar (δA.automorphism a)))
  equivariance_mod_compact g a := by
    let L := c.groupAction.conjugateMapContinuousLinearMap c.groupAction g
    have hadd : c.groupAction.conjugateOperator g (c.operator + K) =
        c.groupAction.conjugateOperator g c.operator + c.groupAction.conjugateOperator g K :=
      L.map_add c.operator K
    rw [hadd]
    have heq : (c.groupAction.conjugateOperator g c.operator +
        c.groupAction.conjugateOperator g K - (c.operator + K)) * c.representation a =
        (c.groupAction.conjugateOperator g c.operator - c.operator) * c.representation a +
        (c.groupAction.conjugateOperator g K * c.representation a - K * c.representation a) := by
      noncomm_ring
    rw [heq]
    exact (c.equivariance_mod_compact g a).add
      ((c.locallyCompact_conjugate K hK g a).sub (hK a))

/-- The symmetrizing difference is compact only after localization. -/
def symmetrizingPerturbation (c : GradedKasparovCycle α β δA δB E) :
    AdjointableMap B E E := (2 : ℂ)⁻¹ • (star c.operator - c.operator)

theorem star_symmetrizingPerturbation (c : GradedKasparovCycle α β δA δB E) :
    star c.symmetrizingPerturbation = -c.symmetrizingPerturbation := by
  simp only [symmetrizingPerturbation, star_smul, star_inv₀, star_ofNat,
    star_sub, star_star, ← smul_neg, neg_sub]

theorem symmetrizingPerturbation_locallyCompact (c : GradedKasparovCycle α β δA δB E)
    (a : A) : IsModuleCompact (c.symmetrizingPerturbation * c.representation a) := by
  have h := ((c.selfadjoint_mod_compact a).neg).smul (2 : ℂ)⁻¹
  simpa only [symmetrizingPerturbation, smul_mul_assoc, ← neg_mul, neg_sub] using h

theorem symmetrizingPerturbation_isOdd (c : GradedKasparovCycle α β δA δB E) :
    c.grading.IsOdd c.grading c.symmetrizingPerturbation := by
  have hh : c.grading.IsOdd c.grading (star c.operator - c.operator) := by
    intro x
    simp only [AdjointableMap.coe_sub_apply, AdjointableMap.star_eq_adjoint]
    rw [map_sub, c.operator_odd.adjoint x, c.operator_odd x]
    abel
  exact hh.smul (2 : ℂ)⁻¹

theorem operatorConditions_symmetrization (c : GradedKasparovCycle α β δA δB E) :
    c.OperatorConditions (c.operator + c.symmetrizingPerturbation) :=
  c.operatorConditions_add_locallyCompact c.symmetrizingPerturbation
    c.symmetrizingPerturbation_isOdd c.symmetrizingPerturbation_locallyCompact
    (fun a => by
      rw [star_symmetrizingPerturbation, neg_mul]
      exact (c.symmetrizingPerturbation_locallyCompact a).neg)

theorem symmetrizedOperator_selfadjoint (c : GradedKasparovCycle α β δA δB E) :
    star (c.operator + c.symmetrizingPerturbation) =
      c.operator + c.symmetrizingPerturbation := by
  simp only [symmetrizingPerturbation, star_add, star_smul, star_sub, star_star]
  norm_num
  module

def symmetrized (c : GradedKasparovCycle α β δA δB E) :
    GradedKasparovCycle α β δA δB E :=
  c.withOperator (c.operator + c.symmetrizingPerturbation) c.operatorConditions_symmetrization

theorem symmetrized_selfadjoint (c : GradedKasparovCycle α β δA δB E) :
    IsSelfAdjoint c.symmetrized.operator := c.symmetrizedOperator_selfadjoint

/-- Twice applying the genuine graded commutator gives the ordinary
commutator of the square; no triviality of the source grading is used. -/
theorem square_commutator_compact (c : GradedKasparovCycle α β δA δB E) (a : A) :
    IsModuleCompact (c.operator * c.operator * c.representation a -
      c.representation a * (c.operator * c.operator)) := by
  have heq : c.operator * c.operator * c.representation a -
      c.representation a * (c.operator * c.operator) =
      c.operator * (c.operator * c.representation a -
        c.representation (δA.automorphism a) * c.operator) +
      (c.operator * c.representation (δA.automorphism a) -
        c.representation a * c.operator) * c.operator := by noncomm_ring
  rw [heq]
  have h := c.commutator_compact (δA.automorphism a)
  simp only [CStarGrading.automorphism_sq] at h
  exact IsModuleCompact.add
    (mul_mem_moduleCompact_left c.operator (c.commutator_compact a))
    (mul_mem_moduleCompact_right h c.operator)

/-- Every affine point is admissible for actual localized differences. -/
theorem operatorConditions_affine_compactPerturbation
    (c : GradedKasparovCycle α β δA δB E) (T : AdjointableMap B E E)
    (hT : c.OperatorConditions T)
    (hK : ∀ a, IsModuleCompact ((T - c.operator) * c.representation a)) (t : ℝ) :
    c.OperatorConditions (affineKasparovOperator c.operator T t) where
  operator_odd :=
    (c.operator_odd.smul (1 - (t : ℂ))).add (hT.operator_odd.smul (t : ℂ))
  selfadjoint_mod_compact a := by
    rw [affineKasparovOperator_selfadjoint_defect]
    exact ((c.selfadjoint_mod_compact a).smul (1 - (t : ℂ))).add
      ((hT.selfadjoint_mod_compact a).smul (t : ℂ))
  square_mod_compact a := by
    have hKsq : IsModuleCompact ((T - c.operator) * (T - c.operator) *
        c.representation a) := by
      rw [mul_assoc]
      exact mul_mem_moduleCompact_left (T - c.operator) (hK a)
    rw [affineKasparovOperator_square_defect, sub_mul, add_mul]
    simp only [smul_mul_assoc]
    exact (((c.square_mod_compact a).smul (1 - (t : ℂ))).add
      ((hT.square_mod_compact a).smul (t : ℂ))).sub
        (hKsq.smul ((t : ℂ) * (1 - (t : ℂ))))
  commutator_compact a := by
    have heq : affineKasparovOperator c.operator T t * c.representation a -
        c.representation (δA.automorphism a) * affineKasparovOperator c.operator T t =
        (1 - (t : ℂ)) • (c.operator * c.representation a -
          c.representation (δA.automorphism a) * c.operator) +
        (t : ℂ) • (T * c.representation a - c.representation (δA.automorphism a) * T) := by
      simp only [affineKasparovOperator, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
      module
    rw [heq]
    exact ((c.commutator_compact a).smul (1 - (t : ℂ))).add
      ((hT.commutator_compact a).smul (t : ℂ))
  equivariance_mod_compact g a := by
    rw [affineKasparovOperator_equivariance_defect]
    exact ((c.equivariance_mod_compact g a).smul (1 - (t : ℂ))).add
      ((hT.equivariance_mod_compact g a).smul (t : ℂ))

end GradedKasparovCycle

/-- An actual norm-continuous operator path of genuinely graded cycles. -/
structure GradedKasparovOperatorHomotopy (c : GradedKasparovCycle α β δA δB E)
    (T₀ T₁ : AdjointableMap B E E) where
  path : Path T₀ T₁
  conditions : ∀ t : I, c.OperatorConditions (path t)

namespace GradedKasparovOperatorHomotopy

variable {c : GradedKasparovCycle α β δA δB E} {T₀ T₁ : AdjointableMap B E E}

def cycleAt (h : GradedKasparovOperatorHomotopy c T₀ T₁) (t : I) :
    GradedKasparovCycle α β δA δB E := c.withOperator (h.path t) (h.conditions t)

theorem source_conditions (h : GradedKasparovOperatorHomotopy c T₀ T₁) :
    c.OperatorConditions T₀ := by simpa only [Path.source] using h.conditions 0

theorem target_conditions (h : GradedKasparovOperatorHomotopy c T₀ T₁) :
    c.OperatorConditions T₁ := by simpa only [Path.target] using h.conditions 1

@[simp] theorem source_cycleAt (h : GradedKasparovOperatorHomotopy c T₀ T₁) :
    h.cycleAt 0 = c.withOperator T₀ h.source_conditions := by
  simp only [cycleAt, Path.source]

@[simp] theorem target_cycleAt (h : GradedKasparovOperatorHomotopy c T₀ T₁) :
    h.cycleAt 1 = c.withOperator T₁ h.target_conditions := by
  simp only [cycleAt, Path.target]

def compactPerturbation (c : GradedKasparovCycle α β δA δB E)
    (T : AdjointableMap B E E) (hT : c.OperatorConditions T)
    (hK : ∀ a, IsModuleCompact ((T - c.operator) * c.representation a)) :
    GradedKasparovOperatorHomotopy c c.operator T where
  path := affineKasparovOperatorPath c.operator T
  conditions t := c.operatorConditions_affine_compactPerturbation T hT hK (t : ℝ)

end GradedKasparovOperatorHomotopy

namespace GradedKasparovCycle

def symmetrizationHomotopy (c : GradedKasparovCycle α β δA δB E) :
    GradedKasparovOperatorHomotopy c c.operator c.symmetrized.operator :=
  GradedKasparovOperatorHomotopy.compactPerturbation c _ c.operatorConditions_symmetrization
    (fun a => by
      change IsModuleCompact ((c.operator + c.symmetrizingPerturbation - c.operator) *
        c.representation a)
      rw [add_sub_cancel_left]
      exact c.symmetrizingPerturbation_locallyCompact a)

end GradedKasparovCycle
end BC4lean.KKTheory
