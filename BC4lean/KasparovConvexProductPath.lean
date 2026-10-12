import BC4lean.KasparovCommonComparisonProduct
import BC4lean.LocalizedModuleFunctionalCalculus

/-! # Genuine analytic estimates on a convex product path

The affine path between two selfadjoint products retains its degree,
graded commutators, group defects, and all four connections. Its square
has an ordinary compact commutator with the source representation even
for a nontrivial source grading. Positive comparison gives the localized
positive-mod-compact square lower bound one half at every parameter.
The square defect of the raw affine path is not asserted compact.
-/

noncomputable section
namespace BC4lean.KKTheory
open unitInterval

variable {Γ A B C E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}

variable (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F)
  {R P : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation)}

local instance kasparovConvexProductPathLocalInstance1 : PartialOrder
    (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) := CStarAlgebra.spectralOrder _
local instance kasparovConvexProductPathLocalInstance2 : StarOrderedRing
    (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) := CStarAlgebra.spectralOrderedRing _

theorem affineProductOperator_isSelfAdjoint (hR : IsSelfAdjoint R) (hP : IsSelfAdjoint P)
    (t : ℝ) : IsSelfAdjoint (affineKasparovOperator R P t) := by
  change star (affineKasparovOperator R P t) = affineKasparovOperator R P t
  simp only [affineKasparovOperator, star_add, star_smul, star_sub, star_one,
    Complex.star_def, Complex.conj_ofReal, hR.star_eq, hP.star_eq]

theorem affineProductOperator_isOdd
    (hR : GradedKasparovTensorOperatorConditions c d R)
    (hP : GradedKasparovTensorOperatorConditions c d P) (t : ℝ) :
    (gradedKasparovTensorGrading c d).IsOdd (gradedKasparovTensorGrading c d)
      (affineKasparovOperator R P t) :=
  (hR.operator_odd.smul (1 - (t : ℂ))).add (hP.operator_odd.smul (t : ℂ))

theorem affineProductOperator_graded_commutator_compact
    (hR : GradedKasparovTensorOperatorConditions c d R)
    (hP : GradedKasparovTensorOperatorConditions c d P) (t : ℝ) (a : A) :
    IsModuleCompact (affineKasparovOperator R P t * gradedKasparovTensorRepresentation c d a -
      gradedKasparovTensorRepresentation c d (δA.automorphism a) * affineKasparovOperator R P t) := by
  have heq : affineKasparovOperator R P t * gradedKasparovTensorRepresentation c d a -
      gradedKasparovTensorRepresentation c d (δA.automorphism a) * affineKasparovOperator R P t =
      (1 - (t : ℂ)) • (R * gradedKasparovTensorRepresentation c d a -
        gradedKasparovTensorRepresentation c d (δA.automorphism a) * R) +
      (t : ℂ) • (P * gradedKasparovTensorRepresentation c d a -
        gradedKasparovTensorRepresentation c d (δA.automorphism a) * P) := by
    simp only [affineKasparovOperator, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
    module
  rw [heq]
  exact ((hR.commutator_compact a).smul _).add ((hP.commutator_compact a).smul _)

theorem affineProductOperator_equivariance_compact
    (hR : GradedKasparovTensorOperatorConditions c d R)
    (hP : GradedKasparovTensorOperatorConditions c d P) (t : ℝ) (g : Γ) (a : A) :
    IsModuleCompact (((gradedKasparovTensorAction c d).conjugateOperator g
        (affineKasparovOperator R P t) - affineKasparovOperator R P t) *
      gradedKasparovTensorRepresentation c d a) := by
  rw [affineKasparovOperator_equivariance_defect]
  exact ((hR.equivariance_mod_compact g a).smul _).add ((hP.equivariance_mod_compact g a).smul _)

/-- The two signed defects interpolate with coefficients summing to one. -/
theorem affineProductOperator_isConnection
    (hdsa : IsSelfAdjoint d.operator) (hRsa : IsSelfAdjoint R) (hPsa : IsSelfAdjoint P)
    (hR : GradedKasparovConnection c d R) (hP : GradedKasparovConnection c d P) (t : ℝ) :
    GradedKasparovConnection c d (affineKasparovOperator R P t) := by
  apply gradedKasparovConnection_of_signed_creation_defects c d hdsa _
    (affineProductOperator_isSelfAdjoint (d := d) hRsa hPsa t)
  intro x
  have heq : (affineKasparovOperator R P t).comp (moduleCreationMap d.representation x) -
      (moduleCreationMap d.representation (c.grading.grading x)).comp d.operator =
      (1 - (t : ℂ)) • (R.comp (moduleCreationMap d.representation x) -
        (moduleCreationMap d.representation (c.grading.grading x)).comp d.operator) +
      (t : ℂ) • (P.comp (moduleCreationMap d.representation x) -
        (moduleCreationMap d.representation (c.grading.grading x)).comp d.operator) := by
    ext y
    simp only [affineKasparovOperator, AdjointableMap.comp_apply,
      AdjointableMap.coe_add_apply, AdjointableMap.coe_sub_apply, AdjointableMap.coe_smul_apply]
    module
  rw [heq]
  exact ((hR.creation_defect x).smul _).add ((hP.creation_defect x).smul _)

/-- The actual source grading cancels when the graded commutator is
applied twice. This provides the ordinary commutator needed for CFC. -/
theorem affineProductOperator_square_commutator_compact
    (hR : GradedKasparovTensorOperatorConditions c d R)
    (hP : GradedKasparovTensorOperatorConditions c d P) (t : ℝ) (a : A) :
    IsModuleCompact ((affineKasparovOperator R P t * affineKasparovOperator R P t) *
      gradedKasparovTensorRepresentation c d a - gradedKasparovTensorRepresentation c d a *
        (affineKasparovOperator R P t * affineKasparovOperator R P t)) := by
  let H := affineKasparovOperator R P t
  let ρ := gradedKasparovTensorRepresentation c d
  have heq : (H * H) * ρ a - ρ a * (H * H) =
      H * (H * ρ a - ρ (δA.automorphism a) * H) +
        (H * ρ (δA.automorphism a) - ρ a * H) * H := by noncomm_ring
  change IsModuleCompact ((H * H) * ρ a - ρ a * (H * H))
  rw [heq]
  have h₁ := affineProductOperator_graded_commutator_compact c d hR hP t a
  have h₂ := affineProductOperator_graded_commutator_compact c d hR hP t (δA.automorphism a)
  simp only [CStarGrading.automorphism_sq] at h₂
  exact IsModuleCompact.add (mul_mem_moduleCompact_left H h₁)
    (mul_mem_moduleCompact_right h₂ H)

/-- Positive comparison supplies the genuine localized lower bound
one half. Both endpoint square errors are compact only after source
localization, which is sufficient for this compression estimate. -/
theorem affineProductOperator_square_lowerBound
    (hR : GradedKasparovTensorOperatorConditions c d R)
    (hP : GradedKasparovTensorOperatorConditions c d P)
    (hpos : ∀ a, IsPositiveModuloModuleCompact (gradedKasparovTensorRepresentation c d a *
      (R * P + P * R) * star (gradedKasparovTensorRepresentation c d a)))
    (t : I) (a : A) :
    IsPositiveModuloModuleCompact (gradedKasparovTensorRepresentation c d a *
      (affineKasparovOperator R P (t : ℝ) * affineKasparovOperator R P (t : ℝ) -
        algebraMap ℝ _ (1 / 2)) * star (gradedKasparovTensorRepresentation c d a)) := by
  let ρ := gradedKasparovTensorRepresentation c d
  let s : ℝ := 1 - (t : ℝ)
  let u : ℝ := (t : ℝ)
  let k : ℝ := s ^ 2 + u ^ 2 - 1 / 2
  have hs : 0 ≤ s := sub_nonneg.mpr t.property.2
  have hu : 0 ≤ u := t.property.1
  have hk : 0 ≤ k := by
    dsimp [k, s, u]
    nlinarith [sq_nonneg ((t : ℝ) - 1 / 2)]
  have hRP : IsPositiveModuloModuleCompact
      (((s * u : ℝ) : ℂ) • (ρ a * (R * P + P * R) * star (ρ a))) :=
    (hpos a).nonneg_real_smul (s * u) (mul_nonneg hs hu)
  have hscalar : 0 ≤ (k : ℂ) • (ρ a * star (ρ a)) := by
    have hroot : (Real.sqrt k : ℂ) * (Real.sqrt k : ℂ) = (k : ℂ) := by
      simpa only [Complex.ofReal_mul] using
        congrArg (fun x : ℝ => (x : ℂ)) (Real.mul_self_sqrt hk)
    have hstar : star (Real.sqrt k : ℂ) = (Real.sqrt k : ℂ) := by simp
    have heq : ((Real.sqrt k : ℂ) • ρ a) * star ((Real.sqrt k : ℂ) • ρ a) =
        (k : ℂ) • (ρ a * star (ρ a)) := by
      rw [star_smul, hstar, smul_mul_assoc, mul_smul_comm, smul_smul, hroot]
    rw [← heq]
    exact mul_star_self_nonneg _
  have hbase := hRP.add (isPositiveModuloModuleCompact_of_nonneg hscalar)
  have hRlocal : IsModuleCompact (ρ a * (R * R - 1) * star (ρ a)) := by
    have h := hR.square_mod_compact (star a)
    rw [map_star] at h
    exact mul_mem_moduleCompact_left (ρ a) h
  have hPlocal : IsModuleCompact (ρ a * (P * P - 1) * star (ρ a)) := by
    have h := hP.square_mod_compact (star a)
    rw [map_star] at h
    exact mul_mem_moduleCompact_left (ρ a) h
  have heq : ρ a * (affineKasparovOperator R P (t : ℝ) *
        affineKasparovOperator R P (t : ℝ) - algebraMap ℝ _ (1 / 2)) * star (ρ a) -
      ((((s * u : ℝ) : ℂ) • (ρ a * (R * P + P * R) * star (ρ a))) +
        (k : ℂ) • (ρ a * star (ρ a))) =
      ((s ^ 2 : ℝ) : ℂ) • (ρ a * (R * R - 1) * star (ρ a)) +
        ((u ^ 2 : ℝ) : ℂ) • (ρ a * (P * P - 1) * star (ρ a)) := by
    dsimp [affineKasparovOperator, k, s, u]
    simp only [Algebra.algebraMap_eq_smul_one, add_mul, mul_add, sub_mul, mul_sub,
      smul_mul_assoc, mul_smul_comm, mul_one, one_mul]
    module
  apply hbase.of_sub_compact
  rw [heq]
  exact (hRlocal.smul _).add (hPlocal.smul _)

end BC4lean.KKTheory
