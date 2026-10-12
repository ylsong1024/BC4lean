import BC4lean.KasparovComparisonPositivity
import BC4lean.EssentialModuleSpectrumCutoff

/-! # Actual weighted comparisons for the common triple operator

The first comparison need only have a positive lift modulo the first technical
algebra: its compact error may have been tensored and need not be compact on
the triple module. The first weight makes that actual error compact. The second
comparison uses the genuine residual H−H⁺ in the second technical algebra;
the second weight has an actual positive lift against H⁺. Together these prove
the common operator's localized comparison without assuming it is a cycle.
-/

noncomputable section
namespace BC4lean.KKTheory

section WeightedLift
variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

local instance kasparovTripleWeightedComparisonLocalInstance1 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance kasparovTripleWeightedComparisonLocalInstance2 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _

/-- Weighting an actual positive lift whose error lies in the first
technical algebra produces positivity modulo genuine module compacts. -/
theorem weighted_positive_of_lift_mod_firstAlgebra
    (m H P : AdjointableMap B E E)
    (E₁ : NonUnitalStarSubalgebra ℂ (AdjointableMap B E E))
    (hm : 0 ≤ m) (hmnorm : ‖m‖ ≤ 1) (hP : 0 ≤ P) (hHP : H - P ∈ E₁)
    (hideal : ∀ T ∈ E₁, IsModuleCompact (m * T))
    (hcomm : IsModuleCompact (m * H - H * m)) :
    IsPositiveModuloModuleCompact (m * H) := by
  have hmHP := hideal _ hHP
  have hHPm : IsModuleCompact ((H - P) * m) := by
    have h := (hideal _ (E₁.star_mem' hHP)).adjoint
    change IsModuleCompact (star (m * star (H - P))) at h
    simpa only [star_mul, star_star, hm.isSelfAdjoint.star_eq] using h
  have hmP : IsModuleCompact (m * P - P * m) := by
    have heq : m * P - P * m = (m * H - H * m) - m * (H - P) + (H - P) * m := by
      noncomm_ring
    rw [heq]
    exact (hcomm.sub hmHP).add hHPm
  have hbase := (isPositiveModuloModuleCompact_of_nonneg hP).positive_weight hm hmnorm hmP
  apply hbase.of_sub_compact
  simpa only [mul_sub] using hmHP

end WeightedLift

section CommonComparison
variable {Γ A B C E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}
  (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F)
  {G R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation)}
  {E₁ E₂ : NonUnitalStarSubalgebra ℂ
    (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation))}
  {Δ : Set (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation))}
  {f : ℕ → AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation)}

local instance kasparovTripleWeightedComparisonLocalInstance3 : PartialOrder (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation)) := CStarAlgebra.spectralOrder _
local instance kasparovTripleWeightedComparisonLocalInstance4 : StarOrderedRing (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation)) := CStarAlgebra.spectralOrderedRing _

/-- The exact positive-part residual, rather than the scalar comparison
defect H−2, gives the common triple operator's second comparison. -/
theorem weightedTechnicalProduct_comparison_positive_of_posPart_residual
    (h : KasparovProductTechnicalInputs c d G E₁ E₂ Δ)
    (p : KasparovTechnicalPartition (gradedKasparovTensorGrading c d)
      (gradedKasparovTensorAction c d) E₁ E₂ Δ f)
    (hRΔ : R ∈ Δ) (hRsa : IsSelfAdjoint R) (hGsa : IsSelfAdjoint G)
    (hresidual : R * G + G * R - (R * G + G * R)⁺ ∈ E₂)
    (hweighted : ∀ a, IsPositiveModuloModuleCompact
      (p.m * gradedKasparovProductPositivityOperator c d R a)) (a : A) :
    IsPositiveModuloModuleCompact (gradedKasparovTensorRepresentation c d a *
      (R * kasparovTechnicalProductOperator G p + kasparovTechnicalProductOperator G p * R) *
      star (gradedKasparovTensorRepresentation c d a)) := by
  let ρ := gradedKasparovTensorRepresentation c d
  let Q := interiorModuleTensorOperator d.representation c.operator
  let firstAnti := Q * R + R * Q
  let secondAnti := R * G + G * R
  have hSA : IsSelfAdjoint secondAnti := by
    change star (_ + _) = _
    simp only [star_add, star_mul, hRsa.star_eq, hGsa.star_eq]
    exact add_comm _ _
  have hmρ := p.commutator_m (ρ a) (h.representation_mem a)
  have hmR := p.commutator_m R hRΔ
  have hnR := p.commutator_n R hRΔ
  have hnG := p.commutator_n G h.connection_mem
  have hnAnti : IsModuleCompact (p.n * secondAnti - secondAnti * p.n) := by
    have heq : p.n * secondAnti - secondAnti * p.n =
        (p.n * (R * G) - (R * G) * p.n) + (p.n * (G * R) - (G * R) * p.n) := by
      dsimp only [secondAnti]
      noncomm_ring
    rw [heq]
    exact (moduleCompact_commutator_mul hnR hnG).add (moduleCompact_commutator_mul hnG hnR)
  have hreverse : IsModuleCompact (secondAnti * p.n - p.n * secondAnti) := by
    simpa only [neg_sub] using hnAnti.neg
  have hpartComm := cfc_commutator_isModuleCompact secondAnti p.n hSA hreverse
    (fun s : ℝ => max s 0) (continuous_id.max continuous_const)
  have hpart : cfc (fun s : ℝ => max s 0) secondAnti = secondAnti⁺ := by
    rw [CFC.posPart_def, cfcₙ_eq_cfc]
    simp only [_root_.posPart_def]
  rw [hpart] at hpartComm
  have hnPart : IsModuleCompact (p.n * secondAnti⁺ - secondAnti⁺ * p.n) := by
    simpa only [neg_sub] using hpartComm.neg
  have hsecond := (isPositiveModuloModuleCompact_of_nonneg (CFC.posPart_nonneg secondAnti)).positive_weight
    p.n_nonneg p.n_norm_le_one hnPart
  have hbase := (hweighted a).add (hsecond.star_right_conjugate (ρ a))
  have hdefect := p.second_ideal (secondAnti - secondAnti⁺) hresidual
  have heq : ρ a * (R * kasparovTechnicalProductOperator G p + kasparovTechnicalProductOperator G p * R) *
      star (ρ a) - (p.m * (ρ a * firstAnti * star (ρ a)) + ρ a * (p.n * secondAnti⁺) * star (ρ a)) =
      -(p.m * ρ a - ρ a * p.m) * firstAnti * star (ρ a) +
      ρ a * (p.n * (secondAnti - secondAnti⁺)) * star (ρ a) -
      ρ a * (p.m * R - R * p.m) * Q * star (ρ a) -
      ρ a * (p.n * R - R * p.n) * G * star (ρ a) := by
    dsimp only [kasparovTechnicalProductOperator, Q, firstAnti, secondAnti]
    noncomm_ring
  apply hbase.of_sub_compact
  change IsModuleCompact (ρ a *
    (R * kasparovTechnicalProductOperator G p + kasparovTechnicalProductOperator G p * R) *
      star (ρ a) -
    (p.m * (ρ a * firstAnti * star (ρ a)) + ρ a * (p.n * secondAnti⁺) * star (ρ a)))
  rw [heq]
  exact IsModuleCompact.sub
    (IsModuleCompact.sub
      (IsModuleCompact.add
        (mul_mem_moduleCompact_right (mul_mem_moduleCompact_right hmρ.neg firstAnti) (star (ρ a)))
        (mul_mem_moduleCompact_right (mul_mem_moduleCompact_left (ρ a) hdefect) (star (ρ a))))
      (mul_mem_moduleCompact_right (mul_mem_moduleCompact_right
        (mul_mem_moduleCompact_left (ρ a) hmR) Q) (star (ρ a))))
    (mul_mem_moduleCompact_right (mul_mem_moduleCompact_right
      (mul_mem_moduleCompact_left (ρ a) hnR) G) (star (ρ a)))

end CommonComparison
end BC4lean.KKTheory
