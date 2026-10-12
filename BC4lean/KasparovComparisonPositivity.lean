import BC4lean.KasparovProductUniquenessPreparation
import BC4lean.KasparovSquareRootCompactControls

/-! # Actual positive lifts for weighted product comparisons

A positive contractive weight commuting modulo the genuine compact ideal
preserves positivity modulo that ideal. The positive lift is an actual
square-root compression. This gives the positivity estimate needed to
compare genuine product operators with a constructed technical product.
-/

noncomputable section
namespace BC4lean.KKTheory

section PositiveWeight
variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [comparisonComplete : CompleteSpace E]

local instance kasparovComparisonPositivityLocalInstance1 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance kasparovComparisonPositivityLocalInstance2 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _

/-- A nonnegative real multiple preserves an actual positive lift. -/
theorem IsPositiveModuloModuleCompact.nonneg_real_smul
    {H : AdjointableMap B E E} (hH : IsPositiveModuloModuleCompact H)
    (r : ℝ) (hr : 0 ≤ r) : IsPositiveModuloModuleCompact ((r : ℂ) • H) := by
  obtain ⟨V, hV⟩ := hH.exists_star_square
  apply (isPositiveModuloModuleCompact_iff_star_square _).mpr
  refine ⟨(Real.sqrt r : ℂ) • V, ?_⟩
  have hs : star (Real.sqrt r : ℂ) = (Real.sqrt r : ℂ) := by simp
  have hsq : (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = (r : ℂ) := by
    simpa only [Complex.ofReal_mul] using
      congrArg (fun x : ℝ => (x : ℂ)) (Real.mul_self_sqrt hr)
  have heq : star ((Real.sqrt r : ℂ) • V) * ((Real.sqrt r : ℂ) • V) =
      (r : ℂ) • (star V * V) := by
    rw [star_smul, hs, smul_mul_assoc, mul_smul_comm, smul_smul, hsq]
  rw [heq, ← smul_sub]
  exact hV.smul (r : ℂ)

/-- Localized compact perturbations preserve comparison positivity for
any actual bounded comparison operator. -/
theorem localizedAnticommutator_positive_of_sub_compact
    (X T R R' : AdjointableMap B E E)
    (hKright : IsModuleCompact ((R' - R) * star X))
    (hKleft : IsModuleCompact (X * (R' - R)))
    (hpos : IsPositiveModuloModuleCompact (X * (T * R + R * T) * star X)) :
    IsPositiveModuloModuleCompact (X * (T * R' + R' * T) * star X) := by
  have heq : X * (T * R' + R' * T) * star X -
      X * (T * R + R * T) * star X =
      (X * T) * ((R' - R) * star X) + (X * (R' - R)) * (T * star X) := by
    noncomm_ring
  apply hpos.of_sub_compact
  rw [heq]
  exact IsModuleCompact.add (mul_mem_moduleCompact_left (X * T) hKright)
    (mul_mem_moduleCompact_right hKleft (T * star X))

/-- The actual square-root compression is a positive lift for a positive
weight times a positive-mod-compact operator. -/
theorem IsPositiveModuloModuleCompact.positive_weight
    {M H : AdjointableMap B E E} (hH : IsPositiveModuloModuleCompact H)
    (hM : 0 ≤ M) (hMnorm : ‖M‖ ≤ 1)
    (hcomm : IsModuleCompact (M * H - H * M)) :
    IsPositiveModuloModuleCompact (M * H) := by
  have hsqrt := hcomm.sqrt_commutator hM hMnorm
  have hpos := hH.star_right_conjugate (CFC.sqrt M)
  have heq : M * H - CFC.sqrt M * H * star (CFC.sqrt M) =
      CFC.sqrt M * (CFC.sqrt M * H - H * CFC.sqrt M) := by
    rw [(CFC.sqrt_nonneg M).isSelfAdjoint.star_eq]
    calc
      _ = (CFC.sqrt M * CFC.sqrt M) * H - CFC.sqrt M * H * CFC.sqrt M := by
        rw [CFC.sqrt_mul_sqrt_self M hM]
      _ = _ := by noncomm_ring
  apply hpos.of_sub_compact
  rw [heq]
  exact mul_mem_moduleCompact_left (CFC.sqrt M) hsqrt

omit comparisonComplete in
/-- Actual compact commutators form a derivation on products. -/
theorem moduleCompact_commutator_mul [CompleteSpace E] {M X Y : AdjointableMap B E E}
    (hX : IsModuleCompact (M * X - X * M))
    (hY : IsModuleCompact (M * Y - Y * M)) :
    IsModuleCompact (M * (X * Y) - (X * Y) * M) := by
  have heq : M * (X * Y) - (X * Y) * M =
      (M * X - X * M) * Y + X * (M * Y - Y * M) := by noncomm_ring
  rw [heq]
  exact IsModuleCompact.add (mul_mem_moduleCompact_right hX Y)
    (mul_mem_moduleCompact_left X hY)

end PositiveWeight

section WeightedComparison
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
  {G R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation)}
  {E₁ E₂ : NonUnitalStarSubalgebra ℂ
    (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation))}
  {Δ : Set (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation))}
  {f : ℕ → AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation)}

local instance kasparovComparisonPositivityLocalInstance3 : PartialOrder
    (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) := CStarAlgebra.spectralOrder _
local instance kasparovComparisonPositivityLocalInstance4 : StarOrderedRing
    (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) := CStarAlgebra.spectralOrderedRing _

/-- A genuine technical partition with the actual comparison defect in
its second algebra produces the localized positive comparison required
for the path construction. This is a lemma about an explicit partition,
not a replacement for constructing that partition. -/
theorem weightedTechnicalProduct_comparison_positive
    (h : KasparovProductTechnicalInputs c d G E₁ E₂ Δ)
    (p : KasparovTechnicalPartition (gradedKasparovTensorGrading c d)
      (gradedKasparovTensorAction c d) E₁ E₂ Δ f)
    (hRΔ : R ∈ Δ) (hRG : R * G + G * R - 2 ∈ E₂)
    (hRpos : ∀ a, IsPositiveModuloModuleCompact
      (gradedKasparovProductPositivityOperator c d R a)) (a : A) :
    IsPositiveModuloModuleCompact (gradedKasparovTensorRepresentation c d a *
      (R * kasparovTechnicalProductOperator G p +
        kasparovTechnicalProductOperator G p * R) *
      star (gradedKasparovTensorRepresentation c d a)) := by
  let ρ := gradedKasparovTensorRepresentation c d
  let Q := interiorModuleTensorOperator d.representation c.operator
  let H := Q * R + R * Q
  have hmR := p.commutator_m R hRΔ
  have hnR := p.commutator_n R hRΔ
  have hmQ := p.commutator_m Q h.first_mem
  have hmρ := p.commutator_m (ρ a) (h.representation_mem a)
  have hmρstar : IsModuleCompact (p.m * star (ρ a) - star (ρ a) * p.m) := by
    simpa only [ρ, map_star] using p.commutator_m (ρ (star a)) (h.representation_mem (star a))
  have hmH : IsModuleCompact (p.m * H - H * p.m) := by
    have heq : p.m * H - H * p.m =
        (p.m * (Q * R) - (Q * R) * p.m) +
          (p.m * (R * Q) - (R * Q) * p.m) := by dsimp [H]; noncomm_ring
    rw [heq]
    exact IsModuleCompact.add (moduleCompact_commutator_mul hmQ hmR)
      (moduleCompact_commutator_mul hmR hmQ)
  have hmHloc := moduleCompact_commutator_mul
    (moduleCompact_commutator_mul hmρ hmH) hmρstar
  have hweighted : IsPositiveModuloModuleCompact (p.m * (ρ a * H * star (ρ a))) :=
    (hRpos a).positive_weight p.m_nonneg p.m_norm_le_one hmHloc
  have hnpos : 0 ≤ ρ a * p.n * star (ρ a) :=
    star_right_conjugate_nonneg p.n_nonneg (ρ a)
  have hbase := hweighted.add ((isPositiveModuloModuleCompact_of_nonneg hnpos).add
    (isPositiveModuloModuleCompact_of_nonneg hnpos))
  have hdefect := p.second_ideal (R * G + G * R - 2) hRG
  have heq : ρ a * (R * kasparovTechnicalProductOperator G p +
        kasparovTechnicalProductOperator G p * R) * star (ρ a) -
      (p.m * (ρ a * H * star (ρ a)) +
        (ρ a * p.n * star (ρ a) + ρ a * p.n * star (ρ a))) =
      -(p.m * ρ a - ρ a * p.m) * H * star (ρ a) +
      ρ a * (p.n * (R * G + G * R - 2)) * star (ρ a) -
      ρ a * (p.m * R - R * p.m) * Q * star (ρ a) -
      ρ a * (p.n * R - R * p.n) * G * star (ρ a) := by
    dsimp [kasparovTechnicalProductOperator, H, Q]
    noncomm_ring
  apply hbase.of_sub_compact
  rw [heq]
  exact IsModuleCompact.sub
    (IsModuleCompact.sub
      (IsModuleCompact.add
        (mul_mem_moduleCompact_right (mul_mem_moduleCompact_right hmρ.neg H) (star (ρ a)))
        (mul_mem_moduleCompact_right (mul_mem_moduleCompact_left (ρ a) hdefect) (star (ρ a))))
      (mul_mem_moduleCompact_right
        (mul_mem_moduleCompact_right (mul_mem_moduleCompact_left (ρ a) hmR) Q) (star (ρ a))))
    (mul_mem_moduleCompact_right
      (mul_mem_moduleCompact_right (mul_mem_moduleCompact_left (ρ a) hnR) G) (star (ρ a)))

/-- The final comparison algebra calculation uses only positivity of the
weighted first comparison, rather than positivity before weighting. This
allows the original first operator to be retained through normalization. -/
theorem weightedTechnicalProduct_comparison_positive_of_weighted_first
    (h : KasparovProductTechnicalInputs c d G E₁ E₂ Δ)
    (p : KasparovTechnicalPartition (gradedKasparovTensorGrading c d)
      (gradedKasparovTensorAction c d) E₁ E₂ Δ f)
    (hRΔ : R ∈ Δ) (hRG : R * G + G * R - 2 ∈ E₂)
    (hweighted : ∀ a, IsPositiveModuloModuleCompact
      (p.m * gradedKasparovProductPositivityOperator c d R a)) (a : A) :
    IsPositiveModuloModuleCompact (gradedKasparovTensorRepresentation c d a *
      (R * kasparovTechnicalProductOperator G p + kasparovTechnicalProductOperator G p * R) *
      star (gradedKasparovTensorRepresentation c d a)) := by
  let ρ := gradedKasparovTensorRepresentation c d
  let Q := interiorModuleTensorOperator d.representation c.operator
  let H := Q * R + R * Q
  have hmρ := p.commutator_m (ρ a) (h.representation_mem a)
  have hmR := p.commutator_m R hRΔ
  have hnR := p.commutator_n R hRΔ
  have hnpos : 0 ≤ ρ a * p.n * star (ρ a) :=
    star_right_conjugate_nonneg p.n_nonneg (ρ a)
  have hbase := (hweighted a).add ((isPositiveModuloModuleCompact_of_nonneg hnpos).add
    (isPositiveModuloModuleCompact_of_nonneg hnpos))
  have hdefect := p.second_ideal (R * G + G * R - 2) hRG
  have heq : ρ a * (R * kasparovTechnicalProductOperator G p +
        kasparovTechnicalProductOperator G p * R) * star (ρ a) -
      (p.m * (ρ a * H * star (ρ a)) +
        (ρ a * p.n * star (ρ a) + ρ a * p.n * star (ρ a))) =
      -(p.m * ρ a - ρ a * p.m) * H * star (ρ a) +
      ρ a * (p.n * (R * G + G * R - 2)) * star (ρ a) -
      ρ a * (p.m * R - R * p.m) * Q * star (ρ a) -
      ρ a * (p.n * R - R * p.n) * G * star (ρ a) := by
    dsimp [kasparovTechnicalProductOperator, H, Q]
    noncomm_ring
  apply hbase.of_sub_compact
  change IsModuleCompact (ρ a * (R * kasparovTechnicalProductOperator G p +
      kasparovTechnicalProductOperator G p * R) * star (ρ a) -
    (p.m * (ρ a * H * star (ρ a)) +
      (ρ a * p.n * star (ρ a) + ρ a * p.n * star (ρ a))))
  rw [heq]
  exact IsModuleCompact.sub
    (IsModuleCompact.sub
      (IsModuleCompact.add
        (mul_mem_moduleCompact_right (mul_mem_moduleCompact_right hmρ.neg H) (star (ρ a)))
        (mul_mem_moduleCompact_right (mul_mem_moduleCompact_left (ρ a) hdefect) (star (ρ a))))
      (mul_mem_moduleCompact_right
        (mul_mem_moduleCompact_right (mul_mem_moduleCompact_left (ρ a) hmR) Q) (star (ρ a))))
    (mul_mem_moduleCompact_right
      (mul_mem_moduleCompact_right (mul_mem_moduleCompact_left (ρ a) hnR) G) (star (ρ a)))

/-- The normalization error of the original first operator lies in the
first technical algebra only after source localization. The genuine
connection normalizer law and the graded source commutator make its
weighted comparison error compact, without tensoring it into compacts. -/
theorem weightedTechnicalProduct_comparison_positive_of_firstReplacement
    (h : KasparovProductTechnicalInputs c d G E₁ E₂ Δ)
    (p : KasparovTechnicalPartition (gradedKasparovTensorGrading c d)
      (gradedKasparovTensorAction c d) E₁ E₂ Δ f)
    (hRΔ : R ∈ Δ) (hRG : R * G + G * R - 2 ∈ E₂)
    (hRcycle : GradedKasparovTensorOperatorConditions c d R)
    (hRnormal : ∀ b ∈ E₁, R * b - b * R ∈ E₁)
    (O : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) (hOΔ : O ∈ Δ)
    (hK : ∀ b, (O - interiorModuleTensorOperator d.representation c.operator) *
      gradedKasparovTensorRepresentation c d b ∈ E₁)
    (hRpos : ∀ a, IsPositiveModuloModuleCompact (gradedKasparovTensorRepresentation c d a *
      (O * R + R * O) * star (gradedKasparovTensorRepresentation c d a))) (a : A) :
    IsPositiveModuloModuleCompact (gradedKasparovTensorRepresentation c d a *
      (R * kasparovTechnicalProductOperator G p + kasparovTechnicalProductOperator G p * R) *
      star (gradedKasparovTensorRepresentation c d a)) := by
  let ρ := gradedKasparovTensorRepresentation c d
  let Q := interiorModuleTensorOperator d.representation c.operator
  let K := O - Q
  have hweighted (b : A) : IsPositiveModuloModuleCompact
      (p.m * gradedKasparovProductPositivityOperator c d R b) := by
    let H := O * R + R * O
    have hmO := p.commutator_m O hOΔ
    have hmR := p.commutator_m R hRΔ
    have hmρ := p.commutator_m (ρ b) (h.representation_mem b)
    have hmρstar : IsModuleCompact (p.m * star (ρ b) - star (ρ b) * p.m) := by
      simpa only [ρ, map_star] using p.commutator_m (ρ (star b)) (h.representation_mem (star b))
    have hmH : IsModuleCompact (p.m * H - H * p.m) := by
      have heq : p.m * H - H * p.m =
          (p.m * (O * R) - (O * R) * p.m) + (p.m * (R * O) - (R * O) * p.m) := by
        dsimp [H]
        noncomm_ring
      rw [heq]
      exact IsModuleCompact.add (moduleCompact_commutator_mul hmO hmR)
        (moduleCompact_commutator_mul hmR hmO)
    have hbase := (hRpos b).positive_weight p.m_nonneg p.m_norm_le_one
      (moduleCompact_commutator_mul (moduleCompact_commutator_mul hmρ hmH) hmρstar)
    have hmK (z : A) : IsModuleCompact (p.m * (K * ρ z)) := p.first_ideal _ (hK z)
    have hmKR : IsModuleCompact (p.m * K * R * star (ρ b)) := by
      have hcomm := hRcycle.commutator_compact (star b)
      rw [map_star] at hcomm
      have heq : p.m * K * R * star (ρ b) =
          (p.m * K) * (R * star (ρ b) - ρ (δA.automorphism (star b)) * R) +
            (p.m * (K * ρ (δA.automorphism (star b)))) * R := by noncomm_ring
      rw [heq]
      exact IsModuleCompact.add (mul_mem_moduleCompact_left (p.m * K) hcomm)
        (mul_mem_moduleCompact_right (hmK (δA.automorphism (star b))) R)
    have hmRK : IsModuleCompact (p.m * R * K * star (ρ b)) := by
      have hnormal := p.first_ideal _ (hRnormal (K * ρ (star b)) (hK (star b)))
      have hmKstar := hmK (star b)
      rw [map_star] at hnormal hmKstar
      have heq : p.m * R * K * star (ρ b) =
          p.m * (R * (K * star (ρ b)) - (K * star (ρ b)) * R) +
            (p.m * (K * star (ρ b))) * R := by noncomm_ring
      rw [heq]
      exact IsModuleCompact.add hnormal (mul_mem_moduleCompact_right hmKstar R)
    have herror : IsModuleCompact (p.m * (ρ b * (K * R + R * K) * star (ρ b))) := by
      have heq : p.m * (ρ b * (K * R + R * K) * star (ρ b)) =
          (p.m * ρ b - ρ b * p.m) * (K * R + R * K) * star (ρ b) +
            ρ b * (p.m * K * R * star (ρ b)) + ρ b * (p.m * R * K * star (ρ b)) := by
        noncomm_ring
      rw [heq]
      exact IsModuleCompact.add
        (IsModuleCompact.add (mul_mem_moduleCompact_right
          (mul_mem_moduleCompact_right hmρ (K * R + R * K)) (star (ρ b)))
          (mul_mem_moduleCompact_left (ρ b) hmKR))
        (mul_mem_moduleCompact_left (ρ b) hmRK)
    have heq : p.m * gradedKasparovProductPositivityOperator c d R b -
        p.m * (ρ b * H * star (ρ b)) =
        -(p.m * (ρ b * (K * R + R * K) * star (ρ b))) := by
      dsimp [gradedKasparovProductPositivityOperator, ρ, H, K, Q]
      noncomm_ring
    apply hbase.of_sub_compact
    rw [heq]
    exact herror.neg
  exact weightedTechnicalProduct_comparison_positive_of_weighted_first c d h p hRΔ hRG hweighted a

end WeightedComparison
end BC4lean.KKTheory
