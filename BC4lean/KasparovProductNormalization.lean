import BC4lean.KasparovProductExistence
import BC4lean.ModuleCompactCFCIntertwining
import BC4lean.ModuleSquareCutoffNormalization

/-! # Actual normalization preserving genuine product connections

Rectangular CFC intertwining proves that the actual localized cycle
normalization preserves all creation connection laws when the second
operator is a selfadjoint contraction. The square intertwining calculation
uses the genuine semilinear first grading twice. No global square defect
or globally compact normalization perturbation is imposed.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

section ContractiveNormalizer
variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

/-- The genuine Fredholm normalizer is exactly one on every actual
contraction, including the zero endomorphism algebra case. -/
theorem globalFredholmNormalizer_eq_one_of_norm_le_one
    (T : AdjointableMap B E F) (hT : ‖T‖ ≤ 1) : globalFredholmNormalizer T = 1 := by
  let _retainedOriginalCompleteF : CompleteSpace F := inferInstance
  have ha : IsSelfAdjoint (T.adjoint.comp T) := by
    change (T.adjoint.comp T).adjoint = T.adjoint.comp T
    rw [AdjointableMap.adjoint_comp, AdjointableMap.adjoint_adjoint]
  have hnorm : ‖T.adjoint.comp T‖ ≤ 1 := by
    change ‖(T.adjoint.comp T).toCLM‖ ≤ 1
    rw [AdjointableMap.norm_toCLM_adjoint_comp_self]
    change ‖T‖ ^ 2 ≤ 1
    nlinarith [norm_nonneg T]
  have hI : ‖(1 : AdjointableMap B E E)‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  have hspec (s : ℝ) (hs : s ∈ spectrum ℝ (T.adjoint.comp T)) : s ≤ 1 :=
    (Real.le_norm_self s).trans ((spectrum.norm_le_norm_mul_of_mem hs).trans
      ((mul_le_mul hnorm hI (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)))
  change cfc fredholmNormWeight (T.adjoint.comp T) = 1
  have heq : cfc fredholmNormWeight (T.adjoint.comp T) =
      cfc (fun _ : ℝ => 1) (T.adjoint.comp T) := by
    apply cfc_congr
    intro s hs
    simp only [fredholmNormWeight, max_eq_left (hspec s hs), Real.sqrt_one, inv_one]
  rw [heq, cfc_const_one ℝ _ ha]

end ContractiveNormalizer

section SignedNormalization
variable {B C E F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F] {δB : CStarGrading B}

/-- The actual signed connection intertwines its square with the actual
second square modulo genuine rectangular compact maps. -/
theorem signedCreationConnection_square_intertwining
    (J : GradedHilbertModule δB E) (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (S : AdjointableMap C F F)
    (R : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ))
    (hR : ∀ x, IsModuleCompact (R.comp (moduleCreationMap φ x) -
      (moduleCreationMap φ (J.grading x)).comp S)) (x : E) :
    IsModuleCompact ((R * R).comp (moduleCreationMap φ x) -
      (moduleCreationMap φ x).comp (S * S)) := by
  let D := fun y : E => R.comp (moduleCreationMap φ y) -
    (moduleCreationMap φ (J.grading y)).comp S
  have heq : (R * R).comp (moduleCreationMap φ x) - (moduleCreationMap φ x).comp (S * S) =
      R.comp (D x) + (D (J.grading x)).comp S := by
    ext y
    simp only [D, AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
      AdjointableMap.coe_add_apply, AdjointableMap.mul_apply, map_sub, J.grading_sq]
    abel
  rw [heq]
  exact ((hR x).comp_left R).add ((hR (J.grading x)).comp_right S)

/-- Genuine rectangular CFC intertwining preserves the signed connection
under actual Fredholm normalization of a selfadjoint operator. -/
theorem signedCreationConnection_globalFredholmNormalization
    (J : GradedHilbertModule δB E) (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (S : AdjointableMap C F F) (hSsa : IsSelfAdjoint S) (hSnorm : ‖S‖ ≤ 1)
    (R : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ))
    (hRsa : IsSelfAdjoint R)
    (hR : ∀ x, IsModuleCompact (R.comp (moduleCreationMap φ x) -
      (moduleCreationMap φ (J.grading x)).comp S)) (x : E) :
    IsModuleCompact ((globalFredholmNormalization R).comp (moduleCreationMap φ x) -
      (moduleCreationMap φ (J.grading x)).comp S) := by
  have hsquare : IsModuleCompact ((R.adjoint.comp R).comp (moduleCreationMap φ x) -
      (moduleCreationMap φ x).comp (S.adjoint.comp S)) := by
    rw [show R.adjoint = R from hRsa.star_eq, show S.adjoint = S from hSsa.star_eq]
    exact signedCreationConnection_square_intertwining J φ S R hR x
  have hR2sa : IsSelfAdjoint (R.adjoint.comp R) := by
    change (R.adjoint.comp R).adjoint = R.adjoint.comp R
    rw [AdjointableMap.adjoint_comp, AdjointableMap.adjoint_adjoint]
  have hS2sa : IsSelfAdjoint (S.adjoint.comp S) := by
    change (S.adjoint.comp S).adjoint = S.adjoint.comp S
    rw [AdjointableMap.adjoint_comp, AdjointableMap.adjoint_adjoint]
  have hcfc := cfc_intertwining_isModuleCompact (R.adjoint.comp R) (S.adjoint.comp S)
    hR2sa hS2sa (moduleCreationMap φ x)
    hsquare fredholmNormWeight continuous_fredholmNormWeight
  change IsModuleCompact ((globalFredholmNormalizer R).comp (moduleCreationMap φ x) -
    (moduleCreationMap φ x).comp (globalFredholmNormalizer S)) at hcfc
  rw [globalFredholmNormalizer_eq_one_of_norm_le_one S hSnorm] at hcfc
  have hcompOne : (moduleCreationMap φ x).comp (1 : AdjointableMap C F F) =
      moduleCreationMap φ x := by
    change (moduleCreationMap φ x).comp AdjointableMap.id = moduleCreationMap φ x
    exact AdjointableMap.comp_id _
  rw [hcompOne] at hcfc
  have heq : (globalFredholmNormalization R).comp (moduleCreationMap φ x) -
      (moduleCreationMap φ (J.grading x)).comp S =
      R.comp ((globalFredholmNormalizer R).comp (moduleCreationMap φ x) - moduleCreationMap φ x) +
        (R.comp (moduleCreationMap φ x) - (moduleCreationMap φ (J.grading x)).comp S) := by
    ext y
    simp only [globalFredholmNormalization, AdjointableMap.comp_apply,
      AdjointableMap.coe_sub_apply, AdjointableMap.coe_add_apply, map_sub]
    abel
  rw [heq]
  exact (hcfc.comp_left R).add (hR x)

end SignedNormalization

section ProductConnectionNormalization
variable {Γ A B C E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}

theorem gradedKasparovConnection_of_signed_creation_defects
    (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F)
    (hdsa : IsSelfAdjoint d.operator)
    (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) (hRsa : IsSelfAdjoint R)
    (hR : ∀ x, IsModuleCompact (R.comp (moduleCreationMap d.representation x) -
      (moduleCreationMap d.representation (c.grading.grading x)).comp d.operator)) :
    GradedKasparovConnection c d R := by
  have heven (x : E) (hx : c.grading.grading x = x) :
      IsModuleCompact ((moduleCreationMap d.representation x).comp d.operator -
        R.comp (moduleCreationMap d.representation x)) := by
    simpa only [hx, neg_sub] using (hR x).neg
  have hodd (x : E) (hx : c.grading.grading x = -x) :
      IsModuleCompact ((moduleCreationMap d.representation x).comp d.operator +
        R.comp (moduleCreationMap d.representation x)) := by
    have h := hR x
    rw [hx, moduleCreationMap_neg] at h
    have heq : R.comp (moduleCreationMap d.representation x) -
        (-moduleCreationMap d.representation x).comp d.operator =
        (moduleCreationMap d.representation x).comp d.operator +
          R.comp (moduleCreationMap d.representation x) := by
      ext y
      simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
        AdjointableMap.coe_add_apply, AdjointableMap.coe_neg_apply]
      abel
    rwa [heq] at h
  exact ⟨heven, fun x hx => by simpa only [hdsa.star_eq, hRsa.star_eq] using heven x hx,
    hodd, fun x hx => by simpa only [hdsa.star_eq, hRsa.star_eq] using hodd x hx⟩

/-- An arbitrary genuine product connection survives the actual localized
cycle normalization when the second cycle is a selfadjoint contraction. -/
theorem normalizedTensorCycle_isConnection
    (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F)
    (hdsa : IsSelfAdjoint d.operator) (hdnorm : ‖d.operator‖ ≤ 1)
    {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)}
    (hc : GradedKasparovTensorOperatorConditions c d R) (hR : GradedKasparovConnection c d R) :
    GradedKasparovConnection c d (gradedKasparovTensorCycleOfConditions c d R hc).normalized.operator := by
  let q := gradedKasparovTensorCycleOfConditions c d R hc
  let Rs := q.symmetrized.operator
  have hDstar (x : E) : IsModuleCompact ((star R).comp (moduleCreationMap d.representation x) -
      (moduleCreationMap d.representation (c.grading.grading x)).comp d.operator) := by
    simpa only [hdsa.star_eq] using hR.creation_adjoint_defect x
  have hD (x : E) : IsModuleCompact (Rs.comp (moduleCreationMap d.representation x) -
      (moduleCreationMap d.representation (c.grading.grading x)).comp d.operator) := by
    have heq : Rs.comp (moduleCreationMap d.representation x) -
        (moduleCreationMap d.representation (c.grading.grading x)).comp d.operator =
        ((2 : ℂ)⁻¹) • ((R.comp (moduleCreationMap d.representation x) -
          (moduleCreationMap d.representation (c.grading.grading x)).comp d.operator) +
            ((star R).comp (moduleCreationMap d.representation x) -
              (moduleCreationMap d.representation (c.grading.grading x)).comp d.operator)) := by
      ext y
      simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
        AdjointableMap.coe_add_apply, AdjointableMap.coe_smul_apply]
      change (R + (2 : ℂ)⁻¹ • (star R - R)) (moduleCreationMap d.representation x y) -
        moduleCreationMap d.representation (c.grading.grading x) (d.operator y) = _
      simp only [AdjointableMap.coe_sub_apply,
        AdjointableMap.coe_add_apply, AdjointableMap.coe_smul_apply]
      norm_num
      module
    rw [heq]
    exact ((hR.creation_defect x).add (hDstar x)).smul _
  apply gradedKasparovConnection_of_signed_creation_defects c d hdsa _ q.normalized_selfadjoint
  exact signedCreationConnection_globalFredholmNormalization c.grading d.representation d.operator
    hdsa hdnorm Rs q.symmetrized_selfadjoint hD

/-- Both actual localized compact perturbation laws suffice to preserve
the original first-operator positivity condition. No first-factor tensor
compactness is inferred from a compact operator on the first module. -/
theorem gradedKasparovProductPositivity_of_localizedPerturbation
    (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F)
    {R R' : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)}
    (hK : ∀ a, IsModuleCompact ((R' - R) * gradedKasparovTensorRepresentation c d a))
    (hKstar : ∀ a, IsModuleCompact (star (R' - R) *
      gradedKasparovTensorRepresentation c d a))
    (hR : ∀ a, IsPositiveModuloModuleCompact
      (gradedKasparovProductPositivityOperator c d R a)) (a : A) :
    IsPositiveModuloModuleCompact (gradedKasparovProductPositivityOperator c d R' a) := by
  let ρ := gradedKasparovTensorRepresentation c d
  let T := interiorModuleTensorOperator d.representation c.operator
  let K := R' - R
  have hright : IsModuleCompact (K * star (ρ a)) := by
    simpa only [ρ, map_star] using hK (star a)
  have hleft : IsModuleCompact (ρ a * K) := by
    have h := (hKstar (star a)).adjoint
    change IsModuleCompact (star (star (R' - R) * ρ (star a))) at h
    simpa only [star_mul, map_star, star_star, K] using h
  have heq : gradedKasparovProductPositivityOperator c d R' a -
      gradedKasparovProductPositivityOperator c d R a =
      (ρ a * T) * (K * star (ρ a)) + (ρ a * K) * (T * star (ρ a)) := by
    dsimp [gradedKasparovProductPositivityOperator, ρ, T, K]
    noncomm_ring
  apply (hR a).of_sub_compact
  rw [heq]
  exact IsModuleCompact.add (mul_mem_moduleCompact_left (ρ a * T) hright)
    (mul_mem_moduleCompact_right hleft (T * star (ρ a)))

/-- An arbitrary actual product normalizes to a selfadjoint contractive
actual product for the same first cycle. The second cycle is required only
to be a selfadjoint contraction; its defects remain coefficient-local. -/
theorem normalizedTensorCycle_isProduct
    (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F)
    (hdsa : IsSelfAdjoint d.operator) (hdnorm : ‖d.operator‖ ≤ 1)
    {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)}
    (hR : IsGradedKasparovProductOperator c d R) :
    IsGradedKasparovProductOperator c d
      (gradedKasparovTensorCycleOfConditions c d R hR.cycleConditions).normalized.operator := by
  let q := gradedKasparovTensorCycleOfConditions c d R hR.cycleConditions
  refine ⟨?_, normalizedTensorCycle_isConnection c d hdsa hdnorm
    hR.cycleConditions hR.connection, ?_⟩
  · exact ⟨q.normalized.operator_odd, q.normalized.selfadjoint_mod_compact,
      q.normalized.square_mod_compact, q.normalized.commutator_compact,
      q.normalized.equivariance_mod_compact⟩
  · exact gradedKasparovProductPositivity_of_localizedPerturbation c d
      q.normalizedOperator_sub_locallyCompact q.normalizedOperator_sub_adjoint_locallyCompact
      hR.positivity

/-- A continuous square cutoff also preserves genuine creation
connections. Its value at one is one, and the second square defect is
localized via the actual coefficient AU rather than globally compact. -/
theorem squareCutoffTensorOperator_isConnection
    (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F)
    (hdsa : IsSelfAdjoint d.operator) {k : ℝ} (hk : 0 < k) (hkone : k ≤ 1)
    {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)}
    (hRsa : IsSelfAdjoint R) (hR : GradedKasparovConnection c d R) :
    GradedKasparovConnection c d (moduleSquareCutoffNormalization k R) := by
  let S := d.operator
  let Q := S.adjoint.comp S
  let K := moduleSquareCutoffNormalizer k S - 1
  have hQsa : IsSelfAdjoint Q := by
    change (S.adjoint.comp S).adjoint = S.adjoint.comp S
    rw [AdjointableMap.adjoint_comp, AdjointableMap.adjoint_adjoint]
  have hK (b : B) : IsModuleCompact (K * d.representation b) := by
    have hlocal : IsModuleCompact ((Q - algebraMap ℝ _ 1) * d.representation b) := by
      rw [map_one]
      change IsModuleCompact ((star S * S - 1) * d.representation b)
      rw [hdsa.star_eq]
      exact d.square_mod_compact b
    have h := cfc_sub_value_mul_isModuleCompact Q (d.representation b) hQsa 1 hlocal
      (moduleSquareCutoffWeight k) (continuous_moduleSquareCutoffWeight hk)
    simpa only [moduleSquareCutoffWeight_one hkone, map_one, K, moduleSquareCutoffNormalizer, Q] using h
  have hKsa : IsSelfAdjoint K := by
    change star (moduleSquareCutoffNormalizer k S - 1) = moduleSquareCutoffNormalizer k S - 1
    rw [star_sub, star_one, show star (moduleSquareCutoffNormalizer k S) =
      moduleSquareCutoffNormalizer k S from moduleSquareCutoffNormalizer_adjoint k S]
  apply gradedKasparovConnection_of_signed_creation_defects c d hdsa _
    (moduleSquareCutoffNormalization_selfadjoint k R hRsa)
  intro x
  have hθK : IsModuleCompact ((moduleCreationMap d.representation x).comp K) :=
    moduleCreationMap_comp_isModuleCompact_of_local d.representation x K hK
      (fun b => by simpa only [hKsa.star_eq] using hK b)
  have hsq : IsModuleCompact ((R.adjoint.comp R).comp (moduleCreationMap d.representation x) -
      (moduleCreationMap d.representation x).comp Q) := by
    change IsModuleCompact ((star R * R).comp (moduleCreationMap d.representation x) -
      (moduleCreationMap d.representation x).comp (star S * S))
    rw [hRsa.star_eq, hdsa.star_eq]
    exact signedCreationConnection_square_intertwining c.grading d.representation S R hR.creation_defect x
  have hR2sa : IsSelfAdjoint (R.adjoint.comp R) := by
    change (R.adjoint.comp R).adjoint = R.adjoint.comp R
    rw [AdjointableMap.adjoint_comp, AdjointableMap.adjoint_adjoint]
  have hcfc := cfc_intertwining_isModuleCompact (R.adjoint.comp R) Q
    hR2sa hQsa
    (moduleCreationMap d.representation x) hsq (moduleSquareCutoffWeight k)
      (continuous_moduleSquareCutoffWeight hk)
  have hnormal : IsModuleCompact ((moduleSquareCutoffNormalizer k R).comp
      (moduleCreationMap d.representation x) - moduleCreationMap d.representation x) := by
    have heq : (moduleSquareCutoffNormalizer k R).comp (moduleCreationMap d.representation x) -
        moduleCreationMap d.representation x =
        ((moduleSquareCutoffNormalizer k R).comp (moduleCreationMap d.representation x) -
          (moduleCreationMap d.representation x).comp (moduleSquareCutoffNormalizer k S)) +
        (moduleCreationMap d.representation x).comp K := by
      ext y
      simp only [K, AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
        AdjointableMap.coe_add_apply, AdjointableMap.one_apply, map_sub]
      abel
    rw [heq]
    exact hcfc.add hθK
  have heq : (moduleSquareCutoffNormalization k R).comp (moduleCreationMap d.representation x) -
      (moduleCreationMap d.representation (c.grading.grading x)).comp S =
      R.comp ((moduleSquareCutoffNormalizer k R).comp (moduleCreationMap d.representation x) -
        moduleCreationMap d.representation x) +
      (R.comp (moduleCreationMap d.representation x) -
        (moduleCreationMap d.representation (c.grading.grading x)).comp S) := by
    ext y
    simp only [moduleSquareCutoffNormalization, AdjointableMap.comp_apply,
      AdjointableMap.coe_sub_apply, AdjointableMap.coe_add_apply, map_sub]
    abel
  rw [heq]
  exact (hnormal.comp_left R).add (hR.creation_defect x)

/-- The coefficient-AU compact differences transfer all four laws in the
other direction as well. The first operator is irrelevant to these four
analytic connection fields, and its genuine grading is retained. -/
theorem gradedKasparovConnection_normalized_second
    (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F)
    {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)}
    (hR : GradedKasparovConnection c d R) : GradedKasparovConnection c d.normalized R := by
  let K := d.normalizedOperator - d.operator
  have hK (x : E) : IsModuleCompact ((moduleCreationMap d.representation x).comp K) :=
    moduleCreationMap_comp_isModuleCompact_of_local d.representation x K
      d.normalizedOperator_sub_locallyCompact d.normalizedOperator_sub_adjoint_locallyCompact
  have hKstar (x : E) : IsModuleCompact ((moduleCreationMap d.representation x).comp (star K)) :=
    moduleCreationMap_comp_isModuleCompact_of_local d.representation x (star K)
      d.normalizedOperator_sub_adjoint_locallyCompact
      (fun b => by simpa only [star_star] using d.normalizedOperator_sub_locallyCompact b)
  constructor
  · intro x hx
    change IsModuleCompact ((moduleCreationMap d.representation x).comp d.normalizedOperator -
      R.comp (moduleCreationMap d.representation x))
    have heq : (moduleCreationMap d.representation x).comp d.normalizedOperator -
        R.comp (moduleCreationMap d.representation x) =
        ((moduleCreationMap d.representation x).comp d.operator -
          R.comp (moduleCreationMap d.representation x)) + (moduleCreationMap d.representation x).comp K := by
      ext y
      simp only [K, AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
        AdjointableMap.coe_add_apply, map_sub]
      abel
    rw [heq]
    exact (hR.even x hx).add (hK x)
  · intro x hx
    change IsModuleCompact ((moduleCreationMap d.representation x).comp (star d.normalizedOperator) -
      (star R).comp (moduleCreationMap d.representation x))
    have heq : (moduleCreationMap d.representation x).comp (star d.normalizedOperator) -
        (star R).comp (moduleCreationMap d.representation x) =
        ((moduleCreationMap d.representation x).comp (star d.operator) -
          (star R).comp (moduleCreationMap d.representation x)) +
          (moduleCreationMap d.representation x).comp (star K) := by
      rw [show star K = star d.normalizedOperator - star d.operator from star_sub _ _]
      ext y
      simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
        AdjointableMap.coe_add_apply, map_sub]
      abel
    rw [heq]
    exact (hR.even_adjoint x hx).add (hKstar x)
  · intro x hx
    change IsModuleCompact ((moduleCreationMap d.representation x).comp d.normalizedOperator +
      R.comp (moduleCreationMap d.representation x))
    have heq : (moduleCreationMap d.representation x).comp d.normalizedOperator +
        R.comp (moduleCreationMap d.representation x) =
        ((moduleCreationMap d.representation x).comp d.operator +
          R.comp (moduleCreationMap d.representation x)) + (moduleCreationMap d.representation x).comp K := by
      ext y
      simp only [K, AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
        AdjointableMap.coe_add_apply, map_sub]
      abel
    rw [heq]
    exact (hR.odd x hx).add (hK x)
  · intro x hx
    change IsModuleCompact ((moduleCreationMap d.representation x).comp (star d.normalizedOperator) +
      (star R).comp (moduleCreationMap d.representation x))
    have heq : (moduleCreationMap d.representation x).comp (star d.normalizedOperator) +
        (star R).comp (moduleCreationMap d.representation x) =
        ((moduleCreationMap d.representation x).comp (star d.operator) +
          (star R).comp (moduleCreationMap d.representation x)) +
          (moduleCreationMap d.representation x).comp (star K) := by
      rw [show star K = star d.normalizedOperator - star d.operator from star_sub _ _]
      ext y
      simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
        AdjointableMap.coe_add_apply, map_sub]
      abel
    rw [heq]
    exact (hR.odd_adjoint x hx).add (hKstar x)

theorem gradedKasparovConnection_iff_normalized_second
    (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F)
    (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) :
    GradedKasparovConnection c d R ↔ GradedKasparovConnection c d.normalized R :=
  ⟨gradedKasparovConnection_normalized_second c d,
    gradedKasparovConnection_of_normalized_second c d⟩

/-- Normalizing the second input preserves the actual product criterion
for the same tensor operator, representation, grading and action. -/
theorem isGradedKasparovProductOperator_iff_normalized_second
    (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F)
    (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) :
    IsGradedKasparovProductOperator c d R ↔ IsGradedKasparovProductOperator c d.normalized R := by
  constructor
  · intro h
    have hc : GradedKasparovTensorOperatorConditions c d.normalized R :=
      ⟨h.cycleConditions.operator_odd, h.cycleConditions.selfadjoint_mod_compact,
        h.cycleConditions.square_mod_compact, h.cycleConditions.commutator_compact,
        h.cycleConditions.equivariance_mod_compact⟩
    exact ⟨hc, gradedKasparovConnection_normalized_second c d h.connection, h.positivity⟩
  · intro h
    have hc : GradedKasparovTensorOperatorConditions c d R :=
      ⟨h.cycleConditions.operator_odd, h.cycleConditions.selfadjoint_mod_compact,
        h.cycleConditions.square_mod_compact, h.cycleConditions.commutator_compact,
        h.cycleConditions.equivariance_mod_compact⟩
    exact ⟨hc, gradedKasparovConnection_of_normalized_second c d h.connection, h.positivity⟩

end ProductConnectionNormalization
end BC4lean.KKTheory
