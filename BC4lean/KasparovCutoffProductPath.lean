import BC4lean.KasparovConvexProductPath
import BC4lean.EssentialModuleSquareCutoffNormalization
import BC4lean.GradedIntervalKasparovNormalization

/-! # Actual normalized convex product paths

The quarter-square cutoff is applied to the genuine convex path. Its
square defect is compact after every source localization by the actual
essential spectral estimate. Rectangular CFC intertwining controls both
ordinary normalizer commutators and localized group differences.
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

/-- The actual normalizing weight has a compact ordinary source
commutator, since the genuine graded square commutator is ordinary. -/
theorem affineProductOperator_cutoffNormalizer_commutator
    (hR : GradedKasparovTensorOperatorConditions c d R)
    (hP : GradedKasparovTensorOperatorConditions c d P)
    (hRsa : IsSelfAdjoint R) (hPsa : IsSelfAdjoint P) (t : ℝ) (a : A) :
    IsModuleCompact (moduleSquareCutoffNormalizer (1 / 4) (affineKasparovOperator R P t) *
      gradedKasparovTensorRepresentation c d a - gradedKasparovTensorRepresentation c d a *
        moduleSquareCutoffNormalizer (1 / 4) (affineKasparovOperator R P t)) := by
  let H := affineKasparovOperator R P t
  have hHsa := affineProductOperator_isSelfAdjoint (d := d) hRsa hPsa t
  change IsModuleCompact (cfc (moduleSquareCutoffWeight (1 / 4)) (H.adjoint.comp H) *
    gradedKasparovTensorRepresentation c d a - gradedKasparovTensorRepresentation c d a *
      cfc (moduleSquareCutoffWeight (1 / 4)) (H.adjoint.comp H))
  have hcomm : IsModuleCompact ((H.adjoint.comp H) * gradedKasparovTensorRepresentation c d a -
      gradedKasparovTensorRepresentation c d a * (H.adjoint.comp H)) := by
    change IsModuleCompact ((star H * H) * gradedKasparovTensorRepresentation c d a -
      gradedKasparovTensorRepresentation c d a * (star H * H))
    rw [hHsa.star_eq]
    exact affineProductOperator_square_commutator_compact c d hR hP t a
  have hQsa : IsSelfAdjoint (H.adjoint.comp H) := by
    change IsSelfAdjoint (star H * H)
    exact IsSelfAdjoint.star_mul_self H
  exact moduleCFC_commutator_isModuleCompact (H.adjoint.comp H)
    (gradedKasparovTensorRepresentation c d a)
    hQsa hcomm _
      (continuous_moduleSquareCutoffWeight (by norm_num))

/-- Actual action conjugation and rectangular CFC intertwining supply
the localized equivariance defect of the normalizing weight. -/
theorem affineProductOperator_cutoffNormalizer_equivariance
    (hR : GradedKasparovTensorOperatorConditions c d R)
    (hP : GradedKasparovTensorOperatorConditions c d P)
    (hRsa : IsSelfAdjoint R) (hPsa : IsSelfAdjoint P) (t : ℝ) (g : Γ) (a : A) :
    IsModuleCompact (((gradedKasparovTensorAction c d).conjugateOperator g
        (moduleSquareCutoffNormalizer (1 / 4) (affineKasparovOperator R P t)) -
      moduleSquareCutoffNormalizer (1 / 4) (affineKasparovOperator R P t)) *
        gradedKasparovTensorRepresentation c d a) := by
  let H := affineKasparovOperator R P t
  let U := gradedKasparovTensorAction c d
  let conjugation := U.conjugateOperatorStarAlgEquiv g
  let Q := H.adjoint.comp H
  let ρ := gradedKasparovTensorRepresentation c d
  let K := conjugation H - H
  have hHsa := affineProductOperator_isSelfAdjoint (d := d) hRsa hPsa t
  have hQsa : IsSelfAdjoint Q := by
    change IsSelfAdjoint (star H * H)
    exact IsSelfAdjoint.star_mul_self H
  have hconjugationQsa : IsSelfAdjoint (conjugation Q) := by
    change star (conjugation Q) = conjugation Q
    rw [← map_star, hQsa.star_eq]
  have hK (b : A) : IsModuleCompact (K * ρ b) :=
    affineProductOperator_equivariance_compact c d hR hP t g b
  have hdiff : IsModuleCompact ((conjugation Q - Q) * ρ a) := by
    have heq : (conjugation Q - Q) * ρ a =
        conjugation H * (K * ρ a) + K * (H * ρ a - ρ (δA.automorphism a) * H) +
          (K * ρ (δA.automorphism a)) * H := by
      dsimp [Q, K]
      change (conjugation (star H * H) - star H * H) * ρ a = _
      rw [hHsa.star_eq, map_mul]
      noncomm_ring
    rw [heq]
    exact IsModuleCompact.add
      (IsModuleCompact.add (mul_mem_moduleCompact_left (conjugation H) (hK a))
        (mul_mem_moduleCompact_left K
          (affineProductOperator_graded_commutator_compact c d hR hP t a)))
      (mul_mem_moduleCompact_right (hK (δA.automorphism a)) H)
  have hcomm : IsModuleCompact (Q * ρ a - ρ a * Q) := by
    change IsModuleCompact ((star H * H) * ρ a - ρ a * (star H * H))
    rw [hHsa.star_eq]
    exact affineProductOperator_square_commutator_compact c d hR hP t a
  have hf := continuous_moduleSquareCutoffWeight (show (0 : ℝ) < 1 / 4 by norm_num)
  have hcfc := cfc_sub_mul_isModuleCompact_of_localized_intertwining (conjugation Q) Q (ρ a)
    hconjugationQsa hQsa hdiff hcomm (moduleSquareCutoffWeight (1 / 4)) hf
  have hmap : conjugation (cfc (moduleSquareCutoffWeight (1 / 4)) Q) =
      cfc (moduleSquareCutoffWeight (1 / 4)) (conjugation Q) :=
    StarAlgHomClass.map_cfc conjugation _ Q hf.continuousOn (StarAlgEquiv.isometry conjugation).continuous hQsa hconjugationQsa
  change IsModuleCompact ((conjugation (cfc (moduleSquareCutoffWeight (1 / 4)) Q) -
    cfc (moduleSquareCutoffWeight (1 / 4)) Q) * ρ a)
  rw [hmap]
  exact hcfc

/-- All genuine graded cycle conditions hold after quarter-square cutoff
of the actual convex comparison path. -/
theorem quarterCutoffAffineProduct_cycleConditions
    (hR : GradedKasparovTensorOperatorConditions c d R)
    (hP : GradedKasparovTensorOperatorConditions c d P)
    (hRsa : IsSelfAdjoint R) (hPsa : IsSelfAdjoint P)
    (hpos : ∀ a, IsPositiveModuloModuleCompact (gradedKasparovTensorRepresentation c d a *
      (R * P + P * R) * star (gradedKasparovTensorRepresentation c d a))) (t : I) :
    GradedKasparovTensorOperatorConditions c d
      (moduleSquareCutoffNormalization (1 / 4) (affineKasparovOperator R P (t : ℝ))) := by
  let H := affineKasparovOperator R P (t : ℝ)
  let N := moduleSquareCutoffNormalizer (1 / 4) H
  let ρ := gradedKasparovTensorRepresentation c d
  let U := gradedKasparovTensorAction c d
  have hHsa := affineProductOperator_isSelfAdjoint (d := d) hRsa hPsa (t : ℝ)
  have hHodd := affineProductOperator_isOdd c d hR hP (t : ℝ)
  have hNeven : (gradedKasparovTensorGrading c d).IsEven (gradedKasparovTensorGrading c d) N :=
    (hHodd.adjoint.comp_odd hHodd).cfc (moduleSquareCutoffWeight (1 / 4))
  have hNcomm := affineProductOperator_cutoffNormalizer_commutator c d hR hP hRsa hPsa (t : ℝ)
  refine ⟨hHodd.comp_even hNeven, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [(moduleSquareCutoffNormalization_selfadjoint (1 / 4) H hHsa).star_eq, sub_self, zero_mul]
    exact IsModuleCompact.zero
  · intro a
    exact quarterSquareCutoffNormalization_square_mul_isModuleCompact H (ρ a) hHsa
      (affineProductOperator_square_commutator_compact c d hR hP (t : ℝ) a)
      (affineProductOperator_square_lowerBound c d hR hP hpos t a)
  · intro a
    have heq : moduleSquareCutoffNormalization (1 / 4) H * ρ a -
        ρ (δA.automorphism a) * moduleSquareCutoffNormalization (1 / 4) H =
        H * (N * ρ a - ρ a * N) + (H * ρ a - ρ (δA.automorphism a) * H) * N := by
      change (H * N) * ρ a - ρ (δA.automorphism a) * (H * N) = _
      noncomm_ring
    rw [heq]
    exact IsModuleCompact.add (mul_mem_moduleCompact_left H (hNcomm a))
      (mul_mem_moduleCompact_right
        (affineProductOperator_graded_commutator_compact c d hR hP (t : ℝ) a) N)
  · intro g a
    let conjugation := U.conjugateOperatorStarAlgEquiv g
    have heq : (U.conjugateOperator g (moduleSquareCutoffNormalization (1 / 4) H) -
        moduleSquareCutoffNormalization (1 / 4) H) * ρ a =
        conjugation H * ((conjugation N - N) * ρ a) + (conjugation H - H) * (N * ρ a - ρ a * N) +
          ((conjugation H - H) * ρ a) * N := by
      change (conjugation (H * N) - H * N) * ρ a = _
      rw [map_mul]
      noncomm_ring
    rw [heq]
    exact IsModuleCompact.add
      (IsModuleCompact.add (mul_mem_moduleCompact_left (conjugation H)
        (affineProductOperator_cutoffNormalizer_equivariance c d hR hP hRsa hPsa (t : ℝ) g a))
        (mul_mem_moduleCompact_left (conjugation H - H) (hNcomm a)))
      (mul_mem_moduleCompact_right
        (affineProductOperator_equivariance_compact c d hR hP (t : ℝ) g a) N)

/-- Every normalized path point retains all four actual connections. -/
theorem quarterCutoffAffineProduct_isConnection
    (hdsa : IsSelfAdjoint d.operator) (hRsa : IsSelfAdjoint R) (hPsa : IsSelfAdjoint P)
    (hR : GradedKasparovConnection c d R) (hP : GradedKasparovConnection c d P) (t : I) :
    GradedKasparovConnection c d
      (moduleSquareCutoffNormalization (1 / 4) (affineKasparovOperator R P (t : ℝ))) :=
  squareCutoffTensorOperator_isConnection c d hdsa (by norm_num) (by norm_num)
    (affineProductOperator_isSelfAdjoint (d := d) hRsa hPsa (t : ℝ))
    (affineProductOperator_isConnection c d hdsa hRsa hPsa hR hP (t : ℝ))

/-- The actual operator-norm continuous normalized path, with its exact
cutoff-normalized endpoints. -/
def quarterCutoffAffineProductOperatorPath :
    Path (moduleSquareCutoffNormalization (1 / 4) R) (moduleSquareCutoffNormalization (1 / 4) P) where
  toFun t := moduleSquareCutoffNormalization (1 / 4) (affineKasparovOperator R P (t : ℝ))
  continuous_toFun := (continuous_moduleSquareCutoffNormalization (by norm_num)).comp
    ((continuous_affineKasparovOperator R P).comp continuous_subtype_val)
  source' := by simp [affineKasparovOperator]
  target' := by simp [affineKasparovOperator]

/-- The actual normalized path supplies a genuine graded operator
homotopy, which the section/fibre construction turns into a full interval
coefficient witness. -/
def quarterCutoffAffineProductHomotopy
    (hR : GradedKasparovTensorOperatorConditions c d R)
    (hP : GradedKasparovTensorOperatorConditions c d P)
    (hRsa : IsSelfAdjoint R) (hPsa : IsSelfAdjoint P)
    (hpos : ∀ a, IsPositiveModuloModuleCompact (gradedKasparovTensorRepresentation c d a *
      (R * P + P * R) * star (gradedKasparovTensorRepresentation c d a))) :
    GradedKasparovOperatorHomotopy (gradedKasparovTensorCycleOfConditions c d R hR)
      (moduleSquareCutoffNormalization (1 / 4) R) (moduleSquareCutoffNormalization (1 / 4) P) where
  path := quarterCutoffAffineProductOperatorPath (d := d) (R := R) (P := P)
  conditions t := by
    have h := quarterCutoffAffineProduct_cycleConditions c d hR hP hRsa hPsa hpos t
    exact ⟨h.operator_odd, h.selfadjoint_mod_compact, h.square_mod_compact,
      h.commutator_compact, h.equivariance_mod_compact⟩

end BC4lean.KKTheory
