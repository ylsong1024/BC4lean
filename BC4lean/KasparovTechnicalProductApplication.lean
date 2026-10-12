import BC4lean.GradedKasparovProductCriterion
import BC4lean.KasparovTechnicalPartition
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-! # Applying an actual technical partition to actual tensor operators

The input memberships here describe the concrete operator defects in the
two technical-theorem algebras. An actual partition supplies their compact
weighted products, the weight commutators, exact evenness and action errors.
The resulting weighted operator is proved to satisfy all genuine graded
cycle laws, all four connection laws and localized positive-lift positivity.
This application lemma does not assert existence of its inputs or replace
the separate construction of the technical partition and its algebras.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace

section WeightCreation

variable {B C E F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

local instance kasparovTechnicalProductApplicationLocalInstance1 (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) : PartialOrder
    (AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ)) :=
  CStarAlgebra.spectralOrder _
local instance kasparovTechnicalProductApplicationLocalInstance2 (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) : StarOrderedRing
    (AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ)) :=
  CStarAlgebra.spectralOrderedRing _

/-- Compactness of the weighted creation square yields rectangular
compactness of the actual weighted creation map. -/
theorem weightedCreation_isModuleCompact_of_square
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (m : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ))
    (hm : IsSelfAdjoint m) (x : E)
    (hx : IsModuleCompact (m * ((moduleCreationMap φ x).comp (moduleCreationMap φ x).adjoint))) :
    IsModuleCompact (m.comp (moduleCreationMap φ x)) := by
  let T := m.comp (moduleCreationMap φ x)
  have heq : T.comp T.adjoint =
      m * ((moduleCreationMap φ x).comp (moduleCreationMap φ x).adjoint) * m := by
    dsimp only [T]
    rw [AdjointableMap.adjoint_comp]
    rw [show m.adjoint = m from hm.star_eq]
    ext y
    rfl
  have hTT : IsModuleCompact (T.comp T.adjoint) := by
    rw [heq]
    exact mul_mem_moduleCompact_right hx m
  have hstar : IsModuleCompact T.adjoint :=
    (isModuleCompact_iff_adjoint_comp_self T.adjoint).mpr
      (by simpa only [AdjointableMap.adjoint_adjoint] using hTT)
  simpa only [AdjointableMap.adjoint_adjoint] using hstar.adjoint

/-- The scalar inverse of `1+n` converts the square partition into the
required shifted-weight compactness on every creation range. -/
theorem shiftedWeight_creation_isModuleCompact
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (m n : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ))
    (hn : 0 ≤ n) (hpart : m * m + n * n = 1) (x : E)
    (hx : IsModuleCompact (m.comp (moduleCreationMap φ x))) :
    IsModuleCompact ((n - 1).comp (moduleCreationMap φ x)) := by
  let q : ℝ → ℝ := fun t => 1 / (1 + max 0 t)
  have hq : Continuous q := continuous_const.div
    (continuous_const.add (continuous_const.max continuous_id)) (fun t => by positivity)
  let Q := cfc q n
  have hpoly : cfc (fun t : ℝ => 1 - t * t) n = 1 - n * n := by
    rw [cfc_sub (fun _ : ℝ => 1) (fun t : ℝ => t * t) n
      continuous_const.continuousOn (continuous_id.mul continuous_id).continuousOn,
      cfc_const_one ℝ n hn.isSelfAdjoint,
      cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) n
        continuous_id.continuousOn continuous_id.continuousOn,
      cfc_id' ℝ n hn.isSelfAdjoint]
  have hQ : Q * (1 - n * n) = 1 - n := by
    calc
      Q * (1 - n * n) = cfc (fun t : ℝ => q t * (1 - t * t)) n := by
        change cfc q n * (1 - n * n) = _
        rw [← hpoly]
        exact (cfc_mul q (fun t : ℝ => 1 - t * t) n hq.continuousOn
          (continuous_const.sub (continuous_id.mul continuous_id)).continuousOn).symm
      _ = cfc (fun t : ℝ => 1 - t) n := by
        apply cfc_congr
        intro t ht
        have ht0 := spectrum_nonneg_of_nonneg hn ht
        dsimp only [q]
        rw [max_eq_right ht0]
        field_simp [show (1 + t : ℝ) ≠ 0 by positivity]
        ring
      _ = 1 - n := by
        rw [cfc_sub (fun _ : ℝ => 1) (fun t : ℝ => t) n
          continuous_const.continuousOn continuous_id.continuousOn,
          cfc_const_one ℝ n hn.isSelfAdjoint, cfc_id' ℝ n hn.isSelfAdjoint]
  have hpart' : 1 - n * n = m * m := by
    rw [← hpart]
    noncomm_ring
  have heq : n - 1 = -(Q * (m * m)) := by
    rw [← hpart', hQ]
    abel
  let L := AdjointableMap.compRightContinuousLinearMap
    (G := InteriorModuleTensor (E := E) φ) (moduleCreationMap φ x)
  change IsModuleCompact (L (n - 1))
  rw [heq, map_neg]
  have h := (hx.comp_left m).comp_left Q
  exact h.neg

end WeightCreation

section TechnicalApplication

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

local instance kasparovTechnicalProductApplicationLocalInstance3 : PartialOrder
    (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) := CStarAlgebra.spectralOrder _
local instance kasparovTechnicalProductApplicationLocalInstance4 : StarOrderedRing
    (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) := CStarAlgebra.spectralOrderedRing _

/-- Concrete defect memberships required when constructing the two
technical-theorem algebras from the actual first lift and frame connection. -/
structure KasparovProductTechnicalInputs
    (G : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation))
    (E₁ E₂ : NonUnitalStarSubalgebra ℂ
      (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
        (InteriorModuleTensor (E := E) d.representation)))
    (Δ : Set (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation))) : Prop where
  first_mem : interiorModuleTensorOperator d.representation c.operator ∈ Δ
  connection_mem : G ∈ Δ
  representation_mem : ∀ a, gradedKasparovTensorRepresentation c d a ∈ Δ
  creation_square_mem : ∀ x : E,
    (moduleCreationMap d.representation x).comp (moduleCreationMap d.representation x).adjoint ∈ E₁
  first_square_mem : ∀ a,
    ((interiorModuleTensorOperator d.representation c.operator) *
      (interiorModuleTensorOperator d.representation c.operator) - 1) *
        gradedKasparovTensorRepresentation c d a ∈ E₁
  first_commutator_mem : ∀ a,
    interiorModuleTensorOperator d.representation c.operator * gradedKasparovTensorRepresentation c d a -
      gradedKasparovTensorRepresentation c d (δA.automorphism a) *
        interiorModuleTensorOperator d.representation c.operator ∈ E₁
  first_equivariance_mem : ∀ g a,
    ((gradedKasparovTensorAction c d).conjugateOperator g
      (interiorModuleTensorOperator d.representation c.operator) -
        interiorModuleTensorOperator d.representation c.operator) *
          gradedKasparovTensorRepresentation c d a ∈ E₁
  second_square_mem : G * G - 1 ∈ E₂
  second_commutator_mem : ∀ a, G * gradedKasparovTensorRepresentation c d a -
    gradedKasparovTensorRepresentation c d (δA.automorphism a) * G ∈ E₂
  second_equivariance_mem : ∀ g, (gradedKasparovTensorAction c d).conjugateOperator g G - G ∈ E₂
  anticommutator_mem : interiorModuleTensorOperator d.representation c.operator * G +
    G * interiorModuleTensorOperator d.representation c.operator ∈ E₂

variable {c d}

def kasparovTechnicalProductOperator
    (G : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation))
    {E₁ E₂ : NonUnitalStarSubalgebra ℂ
      (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
        (InteriorModuleTensor (E := E) d.representation))}
    {Δ : Set (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation))}
    {f : ℕ → AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)}
    (p : KasparovTechnicalPartition (gradedKasparovTensorGrading c d)
      (gradedKasparovTensorAction c d) E₁ E₂ Δ f) :
    AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation) :=
  p.m * interiorModuleTensorOperator d.representation c.operator + p.n * G

namespace KasparovProductTechnicalInputs

variable {G : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation)}
  {E₁ E₂ : NonUnitalStarSubalgebra ℂ
    (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation))}
  {Δ : Set (AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation))}
  {f : ℕ → AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation)}
  (h : KasparovProductTechnicalInputs c d G E₁ E₂ Δ)
  (p : KasparovTechnicalPartition (gradedKasparovTensorGrading c d)
    (gradedKasparovTensorAction c d) E₁ E₂ Δ f)

include h in
theorem m_creation_compact (x : E) :
    IsModuleCompact (p.m.comp (moduleCreationMap d.representation x)) :=
  weightedCreation_isModuleCompact_of_square d.representation p.m p.m_nonneg.isSelfAdjoint x
    (p.first_ideal _ (h.creation_square_mem x))

include h in
theorem shifted_n_creation_compact (x : E) :
    IsModuleCompact ((p.n - 1).comp (moduleCreationMap d.representation x)) :=
  shiftedWeight_creation_isModuleCompact d.representation p.m p.n p.n_nonneg p.square_partition x
    (h.m_creation_compact p x)

include h in
/-- The actual weighted operator has a globally compact selfadjoint defect
from the genuine weight commutators and exact selfadjoint input operators. -/
theorem selfadjoint_defect_compact (hcsa : IsSelfAdjoint c.operator) (hGsa : IsSelfAdjoint G) :
    IsModuleCompact (kasparovTechnicalProductOperator G p - star (kasparovTechnicalProductOperator G p)) := by
  let T := interiorModuleTensorOperator d.representation c.operator
  have hTsa : IsSelfAdjoint T := by
    change star (interiorModuleTensorOperatorHom d.representation c.operator) = _
    rw [← map_star, hcsa.star_eq]
    rfl
  have heq : kasparovTechnicalProductOperator G p - star (kasparovTechnicalProductOperator G p) =
      (p.m * T - T * p.m) + (p.n * G - G * p.n) := by
    dsimp only [kasparovTechnicalProductOperator, T]
    rw [star_add, star_mul, star_mul, p.m_nonneg.isSelfAdjoint.star_eq,
      p.n_nonneg.isSelfAdjoint.star_eq, hTsa.star_eq, hGsa.star_eq]
    noncomm_ring
  rw [heq]
  exact (p.commutator_m _ h.first_mem).add (p.commutator_n _ h.connection_mem)

include h in
/-- The full signed creation defect is compact for the actual weighted
operator, for either second operator occurring in the connection laws. -/
theorem weighted_creation_defect_compact
    (S : AdjointableMap C F F)
    (hD : ∀ x : E, IsModuleCompact (G.comp (moduleCreationMap d.representation x) -
      (moduleCreationMap d.representation (c.grading.grading x)).comp S)) (x : E) :
    IsModuleCompact ((kasparovTechnicalProductOperator G p).comp (moduleCreationMap d.representation x) -
      (moduleCreationMap d.representation (c.grading.grading x)).comp S) := by
  have heq : (kasparovTechnicalProductOperator G p).comp (moduleCreationMap d.representation x) -
      (moduleCreationMap d.representation (c.grading.grading x)).comp S =
      p.m.comp (moduleCreationMap d.representation (c.operator x)) +
      p.n.comp (G.comp (moduleCreationMap d.representation x) -
        (moduleCreationMap d.representation (c.grading.grading x)).comp S) +
      ((p.n - 1).comp (moduleCreationMap d.representation (c.grading.grading x))).comp S := by
    ext y
    simp only [kasparovTechnicalProductOperator, AdjointableMap.comp_apply,
      AdjointableMap.coe_add_apply, AdjointableMap.coe_sub_apply, AdjointableMap.mul_apply,
      AdjointableMap.one_apply, tensorOperator_creation_apply, map_sub]
    abel
  rw [heq]
  exact ((h.m_creation_compact p (c.operator x)).add ((hD x).comp_left p.n)).add
    ((h.shifted_n_creation_compact p (c.grading.grading x)).comp_right S)

include h in
/-- All four actual homogeneous connection laws, including both adjoint
laws, follow from the weighted creation estimates. -/
theorem weighted_connection (hcsa : IsSelfAdjoint c.operator) (hGsa : IsSelfAdjoint G)
    (hG : GradedKasparovConnection c d G) :
    GradedKasparovConnection c d (kasparovTechnicalProductOperator G p) := by
  have hD := h.weighted_creation_defect_compact p d.operator hG.creation_defect
  have hDstar : ∀ x : E, IsModuleCompact (G.comp (moduleCreationMap d.representation x) -
      (moduleCreationMap d.representation (c.grading.grading x)).comp (star d.operator)) := by
    intro x
    simpa only [hGsa.star_eq] using hG.creation_adjoint_defect x
  have hRstar := h.weighted_creation_defect_compact p (star d.operator) hDstar
  have hK := (h.selfadjoint_defect_compact p hcsa hGsa).neg
  have hstar (x : E) : IsModuleCompact ((star (kasparovTechnicalProductOperator G p)).comp
      (moduleCreationMap d.representation x) -
        (moduleCreationMap d.representation (c.grading.grading x)).comp (star d.operator)) := by
    have heq : (star (kasparovTechnicalProductOperator G p)).comp (moduleCreationMap d.representation x) -
        (moduleCreationMap d.representation (c.grading.grading x)).comp (star d.operator) =
        ((kasparovTechnicalProductOperator G p).comp (moduleCreationMap d.representation x) -
          (moduleCreationMap d.representation (c.grading.grading x)).comp (star d.operator)) +
        (star (kasparovTechnicalProductOperator G p) - kasparovTechnicalProductOperator G p).comp
          (moduleCreationMap d.representation x) := by
      ext y
      simp only [AdjointableMap.comp_apply, AdjointableMap.coe_add_apply, AdjointableMap.coe_sub_apply]
      abel
    rw [heq]
    have hKstar : IsModuleCompact (star (kasparovTechnicalProductOperator G p) -
        kasparovTechnicalProductOperator G p) := by
      simpa only [neg_sub] using hK
    exact (hRstar x).add (hKstar.comp_right _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    simpa only [hx, neg_sub] using (hD x).neg
  · intro x hx
    simpa only [hx, neg_sub] using (hstar x).neg
  · intro x hx
    have hc := hD x
    rw [hx, moduleCreationMap_neg] at hc
    convert hc using 1
    ext y
    simp only [AdjointableMap.comp_apply, AdjointableMap.coe_add_apply,
      AdjointableMap.coe_sub_apply, AdjointableMap.coe_neg_apply]
    abel
  · intro x hx
    have hc := hstar x
    rw [hx, moduleCreationMap_neg] at hc
    convert hc using 1
    ext y
    simp only [AdjointableMap.comp_apply, AdjointableMap.coe_add_apply,
      AdjointableMap.coe_sub_apply, AdjointableMap.coe_neg_apply]
    abel

include h in
/-- The exact algebraic weighted calculation proves every genuine graded
cycle defect from the concrete technical-algebra memberships. -/
theorem weighted_cycleConditions (hcsa : IsSelfAdjoint c.operator) (hGsa : IsSelfAdjoint G)
    (hGodd : (gradedKasparovTensorGrading c d).IsOdd (gradedKasparovTensorGrading c d) G) :
    GradedKasparovTensorOperatorConditions c d (kasparovTechnicalProductOperator G p) where
  operator_odd := by
    have hT := GradedHilbertModule.IsOdd.interiorModuleTensorOperator
      d.grading d.representation_graded c.operator_odd
    exact (p.m_even.comp_odd hT).add (p.n_even.comp_odd hGodd)
  selfadjoint_mod_compact a := mul_mem_moduleCompact_right
    (h.selfadjoint_defect_compact p hcsa hGsa) (gradedKasparovTensorRepresentation c d a)
  square_mod_compact a := by
    let T := interiorModuleTensorOperator d.representation c.operator
    let ρ := gradedKasparovTensorRepresentation c d
    let R := kasparovTechnicalProductOperator G p
    have hfirst : IsModuleCompact (p.m * ((T * T - 1) * ρ a)) :=
      p.first_ideal _ (h.first_square_mem a)
    have hsecond : IsModuleCompact (p.n * ((G * G - 1) * ρ a)) := by
      simpa only [IsModuleCompact, mul_assoc] using mul_mem_moduleCompact_right
        (p.second_ideal _ h.second_square_mem) (ρ a)
    have hcross : IsModuleCompact ((p.m * (p.n * (T * G + G * T))) * ρ a) :=
      mul_mem_moduleCompact_right
        (mul_mem_moduleCompact_left p.m (p.second_ideal _ h.anticommutator_mem)) (ρ a)
    have hcomm₁ : IsModuleCompact ((p.m * (T * p.m - p.m * T) * T) * ρ a) :=
      mul_mem_moduleCompact_right (mul_mem_moduleCompact_right
        (mul_mem_moduleCompact_left p.m (by simpa only [IsModuleCompact, neg_sub] using (p.commutator_m _ h.first_mem).neg)) T) (ρ a)
    have hcomm₂ : IsModuleCompact ((p.m * (T * p.n - p.n * T) * G) * ρ a) :=
      mul_mem_moduleCompact_right (mul_mem_moduleCompact_right
        (mul_mem_moduleCompact_left p.m (by simpa only [IsModuleCompact, neg_sub] using (p.commutator_n _ h.first_mem).neg)) G) (ρ a)
    have hcomm₃ : IsModuleCompact ((p.n * (G * p.m - p.m * G) * T) * ρ a) :=
      mul_mem_moduleCompact_right (mul_mem_moduleCompact_right
        (mul_mem_moduleCompact_left p.n (by simpa only [IsModuleCompact, neg_sub] using (p.commutator_m _ h.connection_mem).neg)) T) (ρ a)
    have hcomm₄ : IsModuleCompact ((p.n * (G * p.n - p.n * G) * G) * ρ a) :=
      mul_mem_moduleCompact_right (mul_mem_moduleCompact_right
        (mul_mem_moduleCompact_left p.n (by simpa only [IsModuleCompact, neg_sub] using (p.commutator_n _ h.connection_mem).neg)) G) (ρ a)
    have halg : (R * R - 1) * ρ a =
        p.m * (p.m * ((T * T - 1) * ρ a)) +
        p.n * (p.n * ((G * G - 1) * ρ a)) +
        (p.m * (p.n * (T * G + G * T))) * ρ a +
        ((p.m * (T * p.m - p.m * T) * T) * ρ a) +
        ((p.m * (T * p.n - p.n * T) * G) * ρ a) +
        ((p.n * (G * p.m - p.m * G) * T) * ρ a) +
        ((p.n * (G * p.n - p.n * G) * G) * ρ a) +
        (p.n * p.m - p.m * p.n) * G * T * ρ a +
        (p.m * p.m + p.n * p.n - 1) * ρ a := by
      dsimp only [R, kasparovTechnicalProductOperator, T, ρ]
      noncomm_ring
    have heq := halg
    simp only [p.weights_commute.eq, p.square_partition, sub_self, zero_mul, add_zero] at heq
    change IsModuleCompact ((R * R - 1) * ρ a)
    rw [heq]
    exact (((((IsModuleCompact.add (mul_mem_moduleCompact_left p.m hfirst)
      (mul_mem_moduleCompact_left p.n hsecond)).add hcross).add hcomm₁).add hcomm₂).add hcomm₃).add hcomm₄
  commutator_compact a := by
    let T := interiorModuleTensorOperator d.representation c.operator
    let ρ := gradedKasparovTensorRepresentation c d
    have heq : kasparovTechnicalProductOperator G p * ρ a -
        ρ (δA.automorphism a) * kasparovTechnicalProductOperator G p =
        p.m * (T * ρ a - ρ (δA.automorphism a) * T) +
        p.n * (G * ρ a - ρ (δA.automorphism a) * G) +
        (p.m * ρ (δA.automorphism a) - ρ (δA.automorphism a) * p.m) * T +
        (p.n * ρ (δA.automorphism a) - ρ (δA.automorphism a) * p.n) * G := by
      dsimp only [kasparovTechnicalProductOperator, T, ρ]
      noncomm_ring
    change IsModuleCompact (kasparovTechnicalProductOperator G p * ρ a -
      ρ (δA.automorphism a) * kasparovTechnicalProductOperator G p)
    rw [heq]
    exact (((p.first_ideal _ (h.first_commutator_mem a)).add
      (p.second_ideal _ (h.second_commutator_mem a))).add
      (mul_mem_moduleCompact_right
        (p.commutator_m _ (h.representation_mem (δA.automorphism a))) T)).add
      (mul_mem_moduleCompact_right
        (p.commutator_n _ (h.representation_mem (δA.automorphism a))) G)
  equivariance_mod_compact g a := by
    let T := interiorModuleTensorOperator d.representation c.operator
    let ρ := gradedKasparovTensorRepresentation c d
    let U := gradedKasparovTensorAction c d
    let χ := U.conjugateOperatorStarAlgEquiv g
    have heq : (U.conjugateOperator g (kasparovTechnicalProductOperator G p) -
        kasparovTechnicalProductOperator G p) * ρ a =
        p.m * ((U.conjugateOperator g T - T) * ρ a) +
        p.n * ((U.conjugateOperator g G - G) * ρ a) +
        (U.conjugateOperator g p.m - p.m) * U.conjugateOperator g T * ρ a +
        (U.conjugateOperator g p.n - p.n) * U.conjugateOperator g G * ρ a := by
      change (χ (p.m * T + p.n * G) - (p.m * T + p.n * G)) * ρ a = _
      rw [map_add, map_mul, map_mul]
      change _ = p.m * ((χ T - T) * ρ a) + p.n * ((χ G - G) * ρ a) +
        (χ p.m - p.m) * χ T * ρ a + (χ p.n - p.n) * χ G * ρ a
      noncomm_ring
    have hsecond : IsModuleCompact (p.n * ((U.conjugateOperator g G - G) * ρ a)) := by
      simpa only [IsModuleCompact, mul_assoc] using mul_mem_moduleCompact_right
        (p.second_ideal _ (h.second_equivariance_mem g)) (ρ a)
    change IsModuleCompact ((U.conjugateOperator g (kasparovTechnicalProductOperator G p) -
      kasparovTechnicalProductOperator G p) * ρ a)
    rw [heq]
    exact (((p.first_ideal _ (h.first_equivariance_mem g a)).add hsecond).add
      (mul_mem_moduleCompact_right (mul_mem_moduleCompact_right (p.action_m g)
        (U.conjugateOperator g T)) (ρ a))).add
      (mul_mem_moduleCompact_right (mul_mem_moduleCompact_right (p.action_n g)
        (U.conjugateOperator g G)) (ρ a))

include h in
/-- The explicit localized positive lift is twice the compression of the
positive first weight. Its error is the genuinely compact weighted square
defect, cross anticommutator and weight commutators. -/
theorem weighted_positivity (a : A) :
    IsPositiveModuloModuleCompact (gradedKasparovProductPositivityOperator c d
      (kasparovTechnicalProductOperator G p) a) := by
  let T := interiorModuleTensorOperator d.representation c.operator
  let ρ := gradedKasparovTensorRepresentation c d
  have hfirst : IsModuleCompact (p.m * ((T * T - 1) * star (ρ a))) := by
    have hfirst := p.first_ideal _ (h.first_square_mem (star a))
    simpa only [map_star] using hfirst
  have hcross : IsModuleCompact (ρ a * (p.n * (T * G + G * T)) * star (ρ a)) :=
    mul_mem_moduleCompact_right
      (mul_mem_moduleCompact_left (ρ a) (p.second_ideal _ h.anticommutator_mem)) (star (ρ a))
  have hcomm₁ : IsModuleCompact (ρ a * ((T * p.m - p.m * T) * T) * star (ρ a)) :=
    mul_mem_moduleCompact_right (mul_mem_moduleCompact_left (ρ a)
      (mul_mem_moduleCompact_right (by simpa only [IsModuleCompact, neg_sub] using (p.commutator_m _ h.first_mem).neg) T)) (star (ρ a))
  have hcomm₂ : IsModuleCompact (ρ a * ((T * p.n - p.n * T) * G) * star (ρ a)) :=
    mul_mem_moduleCompact_right (mul_mem_moduleCompact_left (ρ a)
      (mul_mem_moduleCompact_right (by simpa only [IsModuleCompact, neg_sub] using (p.commutator_n _ h.first_mem).neg) G)) (star (ρ a))
  refine ⟨ρ a * p.m * star (ρ a) + ρ a * p.m * star (ρ a),
    add_nonneg (star_right_conjugate_nonneg p.m_nonneg (ρ a))
      (star_right_conjugate_nonneg p.m_nonneg (ρ a)), ?_⟩
  have heq : gradedKasparovProductPositivityOperator c d (kasparovTechnicalProductOperator G p) a -
      (ρ a * p.m * star (ρ a) + ρ a * p.m * star (ρ a)) =
      ρ a * (p.m * ((T * T - 1) * star (ρ a))) +
      ρ a * (p.m * ((T * T - 1) * star (ρ a))) +
      ρ a * (p.n * (T * G + G * T)) * star (ρ a) +
      ρ a * ((T * p.m - p.m * T) * T) * star (ρ a) +
      ρ a * ((T * p.n - p.n * T) * G) * star (ρ a) := by
    dsimp only [gradedKasparovProductPositivityOperator, kasparovTechnicalProductOperator, T, ρ]
    noncomm_ring
  rw [heq]
  exact (((IsModuleCompact.add (mul_mem_moduleCompact_left (ρ a) hfirst)
    (mul_mem_moduleCompact_left (ρ a) hfirst)).add hcross).add hcomm₁).add hcomm₂

include h in
/-- The actual weighted product also satisfies positivity relative to an
unnormalized first operator when its genuine localized difference and
creation-local bracket are included in the constructed test algebras.
The difference is weighted before compactness is concluded; arbitrary
first compacts are not assumed to tensor into tensor compacts. -/
theorem weighted_positivity_of_firstReplacement
    (O : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation))
    (hO : O ∈ Δ) (hOG : O * G + G * O ∈ E₂)
    (hK : ∀ b, (O - interiorModuleTensorOperator d.representation c.operator) *
      gradedKasparovTensorRepresentation c d b ∈ E₁) (a : A) :
    IsPositiveModuloModuleCompact
      (gradedKasparovTensorRepresentation c d a *
        (O * kasparovTechnicalProductOperator G p + kasparovTechnicalProductOperator G p * O) *
          star (gradedKasparovTensorRepresentation c d a)) := by
  let T := interiorModuleTensorOperator d.representation c.operator
  let ρ := gradedKasparovTensorRepresentation c d
  let K := O - T
  let Cₐ := T * star (ρ a) - ρ (δA.automorphism (star a)) * T
  have hMK (b : A) : IsModuleCompact (p.m * (K * ρ b)) :=
    p.first_ideal _ (hK b)
  have hcommK : IsModuleCompact (p.m * K - K * p.m) := by
    have heq : p.m * K - K * p.m =
        (p.m * O - O * p.m) - (p.m * T - T * p.m) := by
      dsimp only [K]
      noncomm_ring
    rw [heq]
    exact (p.commutator_m _ hO).sub (p.commutator_m _ h.first_mem)
  have hMC : IsModuleCompact (p.m * Cₐ) := by
    have hc := p.first_ideal _ (h.first_commutator_mem (star a))
    change IsModuleCompact (p.m * (T * star (ρ a) -
      ρ (δA.automorphism (star a)) * T))
    simpa only [map_star] using hc
  have hMKC : IsModuleCompact (p.m * K * Cₐ) := by
    have heq : p.m * K * Cₐ = K * (p.m * Cₐ) + (p.m * K - K * p.m) * Cₐ := by
      noncomm_ring
    rw [heq]
    exact IsModuleCompact.add (mul_mem_moduleCompact_left K hMC) (mul_mem_moduleCompact_right hcommK Cₐ)
  have hMKstar : IsModuleCompact (p.m * (K * star (ρ a))) := by
    simpa only [map_star] using hMK (star a)
  have hMKT : IsModuleCompact (p.m * K * T * star (ρ a)) := by
    have heq : p.m * K * T * star (ρ a) =
        (p.m * (K * ρ (δA.automorphism (star a)))) * T + p.m * K * Cₐ := by
      dsimp only [Cₐ]
      noncomm_ring
    rw [heq]
    exact IsModuleCompact.add (mul_mem_moduleCompact_right (hMK _) T) hMKC
  have hMTK : IsModuleCompact (p.m * T * K * star (ρ a)) := by
    have heq : p.m * T * K * star (ρ a) =
        T * (p.m * (K * star (ρ a))) + (p.m * T - T * p.m) * K * star (ρ a) := by
      noncomm_ring
    rw [heq]
    exact IsModuleCompact.add (mul_mem_moduleCompact_left T hMKstar)
      (mul_mem_moduleCompact_right
        (mul_mem_moduleCompact_right (p.commutator_m _ h.first_mem) K) (star (ρ a)))
  have hMsquare : IsModuleCompact (p.m * ((T * T - 1) * star (ρ a))) := by
    simpa only [map_star] using p.first_ideal _ (h.first_square_mem (star a))
  have hMOT : IsModuleCompact (p.m * (O * T + T * O - (1 + 1)) * star (ρ a)) := by
    have heq : p.m * (O * T + T * O - (1 + 1)) * star (ρ a) =
        p.m * ((T * T - 1) * star (ρ a)) +
          p.m * ((T * T - 1) * star (ρ a)) +
            p.m * K * T * star (ρ a) + p.m * T * K * star (ρ a) := by
      dsimp only [K]
      noncomm_ring
    rw [heq]
    exact ((hMsquare.add hMsquare).add hMKT).add hMTK
  have hNOG : IsModuleCompact (ρ a * (p.n * (O * G + G * O)) * star (ρ a)) :=
    mul_mem_moduleCompact_right
      (mul_mem_moduleCompact_left (ρ a) (p.second_ideal _ hOG)) (star (ρ a))
  have hcomm₁ : IsModuleCompact (ρ a * ((O * p.m - p.m * O) * T) * star (ρ a)) :=
    mul_mem_moduleCompact_right (mul_mem_moduleCompact_left (ρ a)
      (mul_mem_moduleCompact_right (by simpa only [IsModuleCompact, neg_sub] using (p.commutator_m _ hO).neg) T)) (star (ρ a))
  have hcomm₂ : IsModuleCompact (ρ a * ((O * p.n - p.n * O) * G) * star (ρ a)) :=
    mul_mem_moduleCompact_right (mul_mem_moduleCompact_left (ρ a)
      (mul_mem_moduleCompact_right (by simpa only [IsModuleCompact, neg_sub] using (p.commutator_n _ hO).neg) G)) (star (ρ a))
  refine ⟨ρ a * p.m * star (ρ a) + ρ a * p.m * star (ρ a),
    add_nonneg (star_right_conjugate_nonneg p.m_nonneg (ρ a))
      (star_right_conjugate_nonneg p.m_nonneg (ρ a)), ?_⟩
  have heq : ρ a * (O * kasparovTechnicalProductOperator G p +
      kasparovTechnicalProductOperator G p * O) * star (ρ a) -
      (ρ a * p.m * star (ρ a) + ρ a * p.m * star (ρ a)) =
      ρ a * (p.m * (O * T + T * O - (1 + 1)) * star (ρ a)) +
        ρ a * (p.n * (O * G + G * O)) * star (ρ a) +
          ρ a * ((O * p.m - p.m * O) * T) * star (ρ a) +
            ρ a * ((O * p.n - p.n * O) * G) * star (ρ a) := by
    dsimp only [kasparovTechnicalProductOperator, T]
    noncomm_ring
  rw [heq]
  exact ((IsModuleCompact.add (mul_mem_moduleCompact_left (ρ a) hMOT) hNOG).add hcomm₁).add hcomm₂

include h in
/-- Applying the constructed technical partition yields the full genuine
product criterion once its concrete operator memberships have been proved. -/
theorem isGradedProduct (hcsa : IsSelfAdjoint c.operator) (hGsa : IsSelfAdjoint G)
    (hGodd : (gradedKasparovTensorGrading c d).IsOdd (gradedKasparovTensorGrading c d) G)
    (hG : GradedKasparovConnection c d G) :
    IsGradedKasparovProductOperator c d (kasparovTechnicalProductOperator G p) where
  cycleConditions := h.weighted_cycleConditions p hcsa hGsa hGodd
  connection := h.weighted_connection p hcsa hGsa hG
  positivity := h.weighted_positivity p

end KasparovProductTechnicalInputs
end TechnicalApplication
end BC4lean.KKTheory
