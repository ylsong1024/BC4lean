import BC4lean.KasparovTripleSecondAlgebra
import BC4lean.KasparovTripleWeightedComparison
import BC4lean.SignedConnectionWeightedPartition
import BC4lean.EssentialModulePositivityFibre

/-! # The common weighted operator meets both actual product criteria

The first comparison uses the original first-pair product's actual positive
lift. Its compact error is tensored into the first technical algebra and is
made compact by the first partition weight. The third connection uses the
actual first-pair creation squares and the square partition. All four original
connection laws and all localized cycle conditions are retained through the
whole-cycle associator. No common product or homotopy is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovTriple
open InteriorModuleTensorAssociator
open GradedTripleAnticommutatorConnection

variable {Γ A B C D E F G : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Dᵐᵒᵖ G] [CStarModule Dᵐᵒᵖ G]
  [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C} {χ : CStarAlgebraAction Γ D}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C} {δD : CStarGrading D}
  (c : GradedKasparovCycle α β δA δB E)
  (d : GradedKasparovCycle β γ δB δC F)
  (e : GradedKasparovCycle γ χ δC δD G)
  (Q : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation))
  (hQ : GradedKasparovTensorOperatorConditions c d Q)
  (T : AdjointableMap D (InteriorModuleTensor (E := F) e.representation)
    (InteriorModuleTensor (E := F) e.representation))
  (hT : GradedKasparovTensorOperatorConditions d e T)
  (R : AdjointableMap D (RightTensor (E := E) d.representation e.representation)
    (RightTensor (E := E) d.representation e.representation))


local instance kasparovTripleWeightedProductLocalInstance1 : PartialOrder (AdjointableMap D
    (RightTensor (E := E) d.representation e.representation)
    (RightTensor (E := E) d.representation e.representation)) := CStarAlgebra.spectralOrder _
local instance kasparovTripleWeightedProductLocalInstance2 : StarOrderedRing (AdjointableMap D
    (RightTensor (E := E) d.representation e.representation)
    (RightTensor (E := E) d.representation e.representation)) := CStarAlgebra.spectralOrderedRing _
local instance kasparovTripleWeightedProductLocalInstance3 : PartialOrder (AdjointableMap D
    (LeftTensor (E := E) d.representation e.representation)
    (LeftTensor (E := E) d.representation e.representation)) := CStarAlgebra.spectralOrder _
local instance kasparovTripleWeightedProductLocalInstance4 : StarOrderedRing (AdjointableMap D
    (LeftTensor (E := E) d.representation e.representation)
    (LeftTensor (E := E) d.representation e.representation)) := CStarAlgebra.spectralOrderedRing _
local instance kasparovTripleWeightedProductLocalInstance5 : PartialOrder (AdjointableMap C
    (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation)) := CStarAlgebra.spectralOrder _
local instance kasparovTripleWeightedProductLocalInstance6 : StarOrderedRing (AdjointableMap C
    (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation)) := CStarAlgebra.spectralOrderedRing _

variable {E₁ E₂ : NonUnitalStarSubalgebra ℂ (AdjointableMap D
    (RightTensor (E := E) d.representation e.representation)
    (RightTensor (E := E) d.representation e.representation))}
  {Δ : Set (AdjointableMap D (RightTensor (E := E) d.representation e.representation)
    (RightTensor (E := E) d.representation e.representation))}
  {f : ℕ → AdjointableMap D (RightTensor (E := E) d.representation e.representation)
    (RightTensor (E := E) d.representation e.representation)}
  (p : KasparovTechnicalPartition (gradedKasparovTensorGrading c (secondPairCycle d e T hT))
    (gradedKasparovTensorAction c (secondPairCycle d e T hT)) E₁ E₂ Δ f)
  (inputs : KasparovProductTechnicalInputs c (secondPairCycle d e T hT) R E₁ E₂ Δ)

/-- The actual positive-lift comparison on the first pair is transported
as an operator identity, including its original F₁ operator. -/
theorem lift_firstPairPositivityOperator (a : A) :
    (hilbertEquiv d.representation e.representation).transport
      (interiorModuleTensorOperator e.representation (gradedKasparovProductPositivityOperator c d Q a)) =
    gradedKasparovProductPositivityOperator c (secondPairCycle d e T hT)
      (pairLift d.representation e.representation Q) a := by
  let Ω := hilbertEquiv (E := E) d.representation e.representation
  let σ : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation) →⋆ₐ[ℂ]
      AdjointableMap D (LeftTensor (E := E) d.representation e.representation)
        (LeftTensor (E := E) d.representation e.representation) :=
    interiorModuleTensorOperatorHom e.representation
  let ρL : AdjointableMap D (LeftTensor (E := E) d.representation e.representation)
      (LeftTensor (E := E) d.representation e.representation) :=
    σ (gradedKasparovTensorRepresentation c d a)
  let OL : AdjointableMap D (LeftTensor (E := E) d.representation e.representation)
      (LeftTensor (E := E) d.representation e.representation) :=
    σ (interiorModuleTensorOperator d.representation c.operator)
  let QL : AdjointableMap D (LeftTensor (E := E) d.representation e.representation)
      (LeftTensor (E := E) d.representation e.representation) := σ Q
  let ρR : AdjointableMap D (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation) :=
    interiorModuleTensorOperator (rightRepresentation d.representation e.representation)
      (c.representation a)
  let OR : AdjointableMap D (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation) :=
    interiorModuleTensorOperator (rightRepresentation d.representation e.representation) c.operator
  have hρ : Ω.transport ρL = ρR :=
    hilbertEquiv_transport_operator d.representation e.representation (c.representation a)
  have hO : Ω.transport OL = OR :=
    hilbertEquiv_transport_operator d.representation e.representation c.operator
  change Ω.transport (σ (gradedKasparovProductPositivityOperator c d Q a)) =
    ρR * (OR * Ω.transport QL + Ω.transport QL * OR) * star ρR
  have hσ : σ (gradedKasparovProductPositivityOperator c d Q a) =
      ρL * (OL * QL + QL * OL) * star ρL := by
    change σ (gradedKasparovTensorRepresentation c d a *
      (interiorModuleTensorOperator d.representation c.operator * Q +
        Q * interiorModuleTensorOperator d.representation c.operator) *
          star (gradedKasparovTensorRepresentation c d a)) = _
    simp only [map_mul, map_add, map_star, ρL, OL, QL]
  rw [hσ, HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_mul,
    HilbertModuleEquiv.transport_add, HilbertModuleEquiv.transport_mul,
    HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_star, hρ, hO]

include inputs in
/-- A compact error on the first pair is not asserted compact after
tensoring. Its actual membership in E₁ is consumed by the partition. -/
theorem weighted_firstPairPositivity
    (hQproduct : IsGradedKasparovProductOperator c d Q)
    (hQΔ : pairLift d.representation e.representation Q ∈ Δ)
    (hpair : ∀ K : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation), IsModuleCompact K →
        (hilbertEquiv d.representation e.representation).transport
          (interiorModuleTensorOperator e.representation K) ∈ E₁) (a : A) :
    IsPositiveModuloModuleCompact (p.m * gradedKasparovProductPositivityOperator c
      (secondPairCycle d e T hT) (pairLift d.representation e.representation Q) a) := by
  let Ω := hilbertEquiv (E := E) d.representation e.representation
  let JR : GradedHilbertModule δD (RightTensor (E := E) d.representation e.representation) :=
    gradedKasparovTensorGrading c (secondPairCycle d e T hT)
  let UR : EquivariantHilbertModule χ (RightTensor (E := E) d.representation e.representation) :=
    gradedKasparovTensorAction c (secondPairCycle d e T hT)
  let pR : KasparovTechnicalPartition JR UR E₁ E₂ Δ f := p
  let σ : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation) →⋆ₐ[ℂ]
      AdjointableMap D (LeftTensor (E := E) d.representation e.representation)
        (LeftTensor (E := E) d.representation e.representation) :=
    interiorModuleTensorOperatorHom e.representation
  let m : AdjointableMap D (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation) := pR.m
  let ρ : A →⋆ₙₐ[ℂ] AdjointableMap D
      (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation) :=
    gradedKasparovTensorRepresentation c (secondPairCycle d e T hT)
  let O : AdjointableMap D (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation) :=
    interiorModuleTensorOperator (rightRepresentation d.representation e.representation) c.operator
  let Q₃ : AdjointableMap D (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation) :=
    pairLift d.representation e.representation Q
  let H : AdjointableMap D (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation) :=
    ρ a * (O * Q₃ + Q₃ * O) * star (ρ a)
  obtain ⟨V, hV⟩ := (hQproduct.positivity a).exists_star_square
  let P : AdjointableMap D (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation) := Ω.transport (σ (star V * V))
  have hP : 0 ≤ P := by
    change 0 ≤ Ω.transport (σ (star V * V))
    rw [map_mul, map_star, HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_star]
    exact star_mul_self_nonneg (Ω.transport (σ V))
  have hHP : H - P ∈ E₁ := by
    have h := hpair _ hV
    change Ω.transport (σ (gradedKasparovProductPositivityOperator c d Q a - star V * V)) ∈ E₁ at h
    have hlift : Ω.transport (σ (gradedKasparovProductPositivityOperator c d Q a)) = H :=
      lift_firstPairPositivityOperator c d e Q T hT a
    rw [map_sub, HilbertModuleEquiv.transport_sub, hlift] at h
    exact h
  have hmρ : IsModuleCompact (m * ρ a - ρ a * m) :=
    pR.commutator_m (ρ a) (inputs.representation_mem a)
  have hmsa : IsSelfAdjoint m := pR.m_nonneg.isSelfAdjoint
  have hmρstar : IsModuleCompact (m * star (ρ a) - star (ρ a) * m) := by
    have h := hmρ.adjoint.neg
    change IsModuleCompact (-(star (m * ρ a - ρ a * m))) at h
    simpa only [star_sub, star_mul, hmsa.star_eq, neg_sub] using h
  have hmO : IsModuleCompact (m * O - O * m) := pR.commutator_m O inputs.first_mem
  have hmQ : IsModuleCompact (m * Q₃ - Q₃ * m) := pR.commutator_m Q₃ hQΔ
  have hmAnti : IsModuleCompact (m * (O * Q₃ + Q₃ * O) - (O * Q₃ + Q₃ * O) * m) := by
    have h := (moduleCompact_commutator_mul hmO hmQ).add
      (moduleCompact_commutator_mul hmQ hmO)
    convert h using 1
    noncomm_ring
  have hmH : IsModuleCompact (m * H - H * m) :=
    moduleCompact_commutator_mul (moduleCompact_commutator_mul hmρ hmAnti) hmρstar
  exact weighted_positive_of_lift_mod_firstAlgebra m H P E₁ pR.m_nonneg pR.m_norm_le_one
    hP hHP pR.first_ideal hmH

include inputs in
set_option maxHeartbeats 1200000 in
/-- The weighted operator's genuine third connection comes from the
actual first-pair creation squares in E₁, the composed third connection,
and the square partition; all original adjoint laws are included. -/
theorem weighted_connection_onLeft
    (hcsa : IsSelfAdjoint c.operator) (hRsa : IsSelfAdjoint R)
    (hesa : IsSelfAdjoint e.operator)
    (hRconnection : GradedKasparovConnection c (secondPairCycle d e T hT) R)
    (hTconnection : GradedKasparovConnection d e T)
    (hthird : ∀ u : InteriorModuleTensor (E := E) d.representation,
      (hilbertEquiv d.representation e.representation).transport
        ((moduleCreationMap e.representation u).comp (moduleCreationMap e.representation u).adjoint) ∈ E₁) :
    GradedKasparovConnection (firstPairCycle c d Q hQ) e
      ((hilbertEquiv d.representation e.representation).symm.transport
        (kasparovTechnicalProductOperator (c := c) (d := secondPairCycle d e T hT) R p)) := by
  let Ω := hilbertEquiv (E := E) d.representation e.representation
  let JR : GradedHilbertModule δD (RightTensor (E := E) d.representation e.representation) :=
    gradedKasparovTensorGrading c (secondPairCycle d e T hT)
  let UR : EquivariantHilbertModule χ (RightTensor (E := E) d.representation e.representation) :=
    gradedKasparovTensorAction c (secondPairCycle d e T hT)
  let pR : KasparovTechnicalPartition JR UR E₁ E₂ Δ f := p
  let J : GradedHilbertModule δC (InteriorModuleTensor (E := E) d.representation) :=
    c.grading.interiorTensor d.grading d.representation_graded
  let mR : AdjointableMap D (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation) := pR.m
  let nR : AdjointableMap D (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation) := pR.n
  let OR : AdjointableMap D (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation) :=
    interiorModuleTensorOperator (rightRepresentation d.representation e.representation) c.operator
  let m : AdjointableMap D (LeftTensor (E := E) d.representation e.representation)
      (LeftTensor (E := E) d.representation e.representation) := Ω.symm.transport mR
  let n : AdjointableMap D (LeftTensor (E := E) d.representation e.representation)
      (LeftTensor (E := E) d.representation e.representation) := Ω.symm.transport nR
  let O : AdjointableMap D (LeftTensor (E := E) d.representation e.representation)
      (LeftTensor (E := E) d.representation e.representation) :=
    interiorModuleTensorOperator e.representation (interiorModuleTensorOperator d.representation c.operator)
  let RL : AdjointableMap D (LeftTensor (E := E) d.representation e.representation)
      (LeftTensor (E := E) d.representation e.representation) := Ω.symm.transport R
  have hmRnonneg : 0 ≤ mR := pR.m_nonneg
  have hnRnonneg : 0 ≤ nR := pR.n_nonneg
  have hmRsa : IsSelfAdjoint mR := hmRnonneg.isSelfAdjoint
  have hmsa : IsSelfAdjoint m := by
    change star (Ω.symm.transport mR) = Ω.symm.transport mR
    rw [← HilbertModuleEquiv.transport_star, hmRsa.star_eq]
  have hn : 0 ≤ n := by
    change 0 ≤ Ω.symm.transportStarAlgEquiv nR
    exact map_nonneg Ω.symm.transportStarAlgEquiv hnRnonneg
  have hOsa : IsSelfAdjoint O := by
    change star (interiorModuleTensorOperatorHom e.representation
      (interiorModuleTensorOperatorHom d.representation c.operator)) = _
    rw [← map_star, ← map_star, hcsa.star_eq]
    rfl
  have hRLsa : IsSelfAdjoint RL := by
    change star (Ω.symm.transport R) = Ω.symm.transport R
    rw [← HilbertModuleEquiv.transport_star, hRsa.star_eq]
  have hpartR : mR * mR + nR * nR = 1 := pR.square_partition
  have hpart : m * m + n * n = 1 := by
    have h := congrArg Ω.symm.transport hpartR
    simpa only [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_add,
      HilbertModuleEquiv.transport_one] using h
  have hfirst : Ω.symm.transport OR = O := by
    have h := congrArg Ω.symm.transport
      (hilbertEquiv_transport_operator d.representation e.representation c.operator)
    exact h.symm.trans (Ω.transport_symm O)
  have hmO : IsModuleCompact (m * O - O * m) := by
    have h := (Ω.symm.transport_isModuleCompact_iff _).2
      (pR.commutator_m OR inputs.first_mem)
    simpa only [HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_mul,
      hfirst] using h
  have hnR : IsModuleCompact (n * RL - RL * n) := by
    have h := (Ω.symm.transport_isModuleCompact_iff _).2
      (pR.commutator_n R inputs.connection_mem)
    simpa only [HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_mul] using h
  have hmcreation (u : InteriorModuleTensor (E := E) d.representation) :
      IsModuleCompact (m.comp (moduleCreationMap e.representation u)) := by
    let C_u : AdjointableMap D (LeftTensor (E := E) d.representation e.representation)
        (LeftTensor (E := E) d.representation e.representation) :=
      (moduleCreationMap e.representation u).comp (moduleCreationMap e.representation u).adjoint
    have hC_u : Ω.transport C_u ∈ E₁ := hthird u
    have h := (Ω.symm.transport_isModuleCompact_iff _).2 (pR.first_ideal _ hC_u)
    have hsquare : IsModuleCompact (m * C_u) := by
      change IsModuleCompact (Ω.symm.transport (mR * Ω.transport C_u)) at h
      rw [HilbertModuleEquiv.transport_mul, Ω.transport_symm] at h
      exact h
    exact weightedCreation_isModuleCompact_of_square e.representation m hmsa u hsquare
  -- Compose the two primitive signed creation laws directly. No whole
  -- first-pair cycle has to be expanded to recover these same two fields.
  have hRsigned : IsSignedModuleConnection c.grading
      (rightRepresentation d.representation e.representation) T R :=
    ⟨hRconnection.creation_defect, hRconnection.creation_adjoint_defect⟩
  have hTsigned : IsSignedModuleConnection d.grading e.representation e.operator T :=
    ⟨hTconnection.creation_defect, hTconnection.creation_adjoint_defect⟩
  have hsigned : IsSignedModuleConnection J e.representation e.operator RL :=
    composed_isSignedModuleConnection d.representation e.representation c.grading d.grading
      d.representation_graded R T e.operator hRsigned hTsigned
  have hw : IsSignedModuleConnection J e.representation e.operator (m * O + n * RL) :=
    weighted_partition_isSignedModuleConnection J e.representation e.operator O RL m n
      hsigned hesa hOsa hRLsa hmsa hn hpart hmO hnR hmcreation
  have hproduct : kasparovTechnicalProductOperator (c := c) (d := secondPairCycle d e T hT) R p = mR * OR + nR * R := rfl
  have heq : Ω.symm.transport (kasparovTechnicalProductOperator (c := c) (d := secondPairCycle d e T hT) R p) = m * O + n * RL := by
    rw [hproduct, HilbertModuleEquiv.transport_add, HilbertModuleEquiv.transport_mul,
      HilbertModuleEquiv.transport_mul, hfirst]
  rw [heq]
  exact IsSignedModuleConnection.gradedKasparovConnection
    (B := C) (C := D) (E := InteriorModuleTensor (E := E) d.representation) (F := G)
    (Γ := Γ) (A := A) (α := α) (β := γ) (γ := χ)
    (δA := δA) (δB := δC) (δC := δD) (G := m * O + n * RL)
    (firstPairCycle c d Q hQ) e hw

include inputs in
set_option maxHeartbeats 1200000 in
/-- Once the concrete partition is constructed, the same actual operator
satisfies both complete product criteria. The first-pair criterion uses
its genuine localized positive lift, not a tensor-compact shortcut. -/
theorem weighted_operator_isProduct_onBothSides
    (hQproduct : IsGradedKasparovProductOperator c d Q)
    (hTproduct : IsGradedKasparovProductOperator d e T)
    (hcsa : IsSelfAdjoint c.operator) (hQsa : IsSelfAdjoint Q)
    (hRsa : IsSelfAdjoint R) (hesa : IsSelfAdjoint e.operator)
    (hRodd : (gradedKasparovTensorGrading c (secondPairCycle d e T hT)).IsOdd
      (gradedKasparovTensorGrading c (secondPairCycle d e T hT)) R)
    (hRconnection : GradedKasparovConnection c (secondPairCycle d e T hT) R)
    (hQΔ : pairLift d.representation e.representation Q ∈ Δ)
    (hresidual : tripleResidual d e Q R ∈ E₂)
    (hpair : ∀ K : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation), IsModuleCompact K →
        (hilbertEquiv d.representation e.representation).transport
          (interiorModuleTensorOperator e.representation K) ∈ E₁)
    (hthird : ∀ u : InteriorModuleTensor (E := E) d.representation,
      (hilbertEquiv d.representation e.representation).transport
        ((moduleCreationMap e.representation u).comp (moduleCreationMap e.representation u).adjoint) ∈ E₁) :
    IsGradedKasparovProductOperator c (secondPairCycle d e T hT)
      (kasparovTechnicalProductOperator R p) ∧
    IsGradedKasparovProductOperator (firstPairCycle c d Q hQ) e
      ((hilbertEquiv d.representation e.representation).symm.transport
        (kasparovTechnicalProductOperator (c := c) (d := secondPairCycle d e T hT) R p)) := by
  let Ω := hilbertEquiv (E := E) d.representation e.representation
  let JR : GradedHilbertModule δD (RightTensor (E := E) d.representation e.representation) :=
    gradedKasparovTensorGrading c (secondPairCycle d e T hT)
  let UR : EquivariantHilbertModule χ (RightTensor (E := E) d.representation e.representation) :=
    gradedKasparovTensorAction c (secondPairCycle d e T hT)
  let pR : KasparovTechnicalPartition JR UR E₁ E₂ Δ f := p
  let K : AdjointableMap D (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation) := kasparovTechnicalProductOperator (c := c) (d := secondPairCycle d e T hT) R p
  let KL : AdjointableMap D (LeftTensor (E := E) d.representation e.representation)
      (LeftTensor (E := E) d.representation e.representation) := Ω.symm.transport K
  let QL : AdjointableMap D (LeftTensor (E := E) d.representation e.representation)
      (LeftTensor (E := E) d.representation e.representation) := interiorModuleTensorOperator e.representation Q
  let Q₃ : AdjointableMap D (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation) := Ω.transport QL
  let ρR : A →⋆ₙₐ[ℂ] AdjointableMap D
      (RightTensor (E := E) d.representation e.representation)
      (RightTensor (E := E) d.representation e.representation) :=
    gradedKasparovTensorRepresentation c (secondPairCycle d e T hT)
  have hright : IsGradedKasparovProductOperator c (secondPairCycle d e T hT) K :=
    inputs.isGradedProduct pR hcsa hRsa hRodd hRconnection
  have hleftConditions : GradedKasparovTensorOperatorConditions (firstPairCycle c d Q hQ) e KL :=
    rightTriple_tensorConditions_onLeft c d e Q hQ T hT K hright.cycleConditions
  have hleftConnection : GradedKasparovConnection (firstPairCycle c d Q hQ) e KL :=
    weighted_connection_onLeft c d e Q hQ T hT R pR inputs hcsa hRsa hesa
      hRconnection hTproduct.connection hthird
  have hQ₃Δ : Q₃ ∈ Δ := hQΔ
  have hcomparisonResidual : Q₃ * R + R * Q₃ - (Q₃ * R + R * Q₃)⁺ ∈ E₂ := hresidual
  have hweighted :=
    weighted_firstPairPositivity c d e Q T hT R pR inputs hQproduct hQΔ hpair
  refine ⟨hright, {
    cycleConditions := hleftConditions
    connection := hleftConnection
    positivity := ?_ }⟩
  intro a
  let ρL : AdjointableMap D (LeftTensor (E := E) d.representation e.representation)
      (LeftTensor (E := E) d.representation e.representation) :=
    interiorModuleTensorOperator e.representation (interiorModuleTensorOperator d.representation (c.representation a))
  have hQliftSA : IsSelfAdjoint Q₃ := by
    change star (Ω.transport (interiorModuleTensorOperatorHom e.representation Q)) = _
    rw [← HilbertModuleEquiv.transport_star, ← map_star, hQsa.star_eq]
    rfl
  have hpos : IsPositiveModuloModuleCompact (ρR a * (Q₃ * K + K * Q₃) * star (ρR a)) :=
    weightedTechnicalProduct_comparison_positive_of_posPart_residual
      (G := R) (R := Q₃) (E₁ := E₁) (E₂ := E₂) (Δ := Δ) (f := f) c
      (secondPairCycle d e T hT) inputs pR hQ₃Δ hQliftSA hRsa hcomparisonResidual hweighted a
  have hρ : Ω.symm.transport (ρR a) = ρL := by
    have h := congrArg Ω.symm.transport
      (hilbertEquiv_transport_operator d.representation e.representation (c.representation a))
    exact h.symm.trans (Ω.transport_symm ρL)
  have hQ : Ω.symm.transport Q₃ = QL := Ω.transport_symm QL
  have h := hpos.transport Ω.symm
  have heq : Ω.symm.transport (ρR a * (Q₃ * K + K * Q₃) * star (ρR a)) =
      ρL * (QL * KL + KL * QL) * star ρL := by
    rw [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_mul,
      HilbertModuleEquiv.transport_add, HilbertModuleEquiv.transport_mul,
      HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_star, hρ, hQ]
  rw [heq] at h
  change IsPositiveModuloModuleCompact (ρL * (QL * KL + KL * QL) * star ρL)
  exact h

end BC4lean.KKTheory.KasparovTriple
