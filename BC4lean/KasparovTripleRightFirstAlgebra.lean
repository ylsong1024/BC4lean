import BC4lean.KasparovTripleSandwichAlgebra

/-! # The actual right-coordinate triple first algebra

The concrete three-family sandwich algebra is transported through the genuine
interior tensor associator. Its closedness, countable two-sided approximate
unit, grading, action, and ordinary normalizers follow from the corresponding
left-coordinate constructions. The first-factor sandwich algebra, first-pair
compact tensors, and third-factor creation squares belong to the transported
algebra. No tensor of a compact operator is asserted to be compact.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovTriple

open Filter TopologicalSpace
open scoped Topology
open InteriorModuleTensorAssociator

variable {B C D E F G : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Dᵐᵒᵖ G] [CStarModule Dᵐᵒᵖ G]
  [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
  (ψ : C →⋆ₙₐ[ℂ] AdjointableMap D G G)
  (S₂ : AdjointableMap C F F) (S₃ : AdjointableMap D G G)
  (S₂₃ : AdjointableMap D (InteriorModuleTensor (E := F) ψ)
    (InteriorModuleTensor (E := F) ψ))

/-- The actual enlarged first algebra in the right association. -/
def rightCoordinateFirstAlgebra : NonUnitalStarSubalgebra ℂ
    (AdjointableMap D (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ)) :=
  (normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃).comap
    (hilbertEquiv (E := E) φ ψ).symm.transportStarAlgEquiv.toNonUnitalStarAlgHom

@[simp] theorem mem_rightCoordinateFirstAlgebra
    (T : AdjointableMap D (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ)) :
    T ∈ rightCoordinateFirstAlgebra φ ψ S₂ S₃ S₂₃ ↔
      (hilbertEquiv φ ψ).symm.transport T ∈ normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃ :=
  Iff.rfl

@[simp] theorem transport_mem_rightCoordinateFirstAlgebra
    (T : AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ)) :
    (hilbertEquiv φ ψ).transport T ∈ rightCoordinateFirstAlgebra φ ψ S₂ S₃ S₂₃ ↔
      T ∈ normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃ := by
  rw [mem_rightCoordinateFirstAlgebra, HilbertModuleEquiv.transport_symm]

instance rightCoordinateFirstAlgebra_isClosed :
    IsClosed (rightCoordinateFirstAlgebra (E := E) φ ψ S₂ S₃ S₂₃ :
      Set (AdjointableMap D (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ))) := by
  let ρ := (hilbertEquiv (E := E) φ ψ).symm.transportStarAlgEquiv
  exact (normalizerFirstAlgebra_isClosed φ ψ S₂ S₃ S₂₃).preimage
    (NonUnitalStarAlgHom.isometry ρ ρ.injective).continuous

/-- Transport of actual terms of the left-coordinate approximate unit. -/
def rightCoordinateFirstAlgebraApproximateUnit
    (q : ℕ → normalizerFirstAlgebra (E := E) φ ψ S₂ S₃ S₂₃) :
    ℕ → rightCoordinateFirstAlgebra (E := E) φ ψ S₂ S₃ S₂₃ := by
  intro n
  let Ω := hilbertEquiv (E := E) φ ψ
  refine ⟨Ω.transport
    (q n : AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ)), ?_⟩
  change Ω.symm.transport (Ω.transport
    (q n : AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ))) ∈
      normalizerFirstAlgebra (E := E) φ ψ S₂ S₃ S₂₃
  rw [HilbertModuleEquiv.transport_symm]
  exact (q n).property

@[simp] theorem rightCoordinateFirstAlgebraApproximateUnit_coe
    (q : ℕ → normalizerFirstAlgebra (E := E) φ ψ S₂ S₃ S₂₃) (n : ℕ) :
    (rightCoordinateFirstAlgebraApproximateUnit φ ψ S₂ S₃ S₂₃ q n :
      AdjointableMap D (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ)) =
      (hilbertEquiv φ ψ).transport (q n) := rfl

/-- Genuine two-sided norm convergence is preserved by the actual
isometric star equivalence, including the subtype topology. -/
theorem rightCoordinateFirstAlgebraApproximateUnit_tendsto
    (q : ℕ → normalizerFirstAlgebra (E := E) φ ψ S₂ S₃ S₂₃)
    (hqleft : ∀ T, Tendsto (fun n => T * q n) atTop (𝓝 T))
    (hqright : ∀ T, Tendsto (fun n => q n * T) atTop (𝓝 T)) :
    (∀ T, Tendsto (fun n => T * rightCoordinateFirstAlgebraApproximateUnit φ ψ S₂ S₃ S₂₃ q n)
      atTop (𝓝 T)) ∧
    (∀ T, Tendsto (fun n => rightCoordinateFirstAlgebraApproximateUnit φ ψ S₂ S₃ S₂₃ q n * T)
      atTop (𝓝 T)) := by
  let Ω := hilbertEquiv (E := E) φ ψ
  have hΩcont : Continuous Ω.transport :=
    (NonUnitalStarAlgHom.isometry Ω.transportStarAlgEquiv
      Ω.transportStarAlgEquiv.injective).continuous
  constructor
  · intro T
    let TL : normalizerFirstAlgebra (E := E) φ ψ S₂ S₃ S₂₃ :=
      ⟨Ω.symm.transport T, T.property⟩
    have h := (hΩcont.tendsto (TL : _)).comp
      ((continuous_subtype_val.tendsto TL).comp (hqleft TL))
    change Tendsto (fun n => Ω.transport
      (Ω.symm.transport
        (T : AdjointableMap D (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ)) *
          (q n : AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ))))
      atTop (𝓝 (Ω.transport (Ω.symm.transport
        (T : AdjointableMap D (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ))))) at h
    rw [HilbertModuleEquiv.transport_symm_symm] at h
    apply tendsto_subtype_rng.mpr
    refine Filter.Tendsto.congr (fun n => ?_) h
    change Ω.transport
      (Ω.symm.transport
        (T : AdjointableMap D (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ)) *
          (q n : AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ))) =
        (T : AdjointableMap D (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ)) *
          Ω.transport (q n : AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ))
    rw [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_symm_symm]
  · intro T
    let TL : normalizerFirstAlgebra (E := E) φ ψ S₂ S₃ S₂₃ :=
      ⟨Ω.symm.transport T, T.property⟩
    have h := (hΩcont.tendsto (TL : _)).comp
      ((continuous_subtype_val.tendsto TL).comp (hqright TL))
    change Tendsto (fun n => Ω.transport
      ((q n : AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ)) *
        Ω.symm.transport
          (T : AdjointableMap D (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ))))
      atTop (𝓝 (Ω.transport (Ω.symm.transport
        (T : AdjointableMap D (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ))))) at h
    rw [HilbertModuleEquiv.transport_symm_symm] at h
    apply tendsto_subtype_rng.mpr
    refine Filter.Tendsto.congr (fun n => ?_) h
    change Ω.transport
      ((q n : AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ)) *
        Ω.symm.transport
          (T : AdjointableMap D (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ))) =
        Ω.transport (q n : AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ)) *
          (T : AdjointableMap D (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ))
    rw [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_symm_symm]

/-- The actual right-coordinate algebra has a countable two-sided AU
derived from countable generation of the original first module. -/
theorem exists_rightCoordinateFirstAlgebra_approximateUnit [SeparableSpace B]
    (hE : IsCountablyGeneratedModule B E) :
    ∃ q : ℕ → rightCoordinateFirstAlgebra (E := E) φ ψ S₂ S₃ S₂₃,
      (∀ T, Tendsto (fun n => T * q n) atTop (𝓝 T)) ∧
        (∀ T, Tendsto (fun n => q n * T) atTop (𝓝 T)) := by
  obtain ⟨q, hqleft, hqright⟩ := exists_normalizerFirstAlgebra_approximateUnit
    φ ψ S₂ S₃ S₂₃ hE
  exact ⟨rightCoordinateFirstAlgebraApproximateUnit φ ψ S₂ S₃ S₂₃ q,
    rightCoordinateFirstAlgebraApproximateUnit_tendsto φ ψ S₂ S₃ S₂₃ q hqleft hqright⟩

/-- The first-factor sandwich algebra of the right association belongs
to the concrete right-coordinate enlargement. -/
theorem firstProductAlgebra_le_rightCoordinateFirstAlgebra :
    firstProductAlgebra (E := E) (rightRepresentation φ ψ) S₂₃ ≤
      rightCoordinateFirstAlgebra φ ψ S₂ S₃ S₂₃ := by
  intro T hT
  change (hilbertEquiv φ ψ).symm.transport T ∈ normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃
  apply enlargedFirstAlgebra_le_normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃
  apply rightSandwichAlgebra_le_enlargedFirstAlgebra φ ψ S₃ S₂₃
  change (hilbertEquiv (E := E) φ ψ).transport
    ((hilbertEquiv (E := E) φ ψ).symm.transport T) ∈
      firstProductAlgebra (E := E) (rightRepresentation φ ψ) S₂₃
  simpa only [HilbertModuleEquiv.transport_symm_symm] using hT

/-- Genuine first-pair compact tensors belong to E₁; no compactness of
their tensor extensions is presumed. -/
theorem pairTensorCompact_mem_rightCoordinateFirstAlgebra
    {K : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ)}
    (hK : IsModuleCompact K) :
    (hilbertEquiv φ ψ).transport (interiorModuleTensorOperator ψ K) ∈
      rightCoordinateFirstAlgebra φ ψ S₂ S₃ S₂₃ := by
  apply (transport_mem_rightCoordinateFirstAlgebra φ ψ S₂ S₃ S₂₃ _).mpr
  exact firstAlgebra_le_normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃
    (pairTensorCompact_mem_firstAlgebra φ ψ hK)

/-- Third-factor creation squares belong to the left sandwich family
and hence to the transported actual E₁. -/
theorem thirdCreationSquare_mem_rightCoordinateFirstAlgebra
    (u : InteriorModuleTensor (E := E) φ) :
    (hilbertEquiv φ ψ).transport
      ((moduleCreationMap ψ u).comp (moduleCreationMap ψ u).adjoint) ∈
        rightCoordinateFirstAlgebra φ ψ S₂ S₃ S₂₃ := by
  apply (transport_mem_rightCoordinateFirstAlgebra φ ψ S₂ S₃ S₂₃ _).mpr
  apply enlargedFirstAlgebra_le_normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃
  apply leftSandwichAlgebra_le_enlargedFirstAlgebra φ ψ S₃ S₂₃
  exact creationSandwich_one_mem_firstProductAlgebra ψ S₃ u u

/-- Ordinary commutator normalizers transport through the actual
associator, with the order and signs of both products retained. -/
theorem normalizes_rightCoordinateFirstAlgebra
    (X : AdjointableMap D (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ))
    (hX : ∀ T ∈ normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃,
      (hilbertEquiv φ ψ).symm.transport X * T - T * (hilbertEquiv φ ψ).symm.transport X ∈
        normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃) :
    ∀ T ∈ rightCoordinateFirstAlgebra φ ψ S₂ S₃ S₂₃,
      X * T - T * X ∈ rightCoordinateFirstAlgebra φ ψ S₂ S₃ S₂₃ := by
  intro T hT
  change (hilbertEquiv φ ψ).symm.transport (X * T - T * X) ∈
    normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃
  rw [HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_mul,
    HilbertModuleEquiv.transport_mul]
  exact hX _ hT

section Grading
variable {δD : CStarGrading D}

/-- Actual grading compatibility transports the independently proved
grading stability of the concrete left algebra. -/
theorem grading_preserves_rightCoordinateFirstAlgebra
    (JL : GradedHilbertModule δD (LeftTensor (E := E) φ ψ))
    (JR : GradedHilbertModule δD (RightTensor (E := E) φ ψ))
    (hΩ : ∀ x, hilbertEquiv φ ψ (JL.grading x) = JR.grading (hilbertEquiv φ ψ x))
    (hL : ∀ T ∈ normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃,
      JL.conjugateOperator T ∈ normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃) :
    ∀ T ∈ rightCoordinateFirstAlgebra φ ψ S₂ S₃ S₂₃,
      JR.conjugateOperator T ∈ rightCoordinateFirstAlgebra φ ψ S₂ S₃ S₂₃ := by
  intro T hT
  let Ω := hilbertEquiv (E := E) φ ψ
  have heq : Ω.symm.transport (JR.conjugateOperator T) =
      JL.conjugateOperator (Ω.symm.transport T) := by
    apply Ω.transportStarAlgEquiv.injective
    change Ω.transport (Ω.symm.transport (JR.conjugateOperator T)) =
      Ω.transport (JL.conjugateOperator (Ω.symm.transport T))
    rw [HilbertModuleEquiv.transport_symm_symm,
      HilbertModuleEquiv.transport_conjugateGrading Ω JL JR hΩ,
      HilbertModuleEquiv.transport_symm_symm]
  change Ω.symm.transport (JR.conjugateOperator T) ∈ normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃
  rw [heq]
  exact hL _ hT

end Grading

section Action
variable {Γ : Type*} [Group Γ] {α : CStarAlgebraAction Γ D}

/-- The genuine associator intertwines actions, so independently proved
left-coordinate action invariance yields actual right invariance. -/
theorem action_preserves_rightCoordinateFirstAlgebra
    (UL : EquivariantHilbertModule α (LeftTensor (E := E) φ ψ))
    (UR : EquivariantHilbertModule α (RightTensor (E := E) φ ψ))
    (hΩ : ∀ g x, hilbertEquiv φ ψ (UL.action g x) = UR.action g (hilbertEquiv φ ψ x))
    (hL : ∀ g T, T ∈ normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃ →
      UL.conjugateOperator g T ∈ normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃)
    (g : Γ) :
    ∀ T ∈ rightCoordinateFirstAlgebra φ ψ S₂ S₃ S₂₃,
      UR.conjugateOperator g T ∈ rightCoordinateFirstAlgebra φ ψ S₂ S₃ S₂₃ := by
  intro T hT
  let Ω := hilbertEquiv (E := E) φ ψ
  have heq : Ω.symm.transport (UR.conjugateOperator g T) =
      UL.conjugateOperator g (Ω.symm.transport T) := by
    apply Ω.transportStarAlgEquiv.injective
    change Ω.transport (Ω.symm.transport (UR.conjugateOperator g T)) =
      Ω.transport (UL.conjugateOperator g (Ω.symm.transport T))
    rw [HilbertModuleEquiv.transport_symm_symm,
      HilbertModuleEquiv.transport_conjugateAction Ω UL UR hΩ,
      HilbertModuleEquiv.transport_symm_symm]
  change Ω.symm.transport (UR.conjugateOperator g T) ∈ normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃
  rw [heq]
  exact hL g _ hT

end Action
end BC4lean.KKTheory.KasparovTriple
