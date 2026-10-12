import BC4lean.KasparovProductDefectAlgebra
import BC4lean.KasparovDiscreteTechnicalTheorem
import BC4lean.GradedKasparovNormalization

/-! # Constructing a genuine product for arbitrary input operators

The proof normalizes the two actual input cycles by localized compact
perturbations, constructs an actual homogeneous frame connection, proves
every source hypothesis for the concrete sandwich and defect algebras,
and invokes the constructed countable discrete technical partition.
The original first operator and its genuine connection anticommutator
remain in the test families. This proves positivity for the original
first operator. The coefficient approximate unit transfers all four
connection laws from the normalized second operator to the original one.

The statement is the actual operator product criterion on the actual
interior tensor. It does not assert uniqueness, descent or associativity.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter TopologicalSpace
open scoped Topology

variable {Γ A B C E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}

/-- The genuine coefficient-AU compactness lemma transfers each of the
four analytic connection laws from a locally normalized second cycle. -/
theorem gradedKasparovConnection_of_normalized_second
    (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F)
    {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)}
    (hR : GradedKasparovConnection c d.normalized R) : GradedKasparovConnection c d R := by
  let K := d.normalizedOperator - d.operator
  have hK (x : E) : IsModuleCompact ((moduleCreationMap d.representation x).comp K) :=
    moduleCreationMap_comp_isModuleCompact_of_local d.representation x K
      d.normalizedOperator_sub_locallyCompact d.normalizedOperator_sub_adjoint_locallyCompact
  have hKstar (x : E) : IsModuleCompact
      ((moduleCreationMap d.representation x).comp (star K)) :=
    moduleCreationMap_comp_isModuleCompact_of_local d.representation x (star K)
      d.normalizedOperator_sub_adjoint_locallyCompact
      (fun b => by simpa only [star_star] using d.normalizedOperator_sub_locallyCompact b)
  constructor
  · intro x hx
    have heq : (moduleCreationMap d.representation x).comp d.operator -
        R.comp (moduleCreationMap d.representation x) =
        ((moduleCreationMap d.representation x).comp d.normalized.operator -
          R.comp (moduleCreationMap d.representation x)) -
            (moduleCreationMap d.representation x).comp K := by
      rw [show d.normalized.operator = d.normalizedOperator from rfl]
      ext y
      simp only [K, AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply, map_sub]
      abel
    rw [heq]
    exact (hR.even x hx).sub (hK x)
  · intro x hx
    have heq : (moduleCreationMap d.representation x).comp (star d.operator) -
        (star R).comp (moduleCreationMap d.representation x) =
        ((moduleCreationMap d.representation x).comp (star d.normalized.operator) -
          (star R).comp (moduleCreationMap d.representation x)) -
            (moduleCreationMap d.representation x).comp (star K) := by
      rw [show star K = star d.normalized.operator - star d.operator from star_sub _ _]
      ext y
      simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply, map_sub]
      abel
    rw [heq]
    exact (hR.even_adjoint x hx).sub (hKstar x)
  · intro x hx
    have heq : (moduleCreationMap d.representation x).comp d.operator +
        R.comp (moduleCreationMap d.representation x) =
        ((moduleCreationMap d.representation x).comp d.normalized.operator +
          R.comp (moduleCreationMap d.representation x)) -
            (moduleCreationMap d.representation x).comp K := by
      rw [show d.normalized.operator = d.normalizedOperator from rfl]
      ext y
      simp only [K, AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
        AdjointableMap.coe_add_apply, map_sub]
      abel
    rw [heq]
    exact (hR.odd x hx).sub (hK x)
  · intro x hx
    have heq : (moduleCreationMap d.representation x).comp (star d.operator) +
        (star R).comp (moduleCreationMap d.representation x) =
        ((moduleCreationMap d.representation x).comp (star d.normalized.operator) +
          (star R).comp (moduleCreationMap d.representation x)) -
            (moduleCreationMap d.representation x).comp (star K) := by
      rw [show star K = star d.normalized.operator - star d.operator from star_sub _ _]
      ext y
      simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
        AdjointableMap.coe_add_apply, map_sub]
      abel
    rw [heq]
    exact (hR.odd_adjoint x hx).sub (hKstar x)

/-- In the chapter's separable algebra and countable discrete group
setting, arbitrary genuine graded cycles have an actual product operator.
Every technical-theorem source hypothesis is constructed and proved here. -/
theorem exists_actualGradedKasparovProductOperator
    [SeparableSpace A] [SeparableSpace B] [SeparableSpace C] [Countable Γ]
    (c : GradedKasparovCycle α β δA δB E) (d : GradedKasparovCycle β γ δB δC F) :
    ∃ R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation), IsGradedKasparovProductOperator c d R := by
  classical
  let cₙ := c.normalized
  let dₙ := d.normalized
  obtain ⟨G, hGodd, hGsa, _, hG⟩ :=
    exists_odd_selfadjoint_contractive_gradedKasparovConnection cₙ dₙ
      d.normalized_selfadjoint d.normalized_norm_le_one
  have hGoriginalFirst : GradedKasparovConnection c dₙ G := {
    even := fun x hx => hG.even x hx
    even_adjoint := fun x hx => hG.even_adjoint x hx
    odd := fun x hx => hG.odd x hx
    odd_adjoint := fun x hx => hG.odd_adjoint x hx
  }
  let E₁ := firstProductAlgebra (E := E) dₙ.representation dₙ.operator
  let E₂n := productSecondDefectAlgebra cₙ dₙ G
  let E₂o := productSecondDefectAlgebra c dₙ G
  let E₂ := generatedClosedStarAlgebra E₂n E₂o
  let Δ := productNormalizerTests cₙ dₙ G ∪ productNormalizerTests c dₙ G
  let f : ℕ → AdjointableMap C (InteriorModuleTensor (E := E) dₙ.representation)
      (InteriorModuleTensor (E := E) dₙ.representation) := fun _ => 0
  let J := gradedKasparovTensorGrading cₙ dₙ
  let U := gradedKasparovTensorAction cₙ dₙ
  let : IsClosed (E₁ :
      Set (AdjointableMap C (InteriorModuleTensor (E := E) dₙ.representation)
        (InteriorModuleTensor (E := E) dₙ.representation))) :=
    firstProductAlgebra_isClosed (E := E) dₙ.representation dₙ.operator
  let : IsClosed (E₂n :
      Set (AdjointableMap C (InteriorModuleTensor (E := E) dₙ.representation)
        (InteriorModuleTensor (E := E) dₙ.representation))) :=
    productSecondDefectAlgebra_isClosed cₙ dₙ G
  let : IsClosed (E₂o :
      Set (AdjointableMap C (InteriorModuleTensor (E := E) dₙ.representation)
        (InteriorModuleTensor (E := E) dₙ.representation))) :=
    productSecondDefectAlgebra_isClosed c dₙ G
  let : IsClosed (E₂ :
      Set (AdjointableMap C (InteriorModuleTensor (E := E) dₙ.representation)
        (InteriorModuleTensor (E := E) dₙ.representation))) :=
    generatedClosedStarAlgebra_isClosed E₂n E₂o
  obtain ⟨q₁, hq₁left, hq₁right⟩ :=
    exists_firstProductAlgebra_approximateUnit dₙ.representation dₙ.operator cₙ.countablyGenerated
  obtain ⟨q₂n, hq₂nleft, hq₂nright⟩ :=
    exists_productSecondDefectAlgebra_approximateUnit cₙ dₙ G
  obtain ⟨q₂o, hq₂oleft, hq₂oright⟩ :=
    exists_productSecondDefectAlgebra_approximateUnit c dₙ G
  obtain ⟨q₂, _, _, _, _, _, hq₂left, hq₂right⟩ :=
    exists_generatedClosedStarAlgebra_approximateUnit E₂n E₂o q₂n q₂o
      hq₂nleft hq₂nright hq₂oleft hq₂oright
  have h₂local : E₂ ≤ creationLocallyCompactAlgebra (E := E) dₙ.representation :=
    generatedClosedStarAlgebra_le E₂n E₂o _
      (creationLocallyCompactAlgebra_isClosed dₙ.representation)
      (productSecondDefectAlgebra_creationLocallyCompact cₙ dₙ G
        d.normalized_selfadjoint hGsa hG)
      (productSecondDefectAlgebra_creationLocallyCompact c dₙ G
        d.normalized_selfadjoint hGsa hGoriginalFirst)
  have hproducts : ∀ a ∈ E₁, ∀ b ∈ E₂, IsModuleCompact (a * b) :=
    fun a ha b hb => (firstProductAlgebra_products_compact dₙ.representation dₙ.operator ha (h₂local hb)).1
  have hgrade₂ : ∀ a ∈ E₂, J.conjugateOperator a ∈ E₂ :=
    maps_generatedClosedStarAlgebra E₂n E₂o J.conjugateOperatorStarAlgEquiv
      (grading_preserves_productSecondDefectAlgebra cₙ dₙ G)
      (grading_preserves_productSecondDefectAlgebra c dₙ G)
  have hnormal : ∀ T ∈ Δ, ∀ a ∈ E₁, T * a - a * T ∈ E₁ := by
    intro T hT
    rcases hT with hT | hT
    · exact productNormalizerTests_normalize_firstProductAlgebra cₙ dₙ G
        d.normalized_selfadjoint hGsa hG T hT
    · exact productNormalizerTests_normalize_firstProductAlgebra c dₙ G
        d.normalized_selfadjoint hGsa hGoriginalFirst T hT
  obtain ⟨p⟩ := exists_kasparovDiscreteTechnicalPartition
    (cₙ.countablyGenerated.interiorTensor dₙ.countablyGenerated dₙ.representation)
    J U (gradedKasparovTensorAction_preservesGrading cₙ dₙ) E₁ E₂ q₁ q₂
    hq₁left hq₁right hq₂left hq₂right hproducts
    (action_preserves_firstProductAlgebra cₙ dₙ d.normalized_selfadjoint)
    (grading_preserves_firstProductAlgebra dₙ.representation cₙ.grading dₙ.grading
      dₙ.representation_graded dₙ.operator dₙ.operator_odd)
    hgrade₂ Δ ((productNormalizerTests_isSeparable cₙ dₙ G).union
      (productNormalizerTests_isSeparable c dₙ G)) hnormal f
    ⟨0, fun _ => by
      change ‖(0 : AdjointableMap C (InteriorModuleTensor (E := E) dₙ.representation)
        (InteriorModuleTensor (E := E) dₙ.representation))‖ ≤ 0
      simpa only [norm_zero] using (le_rfl : (0 : ℝ) ≤ 0)⟩ (fun _ a _ => by
        change IsModuleCompact (a * 0) ∧ IsModuleCompact (0 * a)
        constructor
        · simpa only [mul_zero] using
            (IsModuleCompact.zero : IsModuleCompact
              (0 : AdjointableMap C (InteriorModuleTensor (E := E) dₙ.representation)
                (InteriorModuleTensor (E := E) dₙ.representation)))
        · simpa only [zero_mul] using
            (IsModuleCompact.zero : IsModuleCompact
              (0 : AdjointableMap C (InteriorModuleTensor (E := E) dₙ.representation)
                (InteriorModuleTensor (E := E) dₙ.representation))))
  have hn := actualKasparovProductTechnicalInputs cₙ dₙ G
  have hE₂n : E₂n ≤ E₂ := le_generatedClosedStarAlgebra_left E₂n E₂o
  have inputs : KasparovProductTechnicalInputs cₙ dₙ G E₁ E₂ Δ := {
    first_mem := Or.inl hn.first_mem
    connection_mem := Or.inl hn.connection_mem
    representation_mem a := Or.inl (hn.representation_mem a)
    creation_square_mem := hn.creation_square_mem
    first_square_mem := hn.first_square_mem
    first_commutator_mem := hn.first_commutator_mem
    first_equivariance_mem := hn.first_equivariance_mem
    second_square_mem := hE₂n hn.second_square_mem
    second_commutator_mem a := hE₂n (hn.second_commutator_mem a)
    second_equivariance_mem g := hE₂n (hn.second_equivariance_mem g)
    anticommutator_mem := hE₂n hn.anticommutator_mem
  }
  let R := kasparovTechnicalProductOperator G p
  have hRn : IsGradedKasparovProductOperator cₙ dₙ R :=
    inputs.isGradedProduct p c.normalized_selfadjoint hGsa hGodd hG
  let O := interiorModuleTensorOperator dₙ.representation c.operator
  have hO : O ∈ Δ := Or.inr (Or.inl (Or.inl rfl))
  have hOG : O * G + G * O ∈ E₂ :=
    le_generatedClosedStarAlgebra_right E₂n E₂o
      (actualKasparovProductTechnicalInputs c dₙ G).anticommutator_mem
  have hK (b : A) : (O - interiorModuleTensorOperator dₙ.representation cₙ.operator) *
      gradedKasparovTensorRepresentation cₙ dₙ b ∈ E₁ := by
    have hc := (c.normalizedOperator_sub_locallyCompact b).neg
    have heq : -((c.normalizedOperator - c.operator) * c.representation b) =
        (c.operator - cₙ.operator) * c.representation b := by
      change -((c.normalizedOperator - c.operator) * c.representation b) =
        (c.operator - c.normalizedOperator) * c.representation b
      noncomm_ring
    rw [heq] at hc
    have ht := tensorCompact_mem_firstProductAlgebra dₙ.representation dₙ.operator hc
    change interiorModuleTensorOperatorHom dₙ.representation
      ((c.operator - cₙ.operator) * c.representation b) ∈ E₁ at ht
    have hρ : cₙ.representation b = c.representation b := rfl
    simp only [O, gradedKasparovTensorRepresentation_apply, hρ]
    simpa only [map_sub, map_mul, interiorModuleTensorOperatorHom_apply] using ht
  refine ⟨R, ?_⟩
  constructor
  · exact {
      operator_odd := hRn.cycleConditions.operator_odd
      selfadjoint_mod_compact := hRn.cycleConditions.selfadjoint_mod_compact
      square_mod_compact := hRn.cycleConditions.square_mod_compact
      commutator_compact := hRn.cycleConditions.commutator_compact
      equivariance_mod_compact := hRn.cycleConditions.equivariance_mod_compact
    }
  · apply gradedKasparovConnection_of_normalized_second c d
    exact {
      even := fun x hx => hRn.connection.even x hx
      even_adjoint := fun x hx => hRn.connection.even_adjoint x hx
      odd := fun x hx => hRn.connection.odd x hx
      odd_adjoint := fun x hx => hRn.connection.odd_adjoint x hx
    }
  · intro a
    exact inputs.weighted_positivity_of_firstReplacement p O hO hOG hK a

end BC4lean.KKTheory
