import BC4lean.KasparovTripleFirstAlgebra
import BC4lean.InteriorModuleTensorAssociatorCompatibility

/-! # The actual sandwich enlargement of the triple first algebra

The left first-pair sandwich algebra and the associator pullback of the
right first-factor sandwich algebra generate an actual closed star algebra.
A single compact AU of the original first module is a two-sided norm AU for
both families and hence for their generated closure. The three compact
families of `KasparovTriple.firstAlgebra` are included in this enlargement.

Grading stability is derived from the two middle operators' actual oddness
and the genuine grading compatibility of the associator. Action stability
is transported from concrete first-product algebra controls using the
genuine module actions. Ordinary normalizer propagation is exposed as a
generator lemma; this source does not claim the outstanding cross-normalizer
identities or any associativity result.
-/

noncomputable section
namespace BC4lean.KKTheory

open Filter
open scoped Topology

section UnitaryCompatibility
variable {B X Y : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul Bᵐᵒᵖ X] [CStarModule Bᵐᵒᵖ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [SMul Bᵐᵒᵖ Y] [CStarModule Bᵐᵒᵖ Y]

/-- A genuine grading-intertwining module unitary intertwines grading
conjugation on actual adjointable operators. -/
theorem HilbertModuleEquiv.transport_conjugateGrading
    {B X Y : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul Bᵐᵒᵖ X] [CStarModule Bᵐᵒᵖ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [SMul Bᵐᵒᵖ Y] [CStarModule Bᵐᵒᵖ Y]
    (Ω : HilbertModuleEquiv B X Y) {β : CStarGrading B}
    (J : GradedHilbertModule β X) (K : GradedHilbertModule β Y)
    (hΩ : ∀ x, Ω (J.grading x) = K.grading (Ω x))
    (T : AdjointableMap B X X) :
    Ω.transport (J.conjugateOperator T) = K.conjugateOperator (Ω.transport T) := by
  have hsymm (y : Y) : Ω.symm (K.grading y) = J.grading (Ω.symm y) := by
    apply Ω.injective
    rw [Ω.apply_symm_apply, hΩ, Ω.apply_symm_apply]
  ext y
  simp only [HilbertModuleEquiv.transport_apply,
    GradedHilbertModule.conjugateOperator_apply, hsymm, hΩ]

/-- A genuine action-intertwining module unitary transports the actual
semilinear conjugation action on adjointable operators. -/
theorem HilbertModuleEquiv.transport_conjugateAction
    {B X Y : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul Bᵐᵒᵖ X] [CStarModule Bᵐᵒᵖ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [SMul Bᵐᵒᵖ Y] [CStarModule Bᵐᵒᵖ Y]
    {Γ : Type*} [Group Γ] {α : CStarAlgebraAction Γ B}
    (Ω : HilbertModuleEquiv B X Y)
    (U : EquivariantHilbertModule α X) (V : EquivariantHilbertModule α Y)
    (hΩ : ∀ g x, Ω (U.action g x) = V.action g (Ω x))
    (g : Γ) (T : AdjointableMap B X X) :
    Ω.transport (U.conjugateOperator g T) = V.conjugateOperator g (Ω.transport T) := by
  have hsymm (h : Γ) (y : Y) : Ω.symm (V.action h y) = U.action h (Ω.symm y) := by
    apply Ω.injective
    rw [Ω.apply_symm_apply, hΩ, Ω.apply_symm_apply]
  ext y
  simp only [HilbertModuleEquiv.transport_apply,
    EquivariantHilbertModule.conjugateMap_apply, hsymm, hΩ]

end UnitaryCompatibility

section ApproximateUnitMultipliers
variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- Membership of both products with a genuine two-sided AU proves that
an ambient element multiplies the entire closed algebra on both sides. -/
theorem twoSidedMultiplier_of_approximateUnit
    (S : NonUnitalStarSubalgebra ℂ A) (hS : IsClosed (S : Set A))
    (q : ℕ → S)
    (hqleft : ∀ a : S, Tendsto (fun n => q n * a) atTop (𝓝 a))
    (hqright : ∀ a : S, Tendsto (fun n => a * q n) atTop (𝓝 a))
    (d : A) (hdleft : ∀ n, d * (q n : A) ∈ S) (hdright : ∀ n, (q n : A) * d ∈ S) :
    ∀ a ∈ S, d * a ∈ S ∧ a * d ∈ S := by
  intro a ha
  let x : S := ⟨a, ha⟩
  have hqa : Tendsto (fun n => (q n : A) * a) atTop (𝓝 a) :=
    (continuous_subtype_val.tendsto x).comp (hqleft x)
  have haq : Tendsto (fun n => a * (q n : A)) atTop (𝓝 a) :=
    (continuous_subtype_val.tendsto x).comp (hqright x)
  refine ⟨hS.mem_of_tendsto (tendsto_const_nhds.mul hqa) ?_,
    hS.mem_of_tendsto (haq.mul tendsto_const_nhds) ?_⟩
  · exact Eventually.of_forall fun n => by
      rw [← mul_assoc]
      exact S.mul_mem (hdleft n) ha
  · exact Eventually.of_forall fun n => by
      rw [mul_assoc]
      exact S.mul_mem ha (hdright n)

/-- The actual two-sided multiplier conclusion gives the ordinary
commutator normalizer required by the technical theorem. -/
theorem normalizes_of_approximateUnit_products
    (S : NonUnitalStarSubalgebra ℂ A) (hS : IsClosed (S : Set A))
    (q : ℕ → S)
    (hqleft : ∀ a : S, Tendsto (fun n => q n * a) atTop (𝓝 a))
    (hqright : ∀ a : S, Tendsto (fun n => a * q n) atTop (𝓝 a))
    (d : A) (hdleft : ∀ n, d * (q n : A) ∈ S) (hdright : ∀ n, (q n : A) * d ∈ S) :
    ∀ a ∈ S, d * a - a * d ∈ S := by
  intro a ha
  have h := twoSidedMultiplier_of_approximateUnit S hS q hqleft hqright d hdleft hdright a ha
  exact S.sub_mem h.1 h.2

end ApproximateUnitMultipliers

namespace KasparovTriple
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

/-- Sandwiches on the left-parenthesized triple tensor, based on the
first-pair module and a specified actual third-factor operator. -/
def leftSandwichAlgebra (S₃ : AdjointableMap D G G) : NonUnitalStarSubalgebra ℂ
    (AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ)) :=
  firstProductAlgebra (E := InteriorModuleTensor (E := E) φ) ψ S₃

/-- Pull back the genuine right-parenthesized sandwich algebra by the
actual associator, with the actual transported second-pair operator. -/
def rightSandwichAlgebra
    (S₂₃ : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ)) :
    NonUnitalStarSubalgebra ℂ
      (AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ)) :=
  (firstProductAlgebra (E := E) (rightRepresentation φ ψ) S₂₃).comap
    (hilbertEquiv (E := E) φ ψ).transportStarAlgEquiv.toNonUnitalStarAlgHom

theorem leftSandwichAlgebra_isClosed (S₃ : AdjointableMap D G G) :
    IsClosed (leftSandwichAlgebra (E := E) φ ψ S₃ : Set
      (AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ))) :=
  firstProductAlgebra_isClosed ψ S₃

theorem rightSandwichAlgebra_isClosed
    (S₂₃ : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ)) :
    IsClosed (rightSandwichAlgebra (E := E) φ ψ S₂₃ : Set
      (AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ))) := by
  let ρ := (hilbertEquiv (E := E) φ ψ).transportStarAlgEquiv
  exact (firstProductAlgebra_isClosed (rightRepresentation φ ψ) S₂₃).preimage
    (NonUnitalStarAlgHom.isometry ρ ρ.injective).continuous

/-- The concrete sandwich enlargement used for the first technical
algebra of an associativity construction. -/
def enlargedFirstAlgebra (S₃ : AdjointableMap D G G)
    (S₂₃ : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ)) :
    NonUnitalStarSubalgebra ℂ
      (AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ)) :=
  generatedClosedStarAlgebra (leftSandwichAlgebra φ ψ S₃) (rightSandwichAlgebra φ ψ S₂₃)

instance enlargedFirstAlgebra_isClosed (S₃ : AdjointableMap D G G)
    (S₂₃ : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ)) :
    IsClosed (enlargedFirstAlgebra (E := E) φ ψ S₃ S₂₃ : Set
      (AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ))) :=
  generatedClosedStarAlgebra_isClosed _ _

theorem leftSandwichAlgebra_le_enlargedFirstAlgebra (S₃ : AdjointableMap D G G)
    (S₂₃ : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ)) :
    leftSandwichAlgebra φ ψ S₃ ≤ enlargedFirstAlgebra (E := E) φ ψ S₃ S₂₃ :=
  le_generatedClosedStarAlgebra_left _ _

theorem rightSandwichAlgebra_le_enlargedFirstAlgebra (S₃ : AdjointableMap D G G)
    (S₂₃ : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ)) :
    rightSandwichAlgebra φ ψ S₂₃ ≤ enlargedFirstAlgebra (E := E) φ ψ S₃ S₂₃ :=
  le_generatedClosedStarAlgebra_right _ _

/-- Every original first compact tensor belongs to the actual pulled
back right sandwich algebra. -/
theorem doubleTensorCompact_mem_rightSandwichAlgebra
    (S₂₃ : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ))
    {T : AdjointableMap B E E} (hT : IsModuleCompact T) :
    doubleTensorOperator φ ψ T ∈ rightSandwichAlgebra φ ψ S₂₃ := by
  change (hilbertEquiv (E := E) φ ψ).transport (doubleTensorOperator φ ψ T) ∈
    firstProductAlgebra (E := E) (rightRepresentation φ ψ) S₂₃
  change (hilbertEquiv (E := E) φ ψ).transport
    (interiorModuleTensorOperator ψ (interiorModuleTensorOperator φ T)) ∈
      firstProductAlgebra (E := E) (rightRepresentation φ ψ) S₂₃
  rw [hilbertEquiv_transport_operator φ ψ T]
  exact tensorCompact_mem_firstProductAlgebra (rightRepresentation φ ψ) S₂₃ hT

/-- The actual enlargement contains first compact tensors, first-pair
compact tensors, and the genuine triple compact ideal. -/
theorem firstAlgebra_le_enlargedFirstAlgebra (S₃ : AdjointableMap D G G)
    (S₂₃ : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ)) :
    firstAlgebra (E := E) φ ψ ≤ enlargedFirstAlgebra φ ψ S₃ S₂₃ := by
  apply closedNonUnitalStarAdjoin_le _ _ (enlargedFirstAlgebra_isClosed φ ψ S₃ S₂₃)
  intro T hT
  rcases hT with (hT | hT) | hT
  · obtain ⟨K, hK, rfl⟩ := hT
    exact rightSandwichAlgebra_le_enlargedFirstAlgebra φ ψ S₃ S₂₃
      (doubleTensorCompact_mem_rightSandwichAlgebra φ ψ S₂₃ hK)
  · obtain ⟨K, hK, rfl⟩ := hT
    exact leftSandwichAlgebra_le_enlargedFirstAlgebra φ ψ S₃ S₂₃
      (tensorCompact_mem_firstProductAlgebra ψ S₃ hK)
  · exact leftSandwichAlgebra_le_enlargedFirstAlgebra φ ψ S₃ S₂₃
      (moduleCompact_le_firstProductAlgebra ψ S₃ hT)

/-- One original first-module strong selfadjoint contraction sequence
gives genuine two-sided norm convergence on both sandwich families. -/
theorem enlargedFirstAlgebra_tendsto_doubleTensorApproximateUnit
    (S₃ : AdjointableMap D G G)
    (S₂₃ : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ))
    (q : ℕ → AdjointableMap B E E) (hqnorm : ∀ n, ‖q n‖ ≤ 1)
    (hqself : ∀ n, (q n).adjoint = q n)
    (hqstrong : ∀ x, Tendsto (fun n => q n x) atTop (𝓝 x)) :
    ∀ T ∈ enlargedFirstAlgebra φ ψ S₃ S₂₃,
      Tendsto (fun n => doubleTensorOperator φ ψ (q n) * T) atTop (𝓝 T) ∧
        Tendsto (fun n => T * doubleTensorOperator φ ψ (q n)) atTop (𝓝 T) := by
  let v := fun n => interiorModuleTensorOperator φ (q n)
  let u := fun n => doubleTensorOperator φ ψ (q n)
  have hvnorm (n : ℕ) : ‖v n‖ ≤ 1 :=
    (interiorModuleTensorOperator_norm_le φ _).trans (hqnorm n)
  have hvself (n : ℕ) : (v n).adjoint = v n := by
    simp only [v, interiorModuleTensorOperator_adjoint, hqself]
  have hvstrong := tensorOperator_tendsto_apply_of_strong_contractions φ q hqnorm hqstrong
  have hunorm (n : ℕ) : ‖u n‖ ≤ 1 := (doubleTensorOperator_norm_le φ ψ _).trans (hqnorm n)
  have hustar (n : ℕ) : star (u n) = u n := by
    change (u n).adjoint = u n
    simp only [u, doubleTensorOperator_adjoint, hqself]
  let P := approximateUnitConvergenceAlgebra u hustar
  have hleft : leftSandwichAlgebra φ ψ S₃ ≤ P :=
    firstProductAlgebra_tendsto_tensorApproximateUnit ψ S₃ v hvnorm hvself hvstrong
  have hright : rightSandwichAlgebra φ ψ S₂₃ ≤ P := by
    intro T hT
    let ρ := (hilbertEquiv (E := E) φ ψ).transportStarAlgEquiv
    have hρ (n : ℕ) : ρ (u n) = interiorModuleTensorOperator (rightRepresentation φ ψ) (q n) :=
      hilbertEquiv_transport_operator φ ψ (q n)
    have hinv (n : ℕ) :
        ρ.symm (interiorModuleTensorOperator (rightRepresentation φ ψ) (q n)) = u n := by
      rw [← hρ, ρ.symm_apply_apply]
    have h := firstProductAlgebra_tendsto_tensorApproximateUnit
      (rightRepresentation φ ψ) S₂₃ q hqnorm hqself hqstrong (ρ T) hT
    have hcont := (NonUnitalStarAlgHom.isometry ρ.symm ρ.symm.injective).continuous.tendsto (ρ T)
    exact ⟨by simpa only [Function.comp_def, map_mul, hinv, ρ.symm_apply_apply] using hcont.comp h.1,
      by simpa only [Function.comp_def, map_mul, hinv, ρ.symm_apply_apply] using hcont.comp h.2⟩
  exact generatedClosedStarAlgebra_le _ _ P
    (approximateUnitConvergenceAlgebra_isClosed u hustar hunorm) hleft hright

/-- The enlargement's actual countable two-sided AU is derived from the
original first-module compact AU. No triple End separability is required. -/
theorem exists_enlargedFirstAlgebra_approximateUnit [TopologicalSpace.SeparableSpace B]
    (S₃ : AdjointableMap D G G)
    (S₂₃ : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ))
    (hE : IsCountablyGeneratedModule B E) :
    ∃ q : ℕ → enlargedFirstAlgebra (E := E) φ ψ S₃ S₂₃,
      (∀ T : enlargedFirstAlgebra (E := E) φ ψ S₃ S₂₃, Tendsto (fun n => T * q n) atTop (𝓝 T)) ∧
        (∀ T : enlargedFirstAlgebra (E := E) φ ψ S₃ S₂₃, Tendsto (fun n => q n * T) atTop (𝓝 T)) := by
  obtain ⟨e, _, _, _, henorm, _, _, hestrong⟩ :=
    exists_countablyGenerated_compact_approximateUnit hE
  let q : ℕ → enlargedFirstAlgebra φ ψ S₃ S₂₃ := fun n =>
    ⟨doubleTensorOperator (E := E) φ ψ (e n : AdjointableMap B E E),
      rightSandwichAlgebra_le_enlargedFirstAlgebra φ ψ S₃ S₂₃
        (doubleTensorCompact_mem_rightSandwichAlgebra (E := E) φ ψ S₂₃
          (show IsModuleCompact (e n : AdjointableMap B E E) from (e n).property))⟩
  let _nativeEndOrder : PartialOrder (AdjointableMap B E E) :=
    CStarAlgebra.spectralOrder _
  let _nativeEndStarOrder : StarOrderedRing (AdjointableMap B E E) :=
    CStarAlgebra.spectralOrderedRing _
  have heself (n : ℕ) : (e n : AdjointableMap B E E).adjoint = e n :=
    (hestrong.nonneg n).isSelfAdjoint.star_eq
  have hlim := enlargedFirstAlgebra_tendsto_doubleTensorApproximateUnit φ ψ S₃ S₂₃
    (fun n => (e n : AdjointableMap B E E)) henorm heself hestrong.strong
  refine ⟨q, ?_, ?_⟩
  · intro T
    exact tendsto_subtype_rng.mpr (hlim T T.property).2
  · intro T
    exact tendsto_subtype_rng.mpr (hlim T T.property).1

/-- Cross commutators need only land in the actual enlargement. Proving
these identities for both d and star d derives ordinary normalization of
the whole generated closure, without assuming the final KTT conclusion. -/
theorem normalizes_enlargedFirstAlgebra_of_generators
    (S₃ : AdjointableMap D G G)
    (S₂₃ : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ))
    (d : AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ))
    (hL : ∀ a ∈ leftSandwichAlgebra (E := E) φ ψ S₃,
      d * a - a * d ∈ enlargedFirstAlgebra (E := E) φ ψ S₃ S₂₃)
    (hR : ∀ a ∈ rightSandwichAlgebra (E := E) φ ψ S₂₃,
      d * a - a * d ∈ enlargedFirstAlgebra (E := E) φ ψ S₃ S₂₃)
    (hLstar : ∀ a ∈ leftSandwichAlgebra (E := E) φ ψ S₃,
      star d * a - a * star d ∈ enlargedFirstAlgebra (E := E) φ ψ S₃ S₂₃)
    (hRstar : ∀ a ∈ rightSandwichAlgebra (E := E) φ ψ S₂₃,
      star d * a - a * star d ∈ enlargedFirstAlgebra (E := E) φ ψ S₃ S₂₃) :
    ∀ a ∈ enlargedFirstAlgebra (E := E) φ ψ S₃ S₂₃,
      d * a - a * d ∈ enlargedFirstAlgebra (E := E) φ ψ S₃ S₂₃ := by
  apply normalizes_closedNonUnitalStarAdjoin
    ((leftSandwichAlgebra (E := E) φ ψ S₃ : Set (AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ))) ∪
      (rightSandwichAlgebra (E := E) φ ψ S₂₃ : Set (AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ)))) d
  · intro a ha
    rcases ha with ha | ha
    · exact hL a ha
    · exact hR a ha
  · intro a ha
    rcases ha with ha | ha
    · exact hLstar a ha
    · exact hRstar a ha

section Grading
variable {δB : CStarGrading B} {δC : CStarGrading C} {δD : CStarGrading D}

/-- Actual oddness of both middle operators and genuine associator
compatibility give exact grading stability of the enlarged first algebra. -/
theorem grading_preserves_enlargedFirstAlgebra
    (J : GradedHilbertModule δB E) (K : GradedHilbertModule δC F) (L : GradedHilbertModule δD G)
    (hφ : ModuleTensorRepresentationGraded (δB := δB) φ K)
    (hψ : ModuleTensorRepresentationGraded (δB := δC) ψ L)
    (S₃ : AdjointableMap D G G) (hS₃ : GradedHilbertModule.IsOdd L L S₃)
    (S₂₃ : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ))
    (hS₂₃ : GradedHilbertModule.IsOdd (K.interiorTensor L hψ) (K.interiorTensor L hψ) S₂₃) :
    ∀ a ∈ enlargedFirstAlgebra φ ψ S₃ S₂₃,
      ((J.interiorTensor K hφ).interiorTensor L hψ).conjugateOperator a ∈
        enlargedFirstAlgebra φ ψ S₃ S₂₃ := by
  let JL := (J.interiorTensor K hφ).interiorTensor L hψ
  let JR := J.interiorTensor (K.interiorTensor L hψ) (rightRepresentation_graded φ ψ K L hφ hψ)
  have hΩ := hilbertEquiv_grading_intertwine φ ψ J K L hφ hψ
  apply maps_generatedClosedStarAlgebra _ _ JL.conjugateOperatorStarAlgEquiv
  · exact grading_preserves_firstProductAlgebra ψ (J.interiorTensor K hφ) L hψ S₃ hS₃
  · intro a ha
    change (hilbertEquiv (E := E) φ ψ).transport (JL.conjugateOperator a) ∈
      firstProductAlgebra (E := E) (rightRepresentation φ ψ) S₂₃
    rw [HilbertModuleEquiv.transport_conjugateGrading (hilbertEquiv φ ψ) JL JR hΩ]
    exact grading_preserves_firstProductAlgebra (rightRepresentation φ ψ) J
      (K.interiorTensor L hψ) (rightRepresentation_graded φ ψ K L hφ hψ) S₂₃ hS₂₃ _ ha

end Grading

section Action
variable {Γ : Type*} [Group Γ] {α : CStarAlgebraAction Γ D}

/-- Concrete first-product action controls transport through the actual
associator and pass to the generated enlarged algebra. In applications the
two controls are derived by `action_preserves_firstProductAlgebra` for the
already constructed pair cycles; they are not an associativity assumption. -/
theorem action_preserves_enlargedFirstAlgebra_of_firstProduct_controls
    (S₃ : AdjointableMap D G G)
    (S₂₃ : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ))
    (UL : EquivariantHilbertModule α (LeftTensor (E := E) φ ψ))
    (UR : EquivariantHilbertModule α (RightTensor (E := E) φ ψ))
    (hΩ : ∀ g x, hilbertEquiv φ ψ (UL.action g x) = UR.action g (hilbertEquiv φ ψ x))
    (hL : ∀ g a, a ∈ leftSandwichAlgebra φ ψ S₃ → UL.conjugateOperator g a ∈ leftSandwichAlgebra φ ψ S₃)
    (hR : ∀ g a, a ∈ firstProductAlgebra (E := E) (rightRepresentation φ ψ) S₂₃ →
      UR.conjugateOperator g a ∈ firstProductAlgebra (E := E) (rightRepresentation φ ψ) S₂₃)
    (g : Γ) :
    ∀ a ∈ enlargedFirstAlgebra φ ψ S₃ S₂₃,
      UL.conjugateOperator g a ∈ enlargedFirstAlgebra φ ψ S₃ S₂₃ := by
  apply maps_generatedClosedStarAlgebra _ _ (UL.conjugateOperatorStarAlgEquiv g) (hL g)
  intro a ha
  change (hilbertEquiv (E := E) φ ψ).transport (UL.conjugateOperator g a) ∈
    firstProductAlgebra (E := E) (rightRepresentation φ ψ) S₂₃
  rw [HilbertModuleEquiv.transport_conjugateAction (hilbertEquiv φ ψ) UL UR hΩ]
  exact hR g _ ha

end Action

section MiddleEnlargement

/-- The first-pair sandwich algebra is genuinely tensored with one and
then norm closed. Its middle operators include the F₂⊗1 sandwiches
created by the ordinary first-pair commutator expansion. -/
def middleTensorSandwichAlgebra (S₂ : AdjointableMap C F F) :
    NonUnitalStarSubalgebra ℂ
      (AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ)) :=
  ((firstProductAlgebra (E := E) φ S₂).map
    (interiorModuleTensorOperatorHom ψ).toNonUnitalStarAlgHom).topologicalClosure

instance middleTensorSandwichAlgebra_isClosed (S₂ : AdjointableMap C F F) :
    IsClosed (middleTensorSandwichAlgebra (E := E) φ ψ S₂ : Set
      (AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ))) :=
  NonUnitalStarSubalgebra.isClosed_topologicalClosure _

theorem tensorFirstPairSandwich_mem_middleTensorSandwichAlgebra
    (S₂ : AdjointableMap C F F)
    {T : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ)}
    (hT : T ∈ firstProductAlgebra φ S₂) :
    interiorModuleTensorOperator ψ T ∈ middleTensorSandwichAlgebra φ ψ S₂ :=
  NonUnitalStarSubalgebra.le_topologicalClosure _
    (NonUnitalStarSubalgebra.mem_map.mpr ⟨T, hT, rfl⟩)

/-- The final first algebra includes both triple sandwich families and
the genuine tensored first-pair sandwich algebra. -/
def normalizerFirstAlgebra (S₂ : AdjointableMap C F F) (S₃ : AdjointableMap D G G)
    (S₂₃ : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ)) :
    NonUnitalStarSubalgebra ℂ
      (AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ)) :=
  generatedClosedStarAlgebra (enlargedFirstAlgebra φ ψ S₃ S₂₃) (middleTensorSandwichAlgebra φ ψ S₂)

instance normalizerFirstAlgebra_isClosed (S₂ : AdjointableMap C F F) (S₃ : AdjointableMap D G G)
    (S₂₃ : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ)) :
    IsClosed (normalizerFirstAlgebra (E := E) φ ψ S₂ S₃ S₂₃ : Set
      (AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ))) :=
  generatedClosedStarAlgebra_isClosed _ _

theorem enlargedFirstAlgebra_le_normalizerFirstAlgebra
    (S₂ : AdjointableMap C F F) (S₃ : AdjointableMap D G G)
    (S₂₃ : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ)) :
    enlargedFirstAlgebra φ ψ S₃ S₂₃ ≤ normalizerFirstAlgebra (E := E) φ ψ S₂ S₃ S₂₃ :=
  le_generatedClosedStarAlgebra_left _ _

theorem middleTensorSandwichAlgebra_le_normalizerFirstAlgebra
    (S₂ : AdjointableMap C F F) (S₃ : AdjointableMap D G G)
    (S₂₃ : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ)) :
    middleTensorSandwichAlgebra φ ψ S₂ ≤ normalizerFirstAlgebra (E := E) φ ψ S₂ S₃ S₂₃ :=
  le_generatedClosedStarAlgebra_right _ _

theorem firstAlgebra_le_normalizerFirstAlgebra
    (S₂ : AdjointableMap C F F) (S₃ : AdjointableMap D G G)
    (S₂₃ : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ)) :
    firstAlgebra φ ψ ≤ normalizerFirstAlgebra (E := E) φ ψ S₂ S₃ S₂₃ :=
  (firstAlgebra_le_enlargedFirstAlgebra φ ψ S₃ S₂₃).trans
    (enlargedFirstAlgebra_le_normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃)

/-- The original first-module sequence approximates the added actual
tensor-image family in norm on both sides, including its norm closure. -/
theorem middleTensorSandwichAlgebra_tendsto_doubleTensorApproximateUnit
    (S₂ : AdjointableMap C F F)
    (q : ℕ → AdjointableMap B E E) (hqnorm : ∀ n, ‖q n‖ ≤ 1)
    (hqself : ∀ n, (q n).adjoint = q n)
    (hqstrong : ∀ x, Tendsto (fun n => q n x) atTop (𝓝 x)) :
    ∀ T ∈ middleTensorSandwichAlgebra φ ψ S₂,
      Tendsto (fun n => doubleTensorOperator φ ψ (q n) * T) atTop (𝓝 T) ∧
        Tendsto (fun n => T * doubleTensorOperator φ ψ (q n)) atTop (𝓝 T) := by
  let u := fun n => doubleTensorOperator φ ψ (q n)
  have hunorm (n : ℕ) : ‖u n‖ ≤ 1 := (doubleTensorOperator_norm_le φ ψ _).trans (hqnorm n)
  have hustar (n : ℕ) : star (u n) = u n := by
    change (u n).adjoint = u n
    simp only [u, doubleTensorOperator_adjoint, hqself]
  let P := approximateUnitConvergenceAlgebra u hustar
  have hmap : (firstProductAlgebra (E := E) φ S₂).map
      (interiorModuleTensorOperatorHom ψ).toNonUnitalStarAlgHom ≤ P := by
    intro T hT
    obtain ⟨a, ha, rfl⟩ := NonUnitalStarSubalgebra.mem_map.mp hT
    have h := firstProductAlgebra_tendsto_tensorApproximateUnit φ S₂ q hqnorm hqself hqstrong a ha
    have hcont := (interiorModuleTensorOperatorCLM ψ).continuous.tendsto a
    change Tendsto (fun n => u n * interiorModuleTensorOperator ψ a) atTop
        (𝓝 (interiorModuleTensorOperator ψ a)) ∧
      Tendsto (fun n => interiorModuleTensorOperator ψ a * u n) atTop
        (𝓝 (interiorModuleTensorOperator ψ a))
    exact ⟨by simpa only [Function.comp_def, interiorModuleTensorOperatorCLM_apply,
        interiorModuleTensorOperator_mul, u, doubleTensorOperator] using hcont.comp h.1,
      by simpa only [Function.comp_def, interiorModuleTensorOperatorCLM_apply,
        interiorModuleTensorOperator_mul, u, doubleTensorOperator] using hcont.comp h.2⟩
  exact NonUnitalStarSubalgebra.topologicalClosure_minimal _ hmap
    (approximateUnitConvergenceAlgebra_isClosed u hustar hunorm)

/-- The same original first AU gives actual two-sided norm convergence
on the full necessary normalizer enlargement. -/
theorem normalizerFirstAlgebra_tendsto_doubleTensorApproximateUnit
    (S₂ : AdjointableMap C F F) (S₃ : AdjointableMap D G G)
    (S₂₃ : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ))
    (q : ℕ → AdjointableMap B E E) (hqnorm : ∀ n, ‖q n‖ ≤ 1)
    (hqself : ∀ n, (q n).adjoint = q n)
    (hqstrong : ∀ x, Tendsto (fun n => q n x) atTop (𝓝 x)) :
    ∀ T ∈ normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃,
      Tendsto (fun n => doubleTensorOperator φ ψ (q n) * T) atTop (𝓝 T) ∧
        Tendsto (fun n => T * doubleTensorOperator φ ψ (q n)) atTop (𝓝 T) := by
  let u := fun n => doubleTensorOperator φ ψ (q n)
  have hunorm (n : ℕ) : ‖u n‖ ≤ 1 := (doubleTensorOperator_norm_le φ ψ _).trans (hqnorm n)
  have hustar (n : ℕ) : star (u n) = u n := by
    change (u n).adjoint = u n
    simp only [u, doubleTensorOperator_adjoint, hqself]
  let P := approximateUnitConvergenceAlgebra u hustar
  exact generatedClosedStarAlgebra_le _ _ P
    (approximateUnitConvergenceAlgebra_isClosed u hustar hunorm)
    (enlargedFirstAlgebra_tendsto_doubleTensorApproximateUnit φ ψ S₃ S₂₃ q hqnorm hqself hqstrong)
    (middleTensorSandwichAlgebra_tendsto_doubleTensorApproximateUnit φ ψ S₂ q hqnorm hqself hqstrong)

/-- The full normalizer enlargement has a genuine countable two-sided
AU derived from the original first compact algebra. -/
theorem exists_normalizerFirstAlgebra_approximateUnit [TopologicalSpace.SeparableSpace B]
    (S₂ : AdjointableMap C F F) (S₃ : AdjointableMap D G G)
    (S₂₃ : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ))
    (hE : IsCountablyGeneratedModule B E) :
    ∃ q : ℕ → normalizerFirstAlgebra (E := E) φ ψ S₂ S₃ S₂₃,
      (∀ T : normalizerFirstAlgebra (E := E) φ ψ S₂ S₃ S₂₃, Tendsto (fun n => T * q n) atTop (𝓝 T)) ∧
        (∀ T : normalizerFirstAlgebra (E := E) φ ψ S₂ S₃ S₂₃, Tendsto (fun n => q n * T) atTop (𝓝 T)) := by
  obtain ⟨e, _, _, _, henorm, _, _, hestrong⟩ :=
    exists_countablyGenerated_compact_approximateUnit hE
  let q : ℕ → normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃ := fun n =>
    ⟨doubleTensorOperator (E := E) φ ψ (e n : AdjointableMap B E E),
      enlargedFirstAlgebra_le_normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃
        (rightSandwichAlgebra_le_enlargedFirstAlgebra φ ψ S₃ S₂₃
          (doubleTensorCompact_mem_rightSandwichAlgebra (E := E) φ ψ S₂₃
          (show IsModuleCompact (e n : AdjointableMap B E E) from (e n).property)))⟩
  let _nativeEndOrder : PartialOrder (AdjointableMap B E E) :=
    CStarAlgebra.spectralOrder _
  let _nativeEndStarOrder : StarOrderedRing (AdjointableMap B E E) :=
    CStarAlgebra.spectralOrderedRing _
  have heself (n : ℕ) : (e n : AdjointableMap B E E).adjoint = e n :=
    (hestrong.nonneg n).isSelfAdjoint.star_eq
  have hlim := normalizerFirstAlgebra_tendsto_doubleTensorApproximateUnit φ ψ S₂ S₃ S₂₃
    (fun n => (e n : AdjointableMap B E E)) henorm heself hestrong.strong
  refine ⟨q, ?_, ?_⟩
  · intro T
    exact tendsto_subtype_rng.mpr (hlim T T.property).2
  · intro T
    exact tendsto_subtype_rng.mpr (hlim T T.property).1

/-- Actual compact-first products suffice for ordinary normalization of
the entire necessary enlargement, by its proved original compact AU. -/
theorem normalizes_normalizerFirstAlgebra_of_compact_products [TopologicalSpace.SeparableSpace B]
    (S₂ : AdjointableMap C F F) (S₃ : AdjointableMap D G G)
    (S₂₃ : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ))
    (hE : IsCountablyGeneratedModule B E)
    (d : AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ))
    (hdleft : ∀ k : AdjointableMap B E E, IsModuleCompact k →
      d * doubleTensorOperator φ ψ k ∈ normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃)
    (hdright : ∀ k : AdjointableMap B E E, IsModuleCompact k →
      doubleTensorOperator φ ψ k * d ∈ normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃) :
    ∀ a ∈ normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃,
      d * a - a * d ∈ normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃ := by
  obtain ⟨e, _, _, _, henorm, _, _, hestrong⟩ :=
    exists_countablyGenerated_compact_approximateUnit hE
  let q : ℕ → normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃ := fun n =>
    ⟨doubleTensorOperator (E := E) φ ψ (e n : AdjointableMap B E E),
      enlargedFirstAlgebra_le_normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃
        (rightSandwichAlgebra_le_enlargedFirstAlgebra φ ψ S₃ S₂₃
          (doubleTensorCompact_mem_rightSandwichAlgebra (E := E) φ ψ S₂₃
          (show IsModuleCompact (e n : AdjointableMap B E E) from (e n).property)))⟩
  let _nativeEndOrder : PartialOrder (AdjointableMap B E E) :=
    CStarAlgebra.spectralOrder _
  let _nativeEndStarOrder : StarOrderedRing (AdjointableMap B E E) :=
    CStarAlgebra.spectralOrderedRing _
  have heself (n : ℕ) : (e n : AdjointableMap B E E).adjoint = e n :=
    (hestrong.nonneg n).isSelfAdjoint.star_eq
  have hlim := normalizerFirstAlgebra_tendsto_doubleTensorApproximateUnit φ ψ S₂ S₃ S₂₃
    (fun n => (e n : AdjointableMap B E E)) henorm heself hestrong.strong
  exact normalizes_of_approximateUnit_products _
    (normalizerFirstAlgebra_isClosed φ ψ S₂ S₃ S₂₃) q
    (fun a => tendsto_subtype_rng.mpr (hlim a a.property).1)
    (fun a => tendsto_subtype_rng.mpr (hlim a a.property).2) d
    (fun n => hdleft (e n : AdjointableMap B E E)
      (show IsModuleCompact (e n : AdjointableMap B E E) from (e n).property))
    (fun n => hdright (e n : AdjointableMap B E E)
      (show IsModuleCompact (e n : AdjointableMap B E E) from (e n).property))

/-- Actual intertwining ambient automorphisms preserve the norm-closed
tensor image when the first-pair sandwich algebra is invariant. -/
theorem maps_middleTensorSandwichAlgebra
    (S₂ : AdjointableMap C F F)
    (σ : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ) ≃⋆ₐ[ℂ]
      AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ))
    (τ : AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ) ≃⋆ₐ[ℂ]
      AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ))
    (hintertwine : ∀ T, τ (interiorModuleTensorOperator ψ T) = interiorModuleTensorOperator ψ (σ T))
    (hS : ∀ T ∈ firstProductAlgebra φ S₂, σ T ∈ firstProductAlgebra φ S₂) :
    ∀ T ∈ middleTensorSandwichAlgebra φ ψ S₂, τ T ∈ middleTensorSandwichAlgebra φ ψ S₂ := by
  let P := (middleTensorSandwichAlgebra φ ψ S₂).comap τ.toNonUnitalStarAlgHom
  have hP : IsClosed (P : Set (AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ))) :=
    (middleTensorSandwichAlgebra_isClosed φ ψ S₂).preimage
    (NonUnitalStarAlgHom.isometry τ τ.injective).continuous
  have hmap : (firstProductAlgebra (E := E) φ S₂).map
      (interiorModuleTensorOperatorHom ψ).toNonUnitalStarAlgHom ≤ P := by
    intro T hT
    obtain ⟨a, ha, rfl⟩ := NonUnitalStarSubalgebra.mem_map.mp hT
    change τ (interiorModuleTensorOperator ψ a) ∈ middleTensorSandwichAlgebra φ ψ S₂
    rw [hintertwine]
    exact tensorFirstPairSandwich_mem_middleTensorSandwichAlgebra φ ψ S₂ (hS a ha)
  exact NonUnitalStarSubalgebra.topologicalClosure_minimal _ hmap hP

section MiddleGrading
variable {δB : CStarGrading B} {δC : CStarGrading C} {δD : CStarGrading D}

/-- The added middle family is exactly grading stable from actual
oddness of F₂ and the genuine pure-tensor grading formula. -/
theorem grading_preserves_middleTensorSandwichAlgebra
    (J : GradedHilbertModule δB E) (K : GradedHilbertModule δC F) (L : GradedHilbertModule δD G)
    (hφ : ModuleTensorRepresentationGraded (δB := δB) φ K)
    (hψ : ModuleTensorRepresentationGraded (δB := δC) ψ L)
    (S₂ : AdjointableMap C F F) (hS₂ : GradedHilbertModule.IsOdd K K S₂) :
    ∀ T ∈ middleTensorSandwichAlgebra φ ψ S₂,
      ((J.interiorTensor K hφ).interiorTensor L hψ).conjugateOperator T ∈
        middleTensorSandwichAlgebra φ ψ S₂ := by
  let JP := J.interiorTensor K hφ
  let JT := JP.interiorTensor L hψ
  have htransport (T : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ)) :
      JT.conjugateOperator (interiorModuleTensorOperator ψ T) =
        interiorModuleTensorOperator ψ (JP.conjugateOperator T) := by
    apply AdjointableMap.toCLM_injective
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    simp only [GradedHilbertModule.conjugateOperator_apply, interiorModuleTensorOperator_mk]
    change (JP.interiorTensor L hψ).grading
        (interiorModuleTensorOperator (E := InteriorModuleTensor (E := E) φ) ψ T
          ((JP.interiorTensor L hψ).grading (interiorModuleTensorMk ψ x y))) =
      interiorModuleTensorMk ψ (JP.grading (T (JP.grading x))) y
    rw [GradedHilbertModule.interiorTensor_grading_mk (φ := ψ) JP L hψ x y,
      interiorModuleTensorOperator_mk,
      GradedHilbertModule.interiorTensor_grading_mk (φ := ψ) JP L hψ
        (T (JP.grading x)) (L.grading y), L.grading_sq]
  exact maps_middleTensorSandwichAlgebra φ ψ S₂ JP.conjugateOperatorStarAlgEquiv
    JT.conjugateOperatorStarAlgEquiv htransport
    (grading_preserves_firstProductAlgebra φ J K hφ S₂ hS₂)

/-- All three actual sandwich families give an exactly grading-stable
normalizer first algebra when their three middle operators are odd. -/
theorem grading_preserves_normalizerFirstAlgebra
    (J : GradedHilbertModule δB E) (K : GradedHilbertModule δC F) (L : GradedHilbertModule δD G)
    (hφ : ModuleTensorRepresentationGraded (δB := δB) φ K)
    (hψ : ModuleTensorRepresentationGraded (δB := δC) ψ L)
    (S₂ : AdjointableMap C F F) (hS₂ : GradedHilbertModule.IsOdd K K S₂)
    (S₃ : AdjointableMap D G G) (hS₃ : GradedHilbertModule.IsOdd L L S₃)
    (S₂₃ : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ))
    (hS₂₃ : GradedHilbertModule.IsOdd (K.interiorTensor L hψ) (K.interiorTensor L hψ) S₂₃) :
    ∀ T ∈ normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃,
      ((J.interiorTensor K hφ).interiorTensor L hψ).conjugateOperator T ∈
        normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃ :=
  maps_generatedClosedStarAlgebra _ _
    ((J.interiorTensor K hφ).interiorTensor L hψ).conjugateOperatorStarAlgEquiv
    (grading_preserves_enlargedFirstAlgebra φ ψ J K L hφ hψ S₃ hS₃ S₂₃ hS₂₃)
    (grading_preserves_middleTensorSandwichAlgebra φ ψ J K L hφ hψ S₂ hS₂)

end MiddleGrading

section MiddleAction
variable {Γ : Type*} [Group Γ]
  {β : CStarAlgebraAction Γ C} {γ : CStarAlgebraAction Γ D}

/-- The actual tensor group action preserves the added middle family
from the independently derived first-pair sandwich action controls. -/
theorem action_preserves_middleTensorSandwichAlgebra
    (S₂ : AdjointableMap C F F)
    (UP : EquivariantHilbertModule β (InteriorModuleTensor (E := E) φ))
    (W : EquivariantHilbertModule γ G)
    (hψ : ModuleTensorRepresentationEquivariant ψ β W)
    (hpair : ∀ g T, T ∈ firstProductAlgebra φ S₂ → UP.conjugateOperator g T ∈ firstProductAlgebra φ S₂)
    (g : Γ) :
    ∀ T ∈ middleTensorSandwichAlgebra φ ψ S₂,
      (UP.interiorTensor W hψ).conjugateOperator g T ∈ middleTensorSandwichAlgebra φ ψ S₂ :=
  maps_middleTensorSandwichAlgebra φ ψ S₂ (UP.conjugateOperatorStarAlgEquiv g)
    ((UP.interiorTensor W hψ).conjugateOperatorStarAlgEquiv g)
    (UP.interiorTensor_conjugateOperator W hψ g) (hpair g)

/-- Independently derived base and first-pair action controls pass to
the full necessary normalizer algebra under the actual tensor action. -/
theorem action_preserves_normalizerFirstAlgebra_of_pair_controls
    (S₂ : AdjointableMap C F F) (S₃ : AdjointableMap D G G)
    (S₂₃ : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ))
    (UP : EquivariantHilbertModule β (InteriorModuleTensor (E := E) φ))
    (W : EquivariantHilbertModule γ G)
    (hψ : ModuleTensorRepresentationEquivariant ψ β W)
    (hpair : ∀ g T, T ∈ firstProductAlgebra φ S₂ → UP.conjugateOperator g T ∈ firstProductAlgebra φ S₂)
    (hbase : ∀ g T, T ∈ enlargedFirstAlgebra φ ψ S₃ S₂₃ →
      (UP.interiorTensor W hψ).conjugateOperator g T ∈ enlargedFirstAlgebra φ ψ S₃ S₂₃)
    (g : Γ) :
    ∀ T ∈ normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃,
      (UP.interiorTensor W hψ).conjugateOperator g T ∈ normalizerFirstAlgebra φ ψ S₂ S₃ S₂₃ :=
  maps_generatedClosedStarAlgebra _ _ ((UP.interiorTensor W hψ).conjugateOperatorStarAlgEquiv g)
    (hbase g) (action_preserves_middleTensorSandwichAlgebra φ ψ S₂ UP W hψ hpair g)

end MiddleAction
end MiddleEnlargement
end KasparovTriple
end BC4lean.KKTheory
