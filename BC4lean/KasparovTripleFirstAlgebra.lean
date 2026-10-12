import BC4lean.GradedModuleConnectionComposition
import BC4lean.KasparovProductAlgebras

/-! # The actual first technical algebra for a triple product

Skandalis's associativity partition uses compact operators from the original
first module and from the completed first-pair module, as well as the actual
compact ideal of the triple tensor. These three families generate a concrete
closed star algebra. A single genuine compact approximate unit on the original
first module is a two-sided norm approximate unit for the entire enlarged
algebra. In particular sigma-unitality is derived without assuming that an
endomorphism algebra is separable or that a represented essential range splits.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovTriple
open Filter
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

def doubleTensorOperator (T : AdjointableMap B E E) :
    AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ) :=
  interiorModuleTensorOperator ψ (interiorModuleTensorOperator φ T)

def firstGenerators : Set
    (AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ)) :=
  (doubleTensorOperator φ ψ '' (moduleCompact B E E : Set _)) ∪
    (interiorModuleTensorOperator ψ ''
      (moduleCompact C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ) : Set _)) ∪
    (moduleCompact D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ) : Set _)

def firstAlgebra : NonUnitalStarSubalgebra ℂ
    (AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ)) :=
  closedNonUnitalStarAdjoin (firstGenerators φ ψ)

theorem firstAlgebra_isClosed :
    IsClosed (firstAlgebra (E := E) φ ψ : Set (AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ))) :=
  closedNonUnitalStarAdjoin_isClosed _

theorem doubleTensorCompact_mem_firstAlgebra {T : AdjointableMap B E E}
    (hT : IsModuleCompact T) : doubleTensorOperator φ ψ T ∈ firstAlgebra φ ψ :=
  subset_closedNonUnitalStarAdjoin _ (Or.inl (Or.inl ⟨T, hT, rfl⟩))

theorem pairTensorCompact_mem_firstAlgebra
    {T : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ)}
    (hT : IsModuleCompact T) : interiorModuleTensorOperator ψ T ∈ firstAlgebra φ ψ :=
  subset_closedNonUnitalStarAdjoin _ (Or.inl (Or.inr ⟨T, hT, rfl⟩))

theorem moduleCompact_mem_firstAlgebra
    {T : AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ)}
    (hT : IsModuleCompact T) : T ∈ firstAlgebra φ ψ :=
  subset_closedNonUnitalStarAdjoin _ (Or.inr hT)

theorem doubleTensorOperator_norm_le (T : AdjointableMap B E E) :
    ‖doubleTensorOperator φ ψ T‖ ≤ ‖T‖ :=
  (interiorModuleTensorOperator_norm_le ψ _).trans (interiorModuleTensorOperator_norm_le φ T)

theorem doubleTensorOperator_adjoint (T : AdjointableMap B E E) :
    (doubleTensorOperator φ ψ T).adjoint = doubleTensorOperator φ ψ T.adjoint := by
  simp only [doubleTensorOperator, interiorModuleTensorOperator_adjoint]

/-- The original compact approximate unit simultaneously approximates
both compact tensor families and the actual triple compact ideal. -/
theorem firstAlgebra_tendsto_doubleTensorApproximateUnit
    (q : ℕ → AdjointableMap B E E) (hqnorm : ∀ n, ‖q n‖ ≤ 1)
    (hqself : ∀ n, (q n).adjoint = q n)
    (hqstrong : ∀ x, Tendsto (fun n => q n x) atTop (𝓝 x)) :
    ∀ T ∈ firstAlgebra φ ψ,
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
  have huself (n : ℕ) : (u n).adjoint = u n := by
    simp only [u, doubleTensorOperator_adjoint, hqself]
  have hustar (n : ℕ) : star (u n) = u n := huself n
  have hustrong := tensorOperator_tendsto_apply_of_strong_contractions ψ v hvnorm hvstrong
  let P := approximateUnitConvergenceAlgebra u hustar
  have hle : firstAlgebra φ ψ ≤ P := by
    apply closedNonUnitalStarAdjoin_le _ P
      (approximateUnitConvergenceAlgebra_isClosed u hustar hunorm)
    intro T hT
    rcases hT with (hT | hT) | hT
    · obtain ⟨K, hK, rfl⟩ := hT
      let L : AdjointableMap B E E →L[ℂ]
          AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ) :=
        (interiorModuleTensorOperatorCLM (E := InteriorModuleTensor (E := E) φ) ψ).comp
          (interiorModuleTensorOperatorCLM (E := E) φ)
      have hl := L.continuous.tendsto K |>.comp
        (isModuleCompact_tendsto_comp_left_of_strong_contractions q hqnorm hqstrong hK)
      have hr := L.continuous.tendsto K |>.comp
        (isModuleCompact_tendsto_comp_right_of_strong_selfadjoint_contractions q hqnorm hqself hqstrong hK)
      change Tendsto (fun n => L (q n * K)) atTop (𝓝 (L K)) at hl
      change Tendsto (fun n => L (K * q n)) atTop (𝓝 (L K)) at hr
      constructor
      · simpa only [L, ContinuousLinearMap.comp_apply,
          interiorModuleTensorOperatorCLM_apply, interiorModuleTensorOperator_mul,
          u, doubleTensorOperator] using hl
      · simpa only [L, ContinuousLinearMap.comp_apply,
          interiorModuleTensorOperatorCLM_apply, interiorModuleTensorOperator_mul,
          u, doubleTensorOperator] using hr
    · obtain ⟨K, hK, rfl⟩ := hT
      have hl := (interiorModuleTensorOperatorCLM
        (E := InteriorModuleTensor (E := E) φ) ψ).continuous.tendsto K |>.comp
        (isModuleCompact_tendsto_comp_left_of_strong_contractions v hvnorm hvstrong hK)
      have hr := (interiorModuleTensorOperatorCLM
        (E := InteriorModuleTensor (E := E) φ) ψ).continuous.tendsto K |>.comp
        (isModuleCompact_tendsto_comp_right_of_strong_selfadjoint_contractions v hvnorm hvself hvstrong hK)
      change Tendsto (fun n => interiorModuleTensorOperator ψ (v n * K)) atTop
        (𝓝 (interiorModuleTensorOperator ψ K)) at hl
      change Tendsto (fun n => interiorModuleTensorOperator ψ (K * v n)) atTop
        (𝓝 (interiorModuleTensorOperator ψ K)) at hr
      constructor
      · simpa only [interiorModuleTensorOperator_mul, v, u, doubleTensorOperator] using hl
      · simpa only [interiorModuleTensorOperator_mul, v, u, doubleTensorOperator] using hr
    · exact ⟨isModuleCompact_tendsto_comp_left_of_strong_contractions u hunorm hustrong hT,
        isModuleCompact_tendsto_comp_right_of_strong_selfadjoint_contractions u hunorm huself hustrong hT⟩
  exact fun _ hT => hle hT

/-- Genuine sigma-unitality of the enlarged algebra, from countable
generation over the original separable first coefficient algebra. -/
theorem exists_firstAlgebra_approximateUnit [TopologicalSpace.SeparableSpace B]
    (hE : IsCountablyGeneratedModule B E) :
    ∃ q : ℕ → firstAlgebra (E := E) φ ψ,
      (∀ T, Tendsto (fun n => T * q n) atTop (𝓝 T)) ∧
      (∀ T, Tendsto (fun n => q n * T) atTop (𝓝 T)) := by
  let : IsClosed (firstAlgebra (E := E) φ ψ : Set (AdjointableMap D (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ))) :=
    firstAlgebra_isClosed (E := E) φ ψ
  obtain ⟨e, _, _, _, henorm, _, _, hestrong⟩ :=
    exists_countablyGenerated_compact_approximateUnit hE
  let q : ℕ → firstAlgebra (E := E) φ ψ := fun n =>
    ⟨doubleTensorOperator φ ψ (e n), doubleTensorCompact_mem_firstAlgebra φ ψ (e n).property⟩
  let _nativeEndOrder : PartialOrder (AdjointableMap B E E) :=
    CStarAlgebra.spectralOrder _
  let _nativeEndStarOrder : StarOrderedRing (AdjointableMap B E E) :=
    CStarAlgebra.spectralOrderedRing _
  have heself (n : ℕ) : (e n : AdjointableMap B E E).adjoint = e n :=
    (hestrong.nonneg n).isSelfAdjoint.star_eq
  have hlim := firstAlgebra_tendsto_doubleTensorApproximateUnit φ ψ
    (fun n => (e n : AdjointableMap B E E)) henorm heself hestrong.strong
  refine ⟨q, ?_, ?_⟩
  · intro T
    exact tendsto_subtype_rng.mpr (hlim T T.property).2
  · intro T
    exact tendsto_subtype_rng.mpr (hlim T T.property).1

end BC4lean.KKTheory.KasparovTriple
