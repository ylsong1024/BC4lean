import BC4lean.KasparovBandIdealControls
import BC4lean.KasparovCountableTests

/-! # Extending the countable controls to the stated algebras and Δ

Approximate-unit multiplication extends compact product controls from the
specified countable AU values to every coefficient. Norm-closed compact
commutator sets extend a countable dense normalizer track to the actual
norm-separable Δ. The ambient endomorphism algebra is never assumed to be
separable.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter TopologicalSpace
open scoped Topology

section NormalizerEnumeration
variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- Norm separability of the tested set produces an actual countable
dense normalizer family. Adding zero handles an empty tested set. -/
theorem exists_countable_normalizer_tests
    (S : NonUnitalStarSubalgebra ℂ A) (Δ : Set A) (hsep : IsSeparable Δ)
    (hnormal : ∀ d ∈ Δ, ∀ a ∈ S, d * a - a * d ∈ S) :
    ∃ δ : ℕ → A, Δ ⊆ closure (Set.range δ) ∧
      ∀ k, ∀ a ∈ S, δ k * a - a * δ k ∈ S := by
  classical
  let D : Set A := Δ ∪ {0}
  have hD : IsSeparable D := hsep.union (Set.finite_singleton (0 : A)).isSeparable
  let : SeparableSpace D := hD.separableSpace
  let : Nonempty D := ⟨⟨0, Or.inr rfl⟩⟩
  let δ : ℕ → A := fun n => (denseSeq D n).val
  refine ⟨δ, ?_, ?_⟩
  · intro d hd
    let x : D := ⟨d, Or.inl hd⟩
    have hx := denseRange_denseSeq D x
    exact map_mem_closure continuous_subtype_val hx (by
      rintro _ ⟨k, rfl⟩
      exact ⟨k, rfl⟩)
  · intro k a ha
    rcases (denseSeq D k).property with hd | hd
    · exact hnormal (δ k) hd a ha
    · have hz : δ k = 0 := hd
      simp only [hz, zero_mul, mul_zero, sub_self]
      exact S.zero_mem

end NormalizerEnumeration

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- The genuine countable approximate unit extends compact right
products to every coefficient of its actual subalgebra. -/
theorem compact_products_from_subalgebra_approximateUnit
    (S : NonUnitalStarSubalgebra ℂ (AdjointableMap B E E))
    (q : ℕ → S) (hq : ∀ a : S, Tendsto (fun n => q n * a) atTop (𝓝 a))
    (M : AdjointableMap B E E) (hMq : ∀ k, IsModuleCompact (M * (q k : AdjointableMap B E E))) :
    ∀ a ∈ S, IsModuleCompact (M * a) := by
  intro a ha
  let x : S := ⟨a, ha⟩
  have hqa : Tendsto (fun n => (q n : AdjointableMap B E E) * a) atTop (𝓝 a) := by
    exact (continuous_subtype_val.tendsto x).comp (hq x)
  have hlim : Tendsto (fun n => M * ((q n : AdjointableMap B E E) * a)) atTop (𝓝 (M * a)) :=
    tendsto_const_nhds.mul hqa
  apply IsModuleCompact.of_tendsto hlim
  exact Eventually.of_forall fun n => by
    rw [← mul_assoc]
    exact (hMq n).comp_right a

omit [CompleteSpace E] in
/-- The compact-commutator test set is actually closed in operator norm. -/
theorem compact_commutator_test_set_isClosed (M : AdjointableMap B E E) :
    IsClosed {a : AdjointableMap B E E | IsModuleCompact (M * a - a * M)} := by
  let L : AdjointableMap B E E →L[ℂ] AdjointableMap B E E :=
    AdjointableMap.compLeftContinuousLinearMap M
  let R : AdjointableMap B E E →L[ℂ] AdjointableMap B E E :=
    AdjointableMap.compRightContinuousLinearMap M
  exact (moduleCompact_isClosed (B := B) (E := E) (F := E)).preimage (L - R).continuous

omit [CompleteSpace E] in
/-- All of the stated norm-separable normalizer tests retain compact
commutators, by the genuine norm closure of the compact ideal. -/
theorem compact_commutators_from_dense_tests
    (M : AdjointableMap B E E) (δ : ℕ → AdjointableMap B E E)
    (Δ : Set (AdjointableMap B E E)) (hΔ : Δ ⊆ closure (Set.range δ))
    (hδ : ∀ k, IsModuleCompact (M * δ k - δ k * M)) :
    ∀ d ∈ Δ, IsModuleCompact (M * d - d * M) := by
  have hbase : Set.range δ ⊆ {d | IsModuleCompact (M * d - d * M)} := by
    rintro _ ⟨k, rfl⟩
    exact hδ k
  exact fun d hd => closure_minimal hbase (compact_commutator_test_set_isClosed M) (hΔ hd)

end BC4lean.KKTheory
