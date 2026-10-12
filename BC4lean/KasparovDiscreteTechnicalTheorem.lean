import BC4lean.KasparovSelectedTechnicalPartition
import BC4lean.CompactModuleCountableApproximateUnit

/-! # The even countable discrete Kasparov technical theorem

This is the countable discrete group and countable discrete family
specialization of Gabe–Szabó, Theorem 2.6, in the actual Hilbert-module
multiplier algebra. Sigma-unitality of the two source algebras is given by
genuine countable two-sided AUs. In the chapter's separable coefficient
setting the compact AU is derived from countable module generation.
The first algebra is actually augmented by K(E); all hypotheses are proved
to survive. A norm-separable normalizer set supplies countable dense tests.
The selector, strong column-square limit, compact norm-series controls,
even averaging, and actual square roots then construct every conclusion.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter TopologicalSpace
open scoped Topology

variable {Γ B E : Type*} [Group Γ] [Countable Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [SeparableSpace B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

local instance kasparovDiscreteTechnicalTheoremLocalInst1 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance kasparovDiscreteTechnicalTheoremLocalInst2 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _
local instance kasparovDiscreteTechnicalTheoremLocalInst3 : PartialOrder (CompactModuleOperator B E) := CStarAlgebra.spectralOrder _
local instance kasparovDiscreteTechnicalTheoremLocalInst4 : StarOrderedRing (CompactModuleOperator B E) := CStarAlgebra.spectralOrderedRing _

/-- Every source hypothesis of the countable discrete specialization is
retained. Exact grading stability supplies the even refinement used in
the product. No separability of End(E), or essentiality of E₁, is assumed. -/
theorem exists_kasparovDiscreteTechnicalPartition
    (hE : IsCountablyGeneratedModule B E)
    {β : CStarGrading B} {α : CStarAlgebraAction Γ B}
    (J : GradedHilbertModule β E) (V : EquivariantHilbertModule α E) (hV : V.PreservesGrading J)
    (E₁ E₂ : NonUnitalStarSubalgebra ℂ (AdjointableMap B E E))
    [IsClosed (E₁ : Set (AdjointableMap B E E))] [IsClosed (E₂ : Set (AdjointableMap B E E))]
    (q₁ : ℕ → E₁) (q₂ : ℕ → E₂)
    (hq₁left : ∀ a, Tendsto (fun n => a * q₁ n) atTop (𝓝 a))
    (hq₁right : ∀ a, Tendsto (fun n => q₁ n * a) atTop (𝓝 a))
    (_hq₂left : ∀ a, Tendsto (fun n => a * q₂ n) atTop (𝓝 a))
    (hq₂right : ∀ a, Tendsto (fun n => q₂ n * a) atTop (𝓝 a))
    (hE₁E₂ : ∀ a ∈ E₁, ∀ b ∈ E₂, IsModuleCompact (a * b))
    (hE₁action : ∀ g a, a ∈ E₁ → V.conjugateOperator g a ∈ E₁)
    (hE₁grade : ∀ a ∈ E₁, J.conjugateOperator a ∈ E₁)
    (hE₂grade : ∀ a ∈ E₂, J.conjugateOperator a ∈ E₂)
    (Δ : Set (AdjointableMap B E E)) (hΔsep : IsSeparable Δ)
    (hnormal : ∀ d ∈ Δ, ∀ a ∈ E₁, d * a - a * d ∈ E₁)
    (f : ℕ → AdjointableMap B E E)
    (_hfBounded : ∃ C : ℝ, ∀ k, ‖f k‖ ≤ C)
    (hfamily : ∀ k a, a ∈ E₁ → IsModuleCompact (a * f k) ∧ IsModuleCompact (f k * a)) :
    Nonempty (KasparovTechnicalPartition J V E₁ E₂ Δ f) := by
  classical
  rcases subsingleton_or_nontrivial (AdjointableMap B E E) with hzero | hnonzero
  · let := hzero
    have hcompact (T : AdjointableMap B E E) : IsModuleCompact T := by
      rw [Subsingleton.elim T 0]
      exact IsModuleCompact.zero
    refine ⟨{
      m := 0, n := 0
      m_nonneg := le_rfl, n_nonneg := le_rfl
      m_norm_le_one := by simp, n_norm_le_one := by simp
      square_partition := Subsingleton.elim _ _
      m_even := GradedHilbertModule.isEven_zero
      n_even := GradedHilbertModule.isEven_zero
      first_ideal := ?_, second_ideal := ?_
      commutator_m := ?_, commutator_n := ?_
      action_m := ?_, action_n := ?_
      family_left := ?_, family_right := ?_ }⟩
    all_goals intros; exact hcompact _
  · let := hnonzero
    let K := compactModuleOperatorAlgebra (B := B) (E := E)
    have hK : IsClosedTwoSidedStarIdeal K := compactModuleOperatorAlgebra_isClosedTwoSidedStarIdeal
    let U := generatedClosedStarAlgebra E₁ K
    let : PartialOrder U := CStarAlgebra.spectralOrder _
    let : StarOrderedRing U := CStarAlgebra.spectralOrderedRing _
    obtain ⟨qK, _, _, _, _, hqKleft, hqKright, _⟩ :=
      exists_countablyGenerated_compact_approximateUnit hE
    obtain ⟨qU, _, _, _, _, _, hqUleft, hqUright⟩ :=
      exists_generatedClosedStarAlgebra_approximateUnit E₁ K q₁ qK
        hq₁left hq₁right hqKleft hqKright
    let σ := J.conjugateOperatorStarAlgEquiv
    have hσ (a : AdjointableMap B E E) : σ (σ a) = a := J.conjugateOperator_involutive a
    have hUgrade : ∀ a ∈ U, σ a ∈ U := grading_preserves_augmentedOperatorAlgebra J E₁ hE₁grade
    have hUaction (g : Γ) : ∀ a ∈ U, V.conjugateOperator g a ∈ U :=
      action_preserves_augmentedOperatorAlgebra V g E₁ (hE₁action g)
    let αU : Γ → U ≃⋆ₐ[ℂ] U := fun g =>
      restrictStarAlgEquiv U (V.conjugateOperatorStarAlgEquiv g)
        (hUaction g) (hUaction g⁻¹)
    let αK : Γ → CompactModuleOperator B E ≃⋆ₐ[ℂ] CompactModuleOperator B E := fun g =>
      restrictStarAlgEquiv K (V.conjugateOperatorStarAlgEquiv g)
        (fun _ ha => V.conjugateOperator_mem_moduleCompact g ha)
        (fun _ ha => V.conjugateOperator_mem_moduleCompact g⁻¹ ha)
    have hαU (g : Γ) (a : U) : (αU g a : AdjointableMap B E E) = V.conjugateOperator g a := rfl
    have hαK (g : Γ) (a : CompactModuleOperator B E) :
        (αK g a : AdjointableMap B E E) = V.conjugateOperator g a := rfl
    have hnormalU : ∀ d ∈ Δ, ∀ a ∈ U, d * a - a * d ∈ U := fun d hd =>
      normalizes_generatedClosedStarAlgebra E₁ K hK d (hnormal d hd)
    obtain ⟨δ, hδdense, hδnormal⟩ := exists_countable_normalizer_tests U Δ hΔsep hnormalU
    let δ' := kasparovNormalizerTests σ δ
    have hδ'normal : ∀ k, ∀ a ∈ U, δ' k * a - a * δ' k ∈ U := by
      intro k
      dsimp [δ', kasparovNormalizerTests, periodicCountableTests]
      split_ifs
      · exact hδnormal _
      · exact gradingImage_normalizes U σ hσ hUgrade _ (hδnormal _)
    have hE₂products : ∀ a ∈ U, ∀ b ∈ E₂, a * b ∈ K ∧ b * a ∈ K :=
      hK.generated_algebra_products E₁ E₂ hE₁E₂
    let F : Set (AdjointableMap B E E) := {b | ∃ k, b = f k ∨ b = star (f k)}
    have hFstar : ∀ b ∈ F, star b ∈ F := by
      rintro b ⟨k, rfl | rfl⟩
      · exact ⟨k, Or.inr rfl⟩
      · exact ⟨k, Or.inl (star_star _)⟩
    have hE₁F : ∀ a ∈ E₁, ∀ b ∈ F, a * b ∈ K ∧ b * a ∈ K := by
      intro a ha b hb
      obtain ⟨k, rfl | rfl⟩ := hb
      · exact hfamily k a ha
      · have h := hfamily k (star a) (E₁.star_mem' ha)
        exact ⟨by simpa only [star_mul, star_star] using (star_mem (s := K) h.2),
          by simpa only [star_mul, star_star] using (star_mem (s := K) h.1)⟩
    have hFproducts : ∀ a ∈ U, ∀ b ∈ F, a * b ∈ K ∧ b * a ∈ K :=
      fun _ ha => hK.generated_test_products E₁ F hFstar hE₁F ha
    have hgradeProducts (b : AdjointableMap B E E)
        (hb : ∀ a ∈ U, a * b ∈ K ∧ b * a ∈ K) :
        ∀ a ∈ U, a * σ b ∈ K ∧ σ b * a ∈ K := by
      intro a ha
      have h := hb (σ a) (hUgrade a ha)
      have hleft := J.conjugateOperator_mem_moduleCompact h.1
      have hright := J.conjugateOperator_mem_moduleCompact h.2
      change σ (σ a * b) ∈ K at hleft
      change σ (b * σ a) ∈ K at hright
      simpa only [map_mul, hσ] using And.intro hleft hright
    let b := kasparovFamilyTests σ (fun k => (q₂ k : AdjointableMap B E E)) f
    have hbproducts : ∀ a ∈ U, ∀ k, a * b k ∈ K ∧ b k * a ∈ K := by
      intro a ha k
      dsimp [b, kasparovFamilyTests, periodicCountableTests]
      split_ifs
      · exact hE₂products a ha _ (q₂ _).property
      · exact hFproducts a ha _ ⟨_, Or.inl rfl⟩
      · exact hFproducts a ha _ ⟨_, Or.inr rfl⟩
      · exact hgradeProducts _ (fun a ha => hFproducts a ha _ ⟨_, Or.inl rfl⟩) a ha
      · exact hgradeProducts _ (fun a ha => hFproducts a ha _ ⟨_, Or.inr rfl⟩) a ha
      · exact hgradeProducts _ (fun a ha => hE₂products a ha _ (q₂ _).property) a ha
    let t := kasparovBandTests δ' (fun k => (qU k : AdjointableMap B E E)) b
    obtain ⟨τ, hτ⟩ := exists_kasparov_bandControlTolerance t
    obtain ⟨γ, u, e, hγ, hsel⟩ := exists_kasparov_countable_selection U K hK δ' t b qU qK
      hδ'normal hbproducts αU αK τ hτ.positive
    exact ⟨kasparovTechnicalPartition_of_countableSelection J V hV E₁ E₂
      (le_generatedClosedStarAlgebra_left E₁ K) hE₁grade hE₂grade Δ δ hδdense f qU qK q₂
      hqUright hqKleft hqKright hq₂right γ hγ αU αK hαU hαK τ u e hτ hsel⟩

end BC4lean.KKTheory
