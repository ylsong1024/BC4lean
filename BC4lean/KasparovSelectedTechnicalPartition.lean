import BC4lean.KasparovSelectedBandBounds

/-! # The actual partition from the proved paired selector

This theorem assembles the genuine paired recursive selections, their
strong compact resolution, the norm-summable band controls, norm-closure
extensions, exact grading averaging, and square-root conversion. It
assumes the actual selected sequences supplied by the construction
theorem, not ideal membership or cycle conclusions for their limits.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped Topology

variable {Γ B E : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

local instance kasparovSelectedTechnicalPartitionLocalInst1 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance kasparovSelectedTechnicalPartitionLocalInst2 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _
local instance kasparovSelectedTechnicalPartitionLocalInst3 : PartialOrder (CompactModuleOperator B E) := CStarAlgebra.spectralOrder _
local instance kasparovSelectedTechnicalPartitionLocalInst4 : StarOrderedRing (CompactModuleOperator B E) := CStarAlgebra.spectralOrderedRing _

variable {U₁ : NonUnitalStarSubalgebra ℂ (AdjointableMap B E E)} [IsClosed (U₁ : Set (AdjointableMap B E E))]
local instance kasparovSelectedTechnicalPartitionLocalInst5 : PartialOrder U₁ := CStarAlgebra.spectralOrder _
local instance kasparovSelectedTechnicalPartitionLocalInst6 : StarOrderedRing U₁ := CStarAlgebra.spectralOrderedRing _

/-- The complete countable discrete technical partition is constructed
from the genuine selector output and the original AU data. -/
def kasparovTechnicalPartition_of_countableSelection
    {β : CStarGrading B} {α : CStarAlgebraAction Γ B}
    (J : GradedHilbertModule β E) (V : EquivariantHilbertModule α E) (hV : V.PreservesGrading J)
    (E₁ E₂ : NonUnitalStarSubalgebra ℂ (AdjointableMap B E E))
    (hE₁U : E₁ ≤ U₁)
    (hE₁ : ∀ a ∈ E₁, J.conjugateOperator a ∈ E₁)
    (hE₂ : ∀ a ∈ E₂, J.conjugateOperator a ∈ E₂)
    (Δ : Set (AdjointableMap B E E)) (δ : ℕ → AdjointableMap B E E)
    (hΔ : Δ ⊆ closure (Set.range δ)) (f : ℕ → AdjointableMap B E E)
    (qU : ℕ → U₁) (qK : ℕ → CompactModuleOperator B E) (q₂ : ℕ → E₂)
    (hqU : ∀ a, Tendsto (fun n => qU n * a) atTop (𝓝 a))
    (hqKleft : ∀ a, Tendsto (fun n => a * qK n) atTop (𝓝 a))
    (hqKright : ∀ a, Tendsto (fun n => qK n * a) atTop (𝓝 a))
    (hq₂ : ∀ a, Tendsto (fun n => q₂ n * a) atTop (𝓝 a))
    (γ : ℕ → Γ) (hγ : Function.Surjective γ)
    (αU : Γ → U₁ ≃⋆ₐ[ℂ] U₁)
    (αK : Γ → CompactModuleOperator B E ≃⋆ₐ[ℂ] CompactModuleOperator B E)
    (hαU : ∀ g a, (αU g a : AdjointableMap B E E) = V.conjugateOperator g a)
    (hαK : ∀ g a, (αK g a : AdjointableMap B E E) = V.conjugateOperator g a)
    (τ : ℕ → ℝ) (u : ℕ → U₁) (e : ℕ → CompactModuleOperator B E)
    (hτ : IsKasparovBandControlTolerance
      (kasparovBandTests (kasparovNormalizerTests J.conjugateOperatorStarAlgEquiv δ)
        (fun k => (qU k : AdjointableMap B E E))
        (kasparovFamilyTests J.conjugateOperatorStarAlgEquiv
          (fun k => (q₂ k : AdjointableMap B E E)) f)) τ)
    (hsel : IsKasparovCountableSelection U₁ (compactModuleOperatorAlgebra (B := B) (E := E))
      (kasparovNormalizerTests J.conjugateOperatorStarAlgEquiv δ)
      (kasparovBandTests (kasparovNormalizerTests J.conjugateOperatorStarAlgEquiv δ)
        (fun k => (qU k : AdjointableMap B E E))
        (kasparovFamilyTests J.conjugateOperatorStarAlgEquiv
          (fun k => (q₂ k : AdjointableMap B E E)) f))
      (kasparovFamilyTests J.conjugateOperatorStarAlgEquiv
        (fun k => (q₂ k : AdjointableMap B E E)) f)
      qU qK γ αU αK τ u e) :
    KasparovTechnicalPartition J V E₁ E₂ Δ f := by
  let σ := J.conjugateOperatorStarAlgEquiv
  let δ' := kasparovNormalizerTests σ δ
  let b := kasparovFamilyTests σ (fun k => (q₂ k : AdjointableMap B E E)) f
  let t := kasparovBandTests δ' (fun k => (qU k : AdjointableMap B E E)) b
  let ee : ℕ → AdjointableMap B E E := fun n => (e n : AdjointableMap B E E)
  let uu : ℕ → AdjointableMap B E E := fun n => (u n : AdjointableMap B E E)
  let vv : ℕ → AdjointableMap B E E := fun n => 1 - uu n
  have he : IsStrongIncreasingModuleResolution ee := hsel.strongModuleResolution hqKleft hqKright
  have hu0 (n : ℕ) : 0 ≤ uu n := hsel.mappedWeight_nonneg n
  have hu1 (n : ℕ) : uu n ≤ 1 := hsel.mappedWeight_le_one n
  have hv0 (n : ℕ) : 0 ≤ vv n := sub_nonneg.mpr (hu1 n)
  have hv1 (n : ℕ) : vv n ≤ 1 := sub_le_self _ (hu0 n)
  let d := IsStrongIncreasingModuleResolution.band ee
  have hdcompact (n : ℕ) : IsModuleCompact (d n) := compact_sequence_band_isModuleCompact e hsel.monotoneK n
  have hband (k : ℕ) : ∀ᶠ n : ℕ in atTop,
      ‖d n * t k - t k * d n‖ < kasparovSelectionBudget n := by
    filter_upwards [eventually_ge_atTop k] with n hn
    exact hsel.band_commutator_bound hτ he n k hn
  have hbandδ (k : ℕ) : ∀ᶠ n : ℕ in atTop,
      ‖d n * δ' k - δ' k * d n‖ < kasparovSelectionBudget n := by
    simpa only [t, (kasparovBandTests_at δ' (fun k => (qU k : AdjointableMap B E E)) b k).1] using hband (3 * k)
  have hbandq (k : ℕ) : ∀ᶠ n : ℕ in atTop,
      ‖d n * (qU k : AdjointableMap B E E) - (qU k : AdjointableMap B E E) * d n‖ <
        kasparovSelectionBudget n := by
    simpa only [t, (kasparovBandTests_at δ' (fun k => (qU k : AdjointableMap B E E)) b k).2.1] using hband (3 * k + 1)
  have hbandb (k : ℕ) : ∀ᶠ n : ℕ in atTop,
      ‖d n * b k - b k * d n‖ < kasparovSelectionBudget n := by
    simpa only [t, (kasparovBandTests_at δ' (fun k => (qU k : AdjointableMap B E E)) b k).2.2] using hband (3 * k + 2)
  have hunit (k : ℕ) : ∀ᶠ n : ℕ in atTop,
      ‖vv n * (qU k : AdjointableMap B E E)‖ < kasparovSelectionBudget n := by
    filter_upwards [eventually_ge_atTop (max 1 k)] with n hn
    exact hsel.complementary_unit_bound n k ((le_max_left 1 k).trans hn) ((le_max_right 1 k).trans hn)
  have hres (k : ℕ) : ∀ᶠ n : ℕ in atTop,
      ‖ee n * (uu n * b k) - uu n * b k‖ < (kasparovSelectionBudget n) ^ 2 / (‖b k‖ + 1) := by
    filter_upwards [eventually_ge_atTop (max 1 k)] with n hn
    exact hsel.products_left n ((le_max_left 1 k).trans hn) k ((le_max_right 1 k).trans hn)
  have hweightδ (k : ℕ) : ∀ᶠ n : ℕ in atTop,
      ‖uu n * δ' k - δ' k * uu n‖ < kasparovSelectionBudget n := by
    filter_upwards [eventually_ge_atTop (max 1 k)] with n hn
    exact hsel.commutatorU n ((le_max_left 1 k).trans hn) k ((le_max_right 1 k).trans hn)
  have hcomplementδ (k : ℕ) : ∀ᶠ n : ℕ in atTop,
      ‖vv n * δ' k - δ' k * vv n‖ < kasparovSelectionBudget n := by
    filter_upwards [hweightδ k] with n hn
    have heq : vv n * δ' k - δ' k * vv n = -(uu n * δ' k - δ' k * uu n) := by
      dsimp [vv]
      noncomm_ring
    simpa only [heq, norm_neg] using hn
  let N := he.partitionSquare uu hu0 hu1
  let M := he.partitionSquare vv hv0 hv1
  have hMq (k : ℕ) : IsModuleCompact (M * (qU k : AdjointableMap B E E)) :=
    he.complementary_partitionSquare_compact_product_of_unit_controls uu hu0 hu1 hdcompact _ (hunit k) (hbandq k)
  have hNb (k : ℕ) : IsModuleCompact (N * b k) :=
    he.partitionSquare_compact_product_of_residual_controls uu hu0 hu1 hdcompact _ (hres k) (hbandb k)
  have hMδ (k : ℕ) : IsModuleCompact (M * δ' k - δ' k * M) :=
    he.partitionSquare_compact_commutator_of_geometric_controls vv hv0 hv1 hdcompact _ (hbandδ k) (hcomplementδ k)
  have hNδ (k : ℕ) : IsModuleCompact (N * δ' k - δ' k * N) :=
    he.partitionSquare_compact_commutator_of_geometric_controls uu hu0 hu1 hdcompact _ (hbandδ k) (hweightδ k)
  have hfirst : ∀ a ∈ E₁, IsModuleCompact (M * a) := fun a ha =>
    compact_products_from_subalgebra_approximateUnit U₁ qU hqU M hMq a (hE₁U ha)
  have hsecond : ∀ a ∈ E₂, IsModuleCompact (N * a) := by
    apply compact_products_from_subalgebra_approximateUnit E₂ q₂ hq₂ N
    intro k
    simpa only [b, (kasparovFamilyTests_at σ (fun k => (q₂ k : AdjointableMap B E E)) f k).1] using hNb (6 * k)
  have hclosures := kasparovNormalizerTests_closure σ δ Δ hΔ
  have hcommM : ∀ a ∈ Δ, IsModuleCompact (M * a - a * M) ∧
      IsModuleCompact (M * J.conjugateOperator a - J.conjugateOperator a * M) := by
    intro a ha
    exact ⟨compact_commutators_from_dense_tests M δ' Δ hclosures.1 hMδ a ha,
      compact_commutators_from_dense_tests M δ' (σ '' Δ) hclosures.2 hMδ _ ⟨a, ha, rfl⟩⟩
  have hcommN : ∀ a ∈ Δ, IsModuleCompact (N * a - a * N) ∧
      IsModuleCompact (N * J.conjugateOperator a - J.conjugateOperator a * N) := by
    intro a ha
    exact ⟨compact_commutators_from_dense_tests N δ' Δ hclosures.1 hNδ a ha,
      compact_commutators_from_dense_tests N δ' (σ '' Δ) hclosures.2 hNδ _ ⟨a, ha, rfl⟩⟩
  have hactions (g : Γ) : IsModuleCompact (V.conjugateOperator g M - M) ∧
      IsModuleCompact (V.conjugateOperator g N - N) := by
    obtain ⟨k, rfl⟩ := hγ g
    have hda : ∀ᶠ n : ℕ in atTop,
        ‖V.conjugateOperator (γ k) (d n) - d n‖ < kasparovSelectionBudget n := by
      filter_upwards [eventually_ge_atTop k] with n hn
      exact hsel.band_action_bound V hαK hτ he n k hn
    have hua : ∀ᶠ n : ℕ in atTop,
        ‖V.conjugateOperator (γ k) (uu n) - uu n‖ < kasparovSelectionBudget n := by
      filter_upwards [eventually_ge_atTop (max 1 k)] with n hn
      exact hsel.mappedWeight_action_bound V hαU n k ((le_max_left 1 k).trans hn) ((le_max_right 1 k).trans hn)
    have hva : ∀ᶠ n : ℕ in atTop,
        ‖V.conjugateOperator (γ k) (vv n) - vv n‖ < kasparovSelectionBudget n := by
      filter_upwards [hua] with n hn
      let ρ := V.conjugateOperatorStarAlgEquiv (γ k)
      have heq : V.conjugateOperator (γ k) (vv n) - vv n =
          -(V.conjugateOperator (γ k) (uu n) - uu n) := by
        change ρ (1 - uu n) - (1 - uu n) = -(ρ (uu n) - uu n)
        rw [map_sub, map_one]
        abel
      simpa only [heq, norm_neg] using hn
    exact ⟨he.partitionSquare_compact_action_error_of_geometric_controls vv hv0 hv1 hdcompact V (γ k) hda hva,
      he.partitionSquare_compact_action_error_of_geometric_controls uu hu0 hu1 hdcompact V (γ k) hda hua⟩
  have hfamily (k : ℕ) : IsModuleCompact (N * f k) ∧ IsModuleCompact (N * star (f k)) ∧
      IsModuleCompact (N * J.conjugateOperator (f k)) ∧ IsModuleCompact (N * J.conjugateOperator (star (f k))) := by
    have h := kasparovFamilyTests_at σ (fun k => (q₂ k : AdjointableMap B E E)) f k
    exact ⟨by simpa only [b, h.2.1] using hNb (6 * k + 1),
      by simpa only [b, h.2.2.1] using hNb (6 * k + 2),
      by simpa only [b, h.2.2.2.1, σ,
        GradedHilbertModule.conjugateOperatorStarAlgEquiv_apply] using hNb (6 * k + 3),
      by simpa only [b, h.2.2.2.2.1, σ,
        GradedHilbertModule.conjugateOperatorStarAlgEquiv_apply] using hNb (6 * k + 4)⟩
  have hMN : M + N = 1 := by
    have h := he.complementary_partitionSquare_add uu hu0 hu1
    rw [add_comm] at h
    exact h
  exact KasparovTechnicalPartition.ofSourceSquares J V hV E₁ E₂ Δ f hE₁ hE₂ M N
    (he.partitionSquare_nonneg vv hv0 hv1) (he.partitionSquare_nonneg uu hu0 hu1)
    ((CStarAlgebra.norm_le_one_iff_of_nonneg _ (he.partitionSquare_nonneg vv hv0 hv1)).mpr
      (he.partitionSquare_le_one vv hv0 hv1))
    ((CStarAlgebra.norm_le_one_iff_of_nonneg _ (he.partitionSquare_nonneg uu hu0 hu1)).mpr
      (he.partitionSquare_le_one uu hu0 hu1))
    hMN hfirst hsecond hcommM hcommN (fun g => (hactions g).1) (fun g => (hactions g).2) hfamily

end BC4lean.KKTheory
