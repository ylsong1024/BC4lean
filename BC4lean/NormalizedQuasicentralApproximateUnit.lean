import BC4lean.CStarQuasicentralRoute

/-! # Approximate units quasicentral for subalgebra normalizers

The coefficient algebra is a subalgebra, and a tested ambient element need
only normalize it by commutators. In a representation this makes the closed
coefficient-generated subspace invariant: the identity
`a(ι(j)v) = ι(j)(av) + [a,ι(j)]v` proves the claim on its generators.
Star normalization makes this a reducing subspace. The resulting support
projection commutes with the tested element, so the actual approximate unit
has weakly vanishing commutators. Hahn–Banach convexification then supplies
finite simultaneous norm controls. Only an explicit countable family of
ambient tests is needed for the sequential selection.
-/

noncomputable section
namespace BC4lean.KKTheory.NormalizedQuasicentral

open scoped InnerProductSpace Topology CStarAlgebra ComplexOrder
open TopologicalSpace
open Filter

section RepresentedSubalgebra

variable {J D H : Type*} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]
  [NonUnitalCStarAlgebra D]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder J] [StarOrderedRing J] in
/-- Commutator normalization makes the represented coefficient-generated
closed subspace invariant under the tested ambient element. -/
theorem representedSubalgebraSubmodule_invariant
    (ι : J →⋆ₙₐ[ℂ] D) (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : D)
    (hnormal : ∀ j : J, ∃ k : J, ι k = a * ι j - ι j * a)
    {v : H} (hv : v ∈ representedIdealSubmodule ι π) :
    π a v ∈ representedIdealSubmodule ι π := by
  let K := representedIdealSubmodule ι π
  let R := K.comap (π a).toLinearMap
  have hRclosed : IsClosed (R : Set H) :=
    (Submodule.span ℂ _).isClosed_topologicalClosure.preimage (π a).continuous
  have hbase : Submodule.span ℂ
      (Set.range (fun p : J × H => π (ι p.1) p.2)) ≤ R := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨j, w⟩, rfl⟩
    obtain ⟨k, hk⟩ := hnormal j
    change π a (π (ι j) w) ∈ K
    have heq : π a (π (ι j) w) = π (ι j) (π a w) + π (ι k) w := by
      rw [hk, map_sub, map_mul, map_mul]
      simp only [sub_apply, mul_apply_eq_comp]
      abel
    rw [heq]
    exact K.add_mem (representedIdealVector_mem ι π j (π a w))
      (representedIdealVector_mem ι π k w)
  exact ((Submodule.span ℂ _).topologicalClosure_minimal hbase hRclosed) hv

omit [PartialOrder J] [StarOrderedRing J] in
/-- Normalization for the tested element and its star makes the actual
represented support projection commute with it. -/
theorem representedSubalgebraProjection_commutes
    (ι : J →⋆ₙₐ[ℂ] D) (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : D)
    (hnormal : ∀ j : J, ∃ k : J, ι k = a * ι j - ι j * a)
    (hnormalStar : ∀ j : J, ∃ k : J, ι k = star a * ι j - ι j * star a)
    (v : H) :
    (representedIdealSubmodule ι π).starProjection (π a v) =
      π a ((representedIdealSubmodule ι π).starProjection v) := by
  apply starProjection_commutes_of_adjoint_invariant
  · exact fun x hx => representedSubalgebraSubmodule_invariant ι π a hnormal hx
  · intro x hx
    have hstar : ContinuousLinearMap.adjoint (π a) = π (star a) := by
      change star (π a) = _
      exact (map_star π a).symm
    rw [hstar]
    exact representedSubalgebraSubmodule_invariant ι π (star a) hnormalStar hx

end RepresentedSubalgebra

section WeakCommutators

variable {A J : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

omit [StarOrderedRing J] in
/-- Every positive functional sees the actual coefficient approximate-unit
commutator with a star normalizer tend to zero. -/
theorem tendsto_positiveFunctional_commutator
    (ι : J →⋆ₙₐ[ℂ] A) (a : A)
    (hnormal : ∀ j : J, ∃ k : J, ι k = a * ι j - ι j * a)
    (hnormalStar : ∀ j : J, ∃ k : J, ι k = star a * ι j - ι j * star a)
    {l : Filter J} (hau : l.IsIncreasingApproximateUnit) (f : A →ₚ[ℂ] ℂ) :
    Tendsto (fun e => f (ι e * a - a * ι e)) l (𝓝 0) := by
  let π := f.gnsNonUnitalStarAlgHom
  let ζ := unitalGNSCyclicVector f
  have hleftlim := tendsto_represented_ideal_approximateUnit ι π hau (π a ζ)
  have hrightlim := (π a).continuous.continuousAt.tendsto.comp
    (tendsto_represented_ideal_approximateUnit ι π hau ζ)
  have hcomm := representedSubalgebraProjection_commutes ι π a hnormal hnormalStar ζ
  have hvector : Tendsto
      (fun e => π (ι e) (π a ζ) - π a (π (ι e) ζ)) l (𝓝 (0 : f.GNS)) := by
    simpa only [Function.comp_def, hcomm, sub_self] using hleftlim.sub hrightlim
  have hpair := (tendsto_const_nhds (x := ζ)).inner (𝕜 := ℂ) hvector
  have heq (e : J) : f (ι e * a - a * ι e) =
      ⟪ζ, π (ι e) (π a ζ) - π a (π (ι e) ζ)⟫_ℂ := by
    have h := unitalGNS_cyclic_pairing f (ι e * a - a * ι e)
    symm
    change ⟪ζ, π (ι e * a - a * ι e) ζ⟫_ℂ = _ at h
    simpa only [map_sub, map_mul, sub_apply, mul_apply_eq_comp] using h
  simpa only [heq, inner_zero_right] using hpair

omit [StarOrderedRing J] in
/-- Actual complex dual decomposition extends the positive-functional
commutator limit to every bounded complex functional. -/
theorem tendsto_strongDual_commutator [Nontrivial A]
    (ι : J →⋆ₙₐ[ℂ] A) (a : A)
    (hnormal : ∀ j : J, ∃ k : J, ι k = a * ι j - ι j * a)
    (hnormalStar : ∀ j : J, ∃ k : J, ι k = star a * ι j - ι j * star a)
    {l : Filter J} (hau : l.IsIncreasingApproximateUnit) (f : StrongDual ℂ A) :
    Tendsto (fun e => f (ι e * a - a * ι e)) l (𝓝 0) := by
  obtain ⟨p, q, r, s, hf⟩ := exists_four_positive_functionals_decomposition f
  have hp := tendsto_positiveFunctional_commutator ι a hnormal hnormalStar hau p
  have hq := tendsto_positiveFunctional_commutator ι a hnormal hnormalStar hau q
  have hr := tendsto_positiveFunctional_commutator ι a hnormal hnormalStar hau r
  have hs := tendsto_positiveFunctional_commutator ι a hnormal hnormalStar hau s
  simpa only [← hf, sub_self, mul_zero, zero_add] using
    (hp.sub hq).add ((hr.sub hs).const_mul Complex.I)

end WeakCommutators

section FiniteSelection

variable {A J : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nontrivial A] [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- Finite ambient star-normalizer, coefficient-automorphism and
two-sided coefficient errors have a genuine positive contractive convex
selection from every specified approximate-unit tail. -/
theorem exists_positive_contraction_finite_errors_in_convexHull_tail
    (ι : J →⋆ₙₐ[ℂ] A) (hι : Function.Injective ι)
    {l : Filter J} (hau : l.IsIncreasingApproximateUnit)
    (sA : Finset A) (sΓ : Finset (J ≃⋆ₐ[ℂ] J)) (sJ : Finset J)
    (hnormal : ∀ a ∈ sA, ∀ j : J, ∃ k : J, ι k = a * ι j - ι j * a)
    (hnormalStar : ∀ a ∈ sA, ∀ j : J, ∃ k : J,
      ι k = star a * ι j - ι j * star a)
    (s : Set J) (hs : s ∈ l) (ε : ℝ) (hε : 0 < ε) :
    ∃ e : J, 0 ≤ e ∧ ‖e‖ ≤ 1 ∧ star e = e ∧ e ∈ convexHull ℝ s ∧
      (∀ a ∈ sA, ‖ι e * a - a * ι e‖ < ε) ∧
      (∀ α ∈ sΓ, ‖α e - e‖ < ε) ∧
      (∀ j ∈ sJ, ‖j * e - j‖ < ε ∧ ‖e * j - j‖ < ε) := by
  classical
  let : l.NeBot := hau.neBot
  let κ := ↥sA ⊕ (↥sΓ ⊕ (↥sJ ⊕ ↥sJ))
  let maps : κ → J →ₗ[ℂ] A := fun k => match k with
    | .inl a => (LinearMap.mulRight ℂ a.1 - LinearMap.mulLeft ℂ a.1).comp (ι : J →ₗ[ℂ] A)
    | .inr (.inl α) => (ι : J →ₗ[ℂ] A).comp ((α.1 : J →ₗ[ℂ] J) - LinearMap.id)
    | .inr (.inr (.inl j)) => (ι : J →ₗ[ℂ] A).comp (LinearMap.mulLeft ℂ j.1)
    | .inr (.inr (.inr j)) => (ι : J →ₗ[ℂ] A).comp (LinearMap.mulRight ℂ j.1)
  let c : κ → A := fun k => match k with
    | .inl _ => 0
    | .inr (.inl _) => 0
    | .inr (.inr (.inl j)) => ι j.1
    | .inr (.inr (.inr j)) => ι j.1
  let L : J →ₗ[ℝ] (κ → A) := (LinearMap.pi maps).restrictScalars ℝ
  have hweak : Tendsto (fun e => toWeakSpace ℝ (κ → A) (L e - c)) l (𝓝 0) := by
    apply tendsto_realWeakSpace_finitePi_of_complex_dual
    intro k f
    rcases k with a | k
    · simpa [L, maps, c] using tendsto_strongDual_commutator ι a.1
        (hnormal a.1 a.2) (hnormalStar a.1 a.2) hau f
    rcases k with α | k
    · simpa [L, maps, c, map_sub] using
        tendsto_strongDual_ideal_automorphism_error ι hau f α.1
    rcases k with j | j
    · have h := ((f.continuous.comp (map_continuous ι)).tendsto (j.1)).comp
        (hau.tendsto_mul_left j.1)
      simpa [L, maps, c, map_sub] using h.sub (tendsto_const_nhds (x := f (ι j.1)))
    · have h := ((f.continuous.comp (map_continuous ι)).tendsto (j.1)).comp
        (hau.tendsto_mul_right j.1)
      simpa [L, maps, c, map_sub] using h.sub (tendsto_const_nhds (x := f (ι j.1)))
  let goodTail : Set J := s ∩ {e | 0 ≤ e ∧ ‖e‖ ≤ 1}
  have hgoodTail : goodTail ∈ l := Filter.inter_mem hs (hau.eventually_nonneg.and hau.eventually_norm)
  obtain ⟨e, he0, he1, heHull, herr⟩ :=
    exists_positive_contraction_affine_error_lt_of_weak_tendsto id L c hweak goodTail hgoodTail
      (fun _ h => h.2.1) (fun _ h => h.2.2) ε hε
  have heHull' : e ∈ convexHull ℝ s := by
    apply convexHull_mono (show goodTail ⊆ s from fun _ h => h.1)
    simpa only [Set.image_id] using heHull
  have hcoord := (pi_norm_lt_iff hε).mp herr
  refine ⟨e, he0, he1, (IsSelfAdjoint.of_nonneg he0).star_eq, heHull', ?_, ?_, ?_⟩
  · intro a ha
    simpa [L, maps, c] using hcoord (Sum.inl ⟨a, ha⟩)
  · intro α hα
    simpa [L, maps, c, ← map_sub, NonUnitalStarAlgHom.norm_map ι hι] using
      hcoord (Sum.inr (Sum.inl ⟨α, hα⟩))
  · intro j hj
    constructor
    · have h := hcoord (Sum.inr (Sum.inr (Sum.inl ⟨j, hj⟩)))
      change ‖ι (j * e) - ι j‖ < ε at h
      rwa [← map_sub, NonUnitalStarAlgHom.norm_map ι hι] at h
    · have h := hcoord (Sum.inr (Sum.inr (Sum.inr ⟨j, hj⟩)))
      change ‖ι (e * j) - ι j‖ < ε at h
      rwa [← map_sub, NonUnitalStarAlgHom.norm_map ι hι] at h

/-- A genuine finite normalized quasicentral selection can dominate any
previous positive strict contraction, by the convex canonical order tail. -/
theorem exists_positive_contraction_finite_errors_above
    (ι : J →⋆ₙₐ[ℂ] A) (hι : Function.Injective ι)
    (p : J) (hp0 : 0 ≤ p) (hp1 : ‖p‖ < 1)
    (sA : Finset A) (sΓ : Finset (J ≃⋆ₐ[ℂ] J)) (sJ : Finset J)
    (hnormal : ∀ a ∈ sA, ∀ j : J, ∃ k : J, ι k = a * ι j - ι j * a)
    (hnormalStar : ∀ a ∈ sA, ∀ j : J, ∃ k : J,
      ι k = star a * ι j - ι j * star a)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ e : J, p ≤ e ∧ 0 ≤ e ∧ ‖e‖ ≤ 1 ∧ star e = e ∧
      (∀ a ∈ sA, ‖ι e * a - a * ι e‖ < ε) ∧
      (∀ α ∈ sΓ, ‖α e - e‖ < ε) ∧
      (∀ j ∈ sJ, ‖j * e - j‖ < ε ∧ ‖e * j - j‖ < ε) := by
  obtain ⟨e, he0, he1, hestar, heHull, heA, heΓ, heJ⟩ :=
    exists_positive_contraction_finite_errors_in_convexHull_tail ι hι
      (CStarAlgebra.increasingApproximateUnit J) sA sΓ sJ hnormal hnormalStar (Set.Ici p)
      (eventually_le_coefficient_approximateUnit p hp0 hp1) ε hε
  have heabove : p ≤ e := by
    change e ∈ Set.Ici p
    rwa [(convex_Ici (𝕜 := ℝ) p).convexHull_eq] at heHull
  exact ⟨e, heabove, he0, he1, hestar, heA, heΓ, heJ⟩

/-- A finite quasicentral approximate-unit selection can both dominate a
previous positive strict contraction and remain a strict contraction. The
small scalar perturbation controls the only nonhomogeneous errors, the
two-sided approximate-unit errors on the finite ideal tests. -/
theorem exists_positive_strict_contraction_finite_errors_above
    (ι : J →⋆ₙₐ[ℂ] A) (hι : Function.Injective ι)
    (p : J) (hp0 : 0 ≤ p) (hp1 : ‖p‖ < 1)
    (sA : Finset A) (sΓ : Finset (J ≃⋆ₐ[ℂ] J)) (sJ : Finset J)
    (hnormal : ∀ a ∈ sA, ∀ j : J, ∃ k : J, ι k = a * ι j - ι j * a)
    (hnormalStar : ∀ a ∈ sA, ∀ j : J, ∃ k : J,
      ι k = star a * ι j - ι j * star a)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ e : J, p ≤ e ∧ 0 ≤ e ∧ ‖e‖ < 1 ∧ star e = e ∧
      (∀ a ∈ sA, ‖ι e * a - a * ι e‖ < ε) ∧
      (∀ α ∈ sΓ, ‖α e - e‖ < ε) ∧
      (∀ j ∈ sJ, ‖j * e - j‖ < ε ∧ ‖e * j - j‖ < ε) := by
  classical
  let K : ℝ := 1 + ∑ j ∈ sJ, ‖j‖
  have hsum0 : 0 ≤ ∑ j ∈ sJ, ‖j‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hK : 0 < K := by dsimp [K]; linarith
  have hηbound : 0 < min ((1 - ‖p‖) / 2) (ε / (2 * K)) :=
    lt_min (by linarith) (div_pos hε (by positivity))
  obtain ⟨η, hη0, hη⟩ := exists_between hηbound
  have hηp : η < (1 - ‖p‖) / 2 := hη.trans_le (min_le_left _ _)
  have hηK : η * K < ε / 2 := by
    have h := hη.trans_le (min_le_right _ _)
    have h' := (lt_div_iff₀ (show 0 < 2 * K by positivity)).mp h
    nlinarith
  let t : ℝ := 1 - η
  have ht0 : 0 < t := by dsimp [t]; have := norm_nonneg p; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hpt : ‖p‖ < t := by dsimp [t]; linarith
  let q : J := t⁻¹ • p
  have hq0 : 0 ≤ q := smul_nonneg (inv_nonneg.mpr ht0.le) hp0
  have hq1 : ‖q‖ < 1 := by
    simp only [q, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht0]
    rw [← div_eq_inv_mul]
    exact (div_lt_one ht0).mpr hpt
  obtain ⟨v, hqv, hv0, hv1, _, hvA, hvΓ, hvJ⟩ :=
    exists_positive_contraction_finite_errors_above ι hι q hq0 hq1
      sA sΓ sJ hnormal hnormalStar (ε / 2) (by positivity)
  let e : J := t • v
  have hep : p ≤ e := by
    calc
      p = t • q := by simp [q, smul_smul, ht0.ne']
      _ ≤ t • v := smul_le_smul_of_nonneg_left hqv ht0.le
  have he0 : 0 ≤ e := smul_nonneg ht0.le hv0
  have he1 : ‖e‖ < 1 := by
    calc
      ‖e‖ = t * ‖v‖ := by simp [e, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      _ ≤ t * 1 := mul_le_mul_of_nonneg_left hv1 ht0.le
      _ < 1 := by dsimp [t]; linarith
  have hscaled (r : ℝ) (hr0 : 0 ≤ r) (hr : r < ε / 2) : t * r < ε := by
    have h := mul_le_mul_of_nonneg_right ht1 hr0
    nlinarith
  have hjK (j : J) (hj : j ∈ sJ) : ‖j‖ ≤ K := by
    have h := Finset.single_le_sum (fun k _ => norm_nonneg k) hj
    dsimp [K]
    linarith
  have hunitScaled (j z : J) (hj : j ∈ sJ) (hz : ‖z‖ < ε / 2) :
      ‖t • z - η • j‖ < ε := by
    have hn : ‖t • z - η • j‖ ≤ t * ‖z‖ + η * ‖j‖ := by
      simpa [norm_smul, Real.norm_eq_abs, abs_of_pos ht0, abs_of_pos hη0] using
        norm_sub_le (t • z) (η • j)
    have hzbound := mul_le_mul_of_nonneg_right ht1 (norm_nonneg z)
    have hjbound := mul_le_mul_of_nonneg_left (hjK j hj) hη0.le
    nlinarith
  refine ⟨e, hep, he0, he1, (IsSelfAdjoint.of_nonneg he0).star_eq, ?_, ?_, ?_⟩
  · intro a ha
    have heq : ι e * a - a * ι e = t • (ι v * a - a * ι v) := by
      simp only [e, LinearMapClass.map_smul_of_tower (S := ℂ), smul_mul_assoc, mul_smul_comm, smul_sub]
    rw [heq]
    rw [norm_smul, Real.norm_of_nonneg ht0.le]
    exact hscaled _ (norm_nonneg _) (hvA a ha)
  · intro α hα
    have heq : α e - e = t • (α v - v) := by
      simp only [e, LinearMapClass.map_smul_of_tower (S := ℂ), smul_sub]
    rw [heq]
    rw [norm_smul, Real.norm_of_nonneg ht0.le]
    exact hscaled _ (norm_nonneg _) (hvΓ α hα)
  · intro j hj
    constructor
    · have heq : j * e - j = t • (j * v - j) - η • j := by
        simp only [e, mul_smul_comm, t]
        module
      rw [heq]
      exact hunitScaled j _ hj (hvJ j hj).1
    · have heq : e * j - j = t • (v * j - j) - η • j := by
        simp only [e, smul_mul_assoc, t]
        module
      rw [heq]
      exact hunitScaled j _ hj (hvJ j hj).2


end FiniteSelection

section CountableTests

variable {A J Γ : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nontrivial A] [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]
  [SeparableSpace J] [Nonempty Γ] [Countable Γ]

/-- An explicit countable family of ambient star normalizers has a genuine
positive contractive quasicentral coefficient approximate-unit sequence,
asymptotically invariant under a countable family of coefficient
automorphisms. The ambient algebra need not be separable. -/
theorem exists_positive_contractive_sequence
    (ι : J →⋆ₙₐ[ℂ] A) (hι : Function.Injective ι) (a : ℕ → A)
    (hnormal : ∀ n, ∀ j : J, ∃ k : J, ι k = a n * ι j - ι j * a n)
    (hnormalStar : ∀ n, ∀ j : J, ∃ k : J,
      ι k = star (a n) * ι j - ι j * star (a n))
    (α : Γ → J ≃⋆ₐ[ℂ] J) :
    ∃ u : ℕ → J, (∀ n, 0 ≤ u n) ∧ (∀ n, ‖u n‖ ≤ 1) ∧
      (∀ n, star (u n) = u n) ∧
      (∀ j : J, Tendsto (fun n => j * u n) atTop (𝓝 j)) ∧
      (∀ j : J, Tendsto (fun n => u n * j) atTop (𝓝 j)) ∧
      (∀ k : ℕ, Tendsto (fun n => ι (u n) * a k - a k * ι (u n)) atTop (𝓝 0)) ∧
      (∀ g : Γ, Tendsto (fun n => α g (u n) - u n) atTop (𝓝 0)) := by
  classical
  let dJ := denseSeq J
  have hdJ : DenseRange dJ := denseRange_denseSeq J
  obtain ⟨γ, hγ⟩ := exists_surjective_nat Γ
  have hchoice : ∀ n : ℕ, ∃ e : J, 0 ≤ e ∧ ‖e‖ ≤ 1 ∧ star e = e ∧
      (∀ k ≤ n, ‖ι e * a k - a k * ι e‖ < 1 / ((n : ℝ) + 1)) ∧
      (∀ k ≤ n, ‖α (γ k) e - e‖ < 1 / ((n : ℝ) + 1)) ∧
      (∀ k ≤ n, ‖dJ k * e - dJ k‖ < 1 / ((n : ℝ) + 1) ∧
        ‖e * dJ k - dJ k‖ < 1 / ((n : ℝ) + 1)) := by
    intro n
    obtain ⟨e, he0, he1, hestar, _, heA, heΓ, heJ⟩ :=
      exists_positive_contraction_finite_errors_in_convexHull_tail ι hι
        (CStarAlgebra.increasingApproximateUnit J)
        ((Finset.range (n + 1)).image a) ((Finset.range (n + 1)).image (fun k => α (γ k)))
        ((Finset.range (n + 1)).image dJ)
        (fun b hb => by
          obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hb
          exact hnormal k)
        (fun b hb => by
          obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hb
          exact hnormalStar k)
        Set.univ Filter.univ_mem (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨e, he0, he1, hestar,
      fun k hk => heA _ (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩),
      fun k hk => heΓ _ (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩),
      fun k hk => heJ _ (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩)⟩
  choose u hu0 hu1 hustar huA huΓ huJ using hchoice
  refine ⟨u, hu0, hu1, hustar, ?_, ?_, ?_, ?_⟩
  · intro j
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp hdJ j (ε / 4) (by positivity)
    have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε / 2 :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
        (gt_mem_nhds (by positivity : 0 < ε / 2))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
    refine ⟨max k N, fun n hn => ?_⟩
    have hkn : k ≤ n := (le_max_left k N).trans hn
    have hNn : N ≤ n := (le_max_right k N).trans hn
    have hsample := (huJ n k hkn).1
    have herror := norm_right_unit_error_le (u n) j (dJ k) (hu1 n)
    rw [dist_eq_norm] at hk ⊢
    have htail := hN n hNn
    linarith
  · intro j
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp hdJ j (ε / 4) (by positivity)
    have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε / 2 :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
        (gt_mem_nhds (by positivity : 0 < ε / 2))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
    refine ⟨max k N, fun n hn => ?_⟩
    have hkn : k ≤ n := (le_max_left k N).trans hn
    have hNn : N ≤ n := (le_max_right k N).trans hn
    have hsample := (huJ n k hkn).2
    have herror := norm_left_unit_error_le (u n) j (dJ k) (hu1 n)
    rw [dist_eq_norm] at hk ⊢
    have htail := hN n hNn
    linarith
  · intro k
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hε)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
    refine ⟨max k N, fun n hn => ?_⟩
    have hkn : k ≤ n := (le_max_left k N).trans hn
    have hNn : N ≤ n := (le_max_right k N).trans hn
    rw [dist_zero_right]
    exact (huA n k hkn).trans (hN n hNn)
  · intro g
    obtain ⟨k, rfl⟩ := hγ g
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hε)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
    refine ⟨max k N, fun n hn => ?_⟩
    have hkn : k ≤ n := (le_max_left k N).trans hn
    have hNn : N ≤ n := (le_max_right k N).trans hn
    rw [dist_zero_right]
    exact (huΓ n k hkn).trans (hN n hNn)


/-- Recursive selections from genuine convex order tails give an increasing
positive contractive quasicentral coefficient approximate-unit sequence,
asymptotically invariant under a countable family of coefficient
automorphisms. The ambient algebra need not be separable. -/
theorem exists_monotone_positive_contractive_sequence
    (ι : J →⋆ₙₐ[ℂ] A) (hι : Function.Injective ι) (a : ℕ → A)
    (hnormal : ∀ n, ∀ j : J, ∃ k : J, ι k = a n * ι j - ι j * a n)
    (hnormalStar : ∀ n, ∀ j : J, ∃ k : J,
      ι k = star (a n) * ι j - ι j * star (a n))
    (α : Γ → J ≃⋆ₐ[ℂ] J) :
    ∃ u : ℕ → J, u 0 = 0 ∧ Monotone u ∧ (∀ n, 0 ≤ u n) ∧ (∀ n, ‖u n‖ ≤ 1) ∧
      (∀ n, star (u n) = u n) ∧
      (∀ j : J, Tendsto (fun n => j * u n) atTop (𝓝 j)) ∧
      (∀ j : J, Tendsto (fun n => u n * j) atTop (𝓝 j)) ∧
      (∀ k : ℕ, Tendsto (fun n => ι (u n) * a k - a k * ι (u n)) atTop (𝓝 0)) ∧
      (∀ g : Γ, Tendsto (fun n => α g (u n) - u n) atTop (𝓝 0)) := by
  classical
  let dJ := denseSeq J
  have hdJ : DenseRange dJ := denseRange_denseSeq J
  obtain ⟨γ, hγ⟩ := exists_surjective_nat Γ
  let P := {p : J // 0 ≤ p ∧ ‖p‖ < 1}
  have hchoice : ∀ (n : ℕ) (p : P), ∃ e : J, (p : J) ≤ e ∧ 0 ≤ e ∧ ‖e‖ < 1 ∧
      star e = e ∧
      (∀ k ≤ n, ‖ι e * a k - a k * ι e‖ < 1 / ((n : ℝ) + 1)) ∧
      (∀ k ≤ n, ‖α (γ k) e - e‖ < 1 / ((n : ℝ) + 1)) ∧
      (∀ k ≤ n, ‖dJ k * e - dJ k‖ < 1 / ((n : ℝ) + 1) ∧
        ‖e * dJ k - dJ k‖ < 1 / ((n : ℝ) + 1)) := by
    intro n p
    obtain ⟨e, hep, he0, he1, hestar, heA, heΓ, heJ⟩ :=
      exists_positive_strict_contraction_finite_errors_above ι hι p.val p.property.1 p.property.2
        ((Finset.range (n + 1)).image a) ((Finset.range (n + 1)).image (fun k => α (γ k)))
        ((Finset.range (n + 1)).image dJ)
        (fun b hb => by
          obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hb
          exact hnormal k)
        (fun b hb => by
          obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hb
          exact hnormalStar k)
        (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨e, hep, he0, he1, hestar,
      fun k hk => heA _ (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩),
      fun k hk => heΓ _ (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩),
      fun k hk => heJ _ (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩)⟩
  choose v hvAbove hv0 hv1 _hvStar hvA hvΓ hvJ using hchoice
  let uRec : ℕ → P := Nat.rec ⟨0, by simp⟩
    (fun n p => ⟨v n p, hv0 n p, hv1 n p⟩)
  let u : ℕ → J := fun n => (uRec n).val
  have hu0 (n : ℕ) : 0 ≤ u n := (uRec n).property.1
  have hu1 (n : ℕ) : ‖u n‖ ≤ 1 := (uRec n).property.2.le
  have hustar (n : ℕ) : star (u n) = u n := (IsSelfAdjoint.of_nonneg (hu0 n)).star_eq
  have huMono : Monotone u := by
    apply monotone_nat_of_le_succ
    intro n
    exact hvAbove n (uRec n)
  have huA (n k : ℕ) (hk : k ≤ n) :
      ‖ι (u (n + 1)) * a k - a k * ι (u (n + 1))‖ < 1 / ((n : ℝ) + 1) :=
    hvA n (uRec n) k hk
  have huΓ (n k : ℕ) (hk : k ≤ n) :
      ‖α (γ k) (u (n + 1)) - u (n + 1)‖ < 1 / ((n : ℝ) + 1) :=
    hvΓ n (uRec n) k hk
  have huJ (n k : ℕ) (hk : k ≤ n) :
      ‖dJ k * u (n + 1) - dJ k‖ < 1 / ((n : ℝ) + 1) ∧
        ‖u (n + 1) * dJ k - dJ k‖ < 1 / ((n : ℝ) + 1) :=
    hvJ n (uRec n) k hk
  refine ⟨u, rfl, huMono, hu0, hu1, hustar, ?_, ?_, ?_, ?_⟩
  · intro j
    apply (tendsto_add_atTop_iff_nat 1).mp
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp hdJ j (ε / 4) (by positivity)
    have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε / 2 :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
        (gt_mem_nhds (by positivity : 0 < ε / 2))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
    refine ⟨max k N, fun n hn => ?_⟩
    have hkn : k ≤ n := (le_max_left k N).trans hn
    have hNn : N ≤ n := (le_max_right k N).trans hn
    have hsample := (huJ n k hkn).1
    have herror := norm_right_unit_error_le (u (n + 1)) j (dJ k) (hu1 (n + 1))
    rw [dist_eq_norm] at hk ⊢
    have htail := hN n hNn
    linarith
  · intro j
    apply (tendsto_add_atTop_iff_nat 1).mp
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp hdJ j (ε / 4) (by positivity)
    have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε / 2 :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
        (gt_mem_nhds (by positivity : 0 < ε / 2))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
    refine ⟨max k N, fun n hn => ?_⟩
    have hkn : k ≤ n := (le_max_left k N).trans hn
    have hNn : N ≤ n := (le_max_right k N).trans hn
    have hsample := (huJ n k hkn).2
    have herror := norm_left_unit_error_le (u (n + 1)) j (dJ k) (hu1 (n + 1))
    rw [dist_eq_norm] at hk ⊢
    have htail := hN n hNn
    linarith
  · intro k
    apply (tendsto_add_atTop_iff_nat 1).mp
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hε)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
    refine ⟨max k N, fun n hn => ?_⟩
    have hkn : k ≤ n := (le_max_left k N).trans hn
    have hNn : N ≤ n := (le_max_right k N).trans hn
    rw [dist_zero_right]
    exact (huA n k hkn).trans (hN n hNn)
  · intro g
    obtain ⟨k, rfl⟩ := hγ g
    apply (tendsto_add_atTop_iff_nat 1).mp
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hε)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
    refine ⟨max k N, fun n hn => ?_⟩
    have hkn : k ≤ n := (le_max_left k N).trans hn
    have hNn : N ≤ n := (le_max_right k N).trans hn
    rw [dist_zero_right]
    exact (huΓ n k hkn).trans (hN n hNn)

end CountableTests

section NonunitalCountableTests

variable {D J Γ : Type*} [NonUnitalCStarAlgebra D]
  [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]
  [SeparableSpace J] [Nonempty Γ] [Countable Γ]

local instance : PartialOrder D := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing D := CStarAlgebra.spectralOrderedRing _

/-- Unitization gives the same genuine countable-test selection in an
arbitrary ambient C⋆-algebra, including zero algebras. Its ambient algebra
does not need a separability instance. -/
theorem exists_positive_contractive_nonunital_sequence
    (ι : J →⋆ₙₐ[ℂ] D) (hι : Function.Injective ι) (a : ℕ → D)
    (hnormal : ∀ n, ∀ j : J, ∃ k : J, ι k = a n * ι j - ι j * a n)
    (hnormalStar : ∀ n, ∀ j : J, ∃ k : J,
      ι k = star (a n) * ι j - ι j * star (a n))
    (α : Γ → J ≃⋆ₐ[ℂ] J) :
    ∃ u : ℕ → J, (∀ n, 0 ≤ u n) ∧ (∀ n, ‖u n‖ ≤ 1) ∧
      (∀ n, star (u n) = u n) ∧
      (∀ j : J, Tendsto (fun n => j * u n) atTop (𝓝 j)) ∧
      (∀ j : J, Tendsto (fun n => u n * j) atTop (𝓝 j)) ∧
      (∀ k : ℕ, Tendsto (fun n => ι (u n) * a k - a k * ι (u n)) atTop (𝓝 0)) ∧
      (∀ g : Γ, Tendsto (fun n => α g (u n) - u n) atTop (𝓝 0)) := by
  let η := (Unitization.inrNonUnitalStarAlgHom ℂ D).comp ι
  have hη : Function.Injective η := Unitization.inr_injective.comp hι
  let b : ℕ → Unitization ℂ D := fun n => Unitization.inr (a n)
  have hnormal' : ∀ n, ∀ j : J, ∃ k : J, η k = b n * η j - η j * b n := by
    intro n j
    obtain ⟨k, hk⟩ := hnormal n j
    refine ⟨k, ?_⟩
    simpa [η, b, Function.comp_def, ← Unitization.inr_mul, ← Unitization.inr_sub] using
      congrArg (Unitization.inr : D → Unitization ℂ D) hk
  have hnormalStar' : ∀ n, ∀ j : J, ∃ k : J,
      η k = star (b n) * η j - η j * star (b n) := by
    intro n j
    obtain ⟨k, hk⟩ := hnormalStar n j
    refine ⟨k, ?_⟩
    simpa [η, b, Function.comp_def, ← Unitization.inr_mul, ← Unitization.inr_sub, ← Unitization.inr_star] using
      congrArg (Unitization.inr : D → Unitization ℂ D) hk
  obtain ⟨u, hu0, hu1, hustar, hleft, hright, hcomm, hΓ⟩ :=
    exists_positive_contractive_sequence η hη b hnormal' hnormalStar' α
  refine ⟨u, hu0, hu1, hustar, hleft, hright, ?_, hΓ⟩
  intro k
  apply (Unitization.isometry_inr (𝕜 := ℂ) (A := D)).tendsto_nhds_iff.mpr
  simpa [η, b, Function.comp_def, ← Unitization.inr_mul, ← Unitization.inr_sub] using hcomm k


/-- Unitization gives the same genuine countable-test selection in an
arbitrary ambient C⋆-algebra, including zero algebras. Its ambient algebra
does not need a separability instance. -/
theorem exists_monotone_positive_contractive_nonunital_sequence
    (ι : J →⋆ₙₐ[ℂ] D) (hι : Function.Injective ι) (a : ℕ → D)
    (hnormal : ∀ n, ∀ j : J, ∃ k : J, ι k = a n * ι j - ι j * a n)
    (hnormalStar : ∀ n, ∀ j : J, ∃ k : J,
      ι k = star (a n) * ι j - ι j * star (a n))
    (α : Γ → J ≃⋆ₐ[ℂ] J) :
    ∃ u : ℕ → J, u 0 = 0 ∧ Monotone u ∧ (∀ n, 0 ≤ u n) ∧ (∀ n, ‖u n‖ ≤ 1) ∧
      (∀ n, star (u n) = u n) ∧
      (∀ j : J, Tendsto (fun n => j * u n) atTop (𝓝 j)) ∧
      (∀ j : J, Tendsto (fun n => u n * j) atTop (𝓝 j)) ∧
      (∀ k : ℕ, Tendsto (fun n => ι (u n) * a k - a k * ι (u n)) atTop (𝓝 0)) ∧
      (∀ g : Γ, Tendsto (fun n => α g (u n) - u n) atTop (𝓝 0)) := by
  let η := (Unitization.inrNonUnitalStarAlgHom ℂ D).comp ι
  have hη : Function.Injective η := Unitization.inr_injective.comp hι
  let b : ℕ → Unitization ℂ D := fun n => Unitization.inr (a n)
  have hnormal' : ∀ n, ∀ j : J, ∃ k : J, η k = b n * η j - η j * b n := by
    intro n j
    obtain ⟨k, hk⟩ := hnormal n j
    refine ⟨k, ?_⟩
    simpa [η, b, Function.comp_def, ← Unitization.inr_mul, ← Unitization.inr_sub] using
      congrArg (Unitization.inr : D → Unitization ℂ D) hk
  have hnormalStar' : ∀ n, ∀ j : J, ∃ k : J,
      η k = star (b n) * η j - η j * star (b n) := by
    intro n j
    obtain ⟨k, hk⟩ := hnormalStar n j
    refine ⟨k, ?_⟩
    simpa [η, b, Function.comp_def, ← Unitization.inr_mul, ← Unitization.inr_sub, ← Unitization.inr_star] using
      congrArg (Unitization.inr : D → Unitization ℂ D) hk
  obtain ⟨u, huZero, huMono, hu0, hu1, hustar, hleft, hright, hcomm, hΓ⟩ :=
    exists_monotone_positive_contractive_sequence η hη b hnormal' hnormalStar' α
  refine ⟨u, huZero, huMono, hu0, hu1, hustar, hleft, hright, ?_, hΓ⟩
  intro k
  apply (Unitization.isometry_inr (𝕜 := ℂ) (A := D)).tendsto_nhds_iff.mpr
  simpa [η, b, Function.comp_def, ← Unitization.inr_mul, ← Unitization.inr_sub] using hcomm k

end NonunitalCountableTests

end BC4lean.KKTheory.NormalizedQuasicentral
