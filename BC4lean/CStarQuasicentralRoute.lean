import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.RCLike.Extend
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Countable.Defs
import Mathlib.Tactic.Module
import BC4lean.CStarFunctionalDecomposition


noncomputable section

namespace BC4lean.KKTheory

open scoped ComplexOrder InnerProductSpace Topology CStarAlgebra
open UniformSpace TopologicalSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

section ReducingSubspace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A closed invariant subspace for an operator and its adjoint is reducing;
the actual orthogonal projection commutes with that operator. -/
theorem starProjection_commutes_of_adjoint_invariant
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] (T : H →L[ℂ] H)
    (hT : ∀ x ∈ K, T x ∈ K) (hTadj : ∀ x ∈ K, (ContinuousLinearMap.adjoint T) x ∈ K)
    (x : H) : K.starProjection (T x) = T (K.starProjection x) := by
  have horth (z : H) (hz : z ∈ Kᗮ) : T z ∈ Kᗮ := by
    apply (K.mem_orthogonal (T z)).mpr
    intro y hy
    rw [← ContinuousLinearMap.adjoint_inner_left T z y]
    exact Submodule.inner_right_of_mem_orthogonal (hTadj y hy) hz
  apply (K.eq_starProjection_of_mem_orthogonal
    (hT _ (K.starProjection_apply_mem x)) ?_)
  rw [← map_sub]
  exact horth _ (K.sub_starProjection_mem_orthogonal x)

end ReducingSubspace

section StrongConvergenceClosure

variable {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] {l : Filter ι}

/-- An eventual uniform operator bound extends strong convergence to the
actual norm closure of a set. -/
theorem tendsto_apply_of_mem_closure_of_eventually_norm_le
    (T : ι → H →L[ℂ] H) (S : H →L[ℂ] H) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᶠ i in l, ‖T i‖ ≤ C) (s : Set H)
    (hs : ∀ y ∈ s, Filter.Tendsto (fun i => T i y) l (𝓝 (S y)))
    {x : H} (hx : x ∈ closure s) :
    Filter.Tendsto (fun i => T i x) l (𝓝 (S x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hd : 0 < 2 * (C + ‖S‖ + 1) := by positivity
  obtain ⟨y, hys, hxy⟩ := Metric.mem_closure_iff.mp hx
    (ε / (2 * (C + ‖S‖ + 1))) (div_pos hε hd)
  have hy : ‖x - y‖ * (2 * (C + ‖S‖ + 1)) < ε := by
    rw [dist_eq_norm] at hxy
    exact (lt_div_iff₀ hd).mp hxy
  have hsmall : ∀ᶠ i in l, ‖T i y - S y‖ < ε / 2 := by
    have ht := (hs y hys).sub (tendsto_const_nhds (x := S y))
    have hn := ht.norm
    simpa only [sub_self, norm_zero] using
      hn.eventually (gt_mem_nhds (show ‖S y - S y‖ < ε / 2 by simpa using (show (0 : ℝ) < ε / 2 by positivity)))
  filter_upwards [hbound, hsmall] with i hi hiy
  rw [dist_eq_norm]
  have hnorm : ‖T i x - S x‖ ≤
      (C + ‖S‖) * ‖x - y‖ + ‖T i y - S y‖ := by
    calc
      ‖T i x - S x‖ = ‖T i (x - y) + (T i y - S y) + S (y - x)‖ := by
        congr 1
        simp only [map_sub]
        abel
      _ ≤ ‖T i (x - y)‖ + ‖T i y - S y‖ + ‖S (y - x)‖ := norm_add₃_le
      _ ≤ (‖T i‖ * ‖x - y‖) + ‖T i y - S y‖ + ‖S‖ * ‖y - x‖ := by
        gcongr
        · exact (T i).le_opNorm _
        · exact S.le_opNorm _
      _ ≤ C * ‖x - y‖ + ‖T i y - S y‖ + ‖S‖ * ‖y - x‖ := by gcongr
      _ = _ := by rw [norm_sub_rev y x]; ring
  have houter : (C + ‖S‖) * ‖x - y‖ < ε / 2 := by
    have hnonneg : 0 ≤ ‖x - y‖ := norm_nonneg _
    nlinarith
  linarith

/-- The vectors where a uniformly bounded operator family has a specified
strong linear limit form a closed complex submodule. -/
def strongConvergenceSubmodule (T : ι → H →L[ℂ] H) (S : H →L[ℂ] H) : Submodule ℂ H where
  carrier := {x | Filter.Tendsto (fun i => T i x) l (𝓝 (S x))}
  zero_mem' := by
    change Filter.Tendsto (fun i => T i 0) l (𝓝 (S 0))
    simpa using (tendsto_const_nhds (f := l) (x := (0 : H)))
  add_mem' := fun hx hy => by
    change Filter.Tendsto (fun i => T i (_ + _)) l (𝓝 (S (_ + _)))
    simpa only [map_add] using hx.add hy
  smul_mem' := fun c x hx => by
    change Filter.Tendsto (fun i => T i (c • x)) l (𝓝 (S (c • x)))
    simpa only [map_smul] using hx.const_smul c

theorem strongConvergenceSubmodule_isClosed
    (T : ι → H →L[ℂ] H) (S : H →L[ℂ] H) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᶠ i in l, ‖T i‖ ≤ C) :
    IsClosed (strongConvergenceSubmodule (l := l) T S : Set H) := by
  apply closure_subset_iff_isClosed.mp
  intro x hx
  exact tendsto_apply_of_mem_closure_of_eventually_norm_le T S C hC hbound _
    (fun _ hy => hy) hx

end StrongConvergenceClosure

section RepresentedIdeal

open scoped CStarAlgebra

variable {J D H : Type*} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]
  [NonUnitalCStarAlgebra D] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual closed subspace generated by a represented coefficient ideal. -/
def representedIdealSubmodule (ι : J →⋆ₙₐ[ℂ] D)
    (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : Submodule ℂ H :=
  (Submodule.span ℂ (Set.range (fun p : J × H => π (ι p.1) p.2))).topologicalClosure

instance representedIdealSubmodule_completeSpace (ι : J →⋆ₙₐ[ℂ] D)
    (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : CompleteSpace (representedIdealSubmodule ι π) :=
  inferInstanceAs (CompleteSpace
    ((Submodule.span ℂ (Set.range (fun p : J × H => π (ι p.1) p.2))).topologicalClosure))

omit [PartialOrder J] [StarOrderedRing J] in
theorem representedIdealVector_mem (ι : J →⋆ₙₐ[ℂ] D)
    (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (j : J) (v : H) :
    π (ι j) v ∈ representedIdealSubmodule ι π :=
  (Submodule.span ℂ _).le_topologicalClosure
    (Submodule.subset_span ⟨(j, v), rfl⟩)

omit [PartialOrder J] [StarOrderedRing J] in
/-- Every represented ideal coefficient kills the orthogonal complement of
the closed ideal-generated subspace. -/
theorem representedIdeal_apply_eq_zero_of_mem_orthogonal
    (ι : J →⋆ₙₐ[ℂ] D) (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (j : J) {v : H}
    (hv : v ∈ (representedIdealSubmodule ι π)ᗮ) : π (ι j) v = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [← ContinuousLinearMap.adjoint_inner_left (π (ι j)) v (π (ι j) v)]
  have hstar : ContinuousLinearMap.adjoint (π (ι j)) = π (ι (star j)) := by
    change star (π (ι j)) = _
    exact (map_star π (ι j)).symm.trans (congrArg π (map_star ι j).symm)
  rw [hstar]
  exact Submodule.inner_right_of_mem_orthogonal
    (representedIdealVector_mem ι π (star j) (π (ι j) v)) hv

omit [StarOrderedRing J] in
/-- Any actual positive contractive coefficient approximate-unit filter
converges strongly in a representation to the projection onto the actual
closed ideal-generated subspace. This requires no unit on the ideal. -/
theorem tendsto_represented_ideal_approximateUnit
    (ι : J →⋆ₙₐ[ℂ] D) (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    {l : Filter J} (hau : l.IsIncreasingApproximateUnit) (v : H) :
    Filter.Tendsto (fun e => π (ι e) v) l
      (𝓝 ((representedIdealSubmodule ι π).starProjection v)) := by
  let K := representedIdealSubmodule ι π
  let T : J → H →L[ℂ] H := fun e => π (ι e)
  let S : H →L[ℂ] H := ContinuousLinearMap.id ℂ H
  let C := strongConvergenceSubmodule (l := l) T S
  have hbound : ∀ᶠ e in l, ‖T e‖ ≤ 1 := by
    filter_upwards [hau.eventually_norm] with e he
    exact (NonUnitalStarAlgHom.norm_apply_le π (ι e)).trans
      ((NonUnitalStarAlgHom.norm_apply_le ι e).trans he)
  have hCclosed : IsClosed (C : Set H) :=
    strongConvergenceSubmodule_isClosed T S 1 zero_le_one hbound
  have hbase : Submodule.span ℂ
      (Set.range (fun p : J × H => π (ι p.1) p.2)) ≤ C := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨j, w⟩, rfl⟩
    change Filter.Tendsto (fun e => T e (π (ι j) w)) l (𝓝 (S (π (ι j) w)))
    have hcont : Continuous (fun a : J => π (ι a) w) :=
      (ContinuousLinearMap.apply ℂ H w).continuous.comp
        ((map_continuous π).comp (map_continuous ι))
    have hlim := hcont.continuousAt.tendsto.comp (hau.tendsto_mul_right j)
    simpa only [Function.comp_def, T, map_mul, mul_apply_eq_comp, S, ContinuousLinearMap.id_apply]
      using hlim
  have hK : K ≤ C := (Submodule.span ℂ _).topologicalClosure_minimal hbase hCclosed
  obtain ⟨y, hy, z, hz, hv⟩ := Submodule.exists_add_mem_mem_orthogonal (K := K) v
  have hyconv : Filter.Tendsto (fun e => T e y) l (𝓝 y) := by
    have h := hK hy
    change Filter.Tendsto (fun e => T e y) l (𝓝 (S y)) at h
    simpa only [S, ContinuousLinearMap.id_apply] using h
  have hzero (e : J) : T e z = 0 :=
    representedIdeal_apply_eq_zero_of_mem_orthogonal ι π e hz
  have hzconv : Filter.Tendsto (fun e => T e z) l (𝓝 (0 : H)) := by
    simpa only [hzero] using (tendsto_const_nhds (f := l) (x := (0 : H)))
  have hproj : K.starProjection v = y := by
    rw [hv, map_add, K.starProjection_eq_self_iff.mpr hy]
    have hzproj : K.starProjection z = 0 := by
      simp only [Submodule.starProjection_apply,
        Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hz, Submodule.coe_zero]
    rw [hzproj, add_zero]
  rw [hproj, hv]
  simpa only [T, map_add, add_zero] using hyconv.add hzconv

omit [PartialOrder J] [StarOrderedRing J] in
/-- If the represented coefficient range is an ambient left ideal, the
closed ideal-generated subspace is invariant under every ambient operator. -/
theorem representedIdealSubmodule_invariant
    (ι : J →⋆ₙₐ[ℂ] D) (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hleft : ∀ a : D, ∀ j : J, ∃ k : J, ι k = a * ι j)
    (a : D) {v : H} (hv : v ∈ representedIdealSubmodule ι π) :
    π a v ∈ representedIdealSubmodule ι π := by
  let K := representedIdealSubmodule ι π
  let R := K.comap (π a).toLinearMap
  have hRclosed : IsClosed (R : Set H) :=
    (Submodule.span ℂ _).isClosed_topologicalClosure.preimage (π a).continuous
  have hbase : Submodule.span ℂ
      (Set.range (fun p : J × H => π (ι p.1) p.2)) ≤ R := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨j, w⟩, rfl⟩
    obtain ⟨k, hk⟩ := hleft a j
    change π a (π (ι j) w) ∈ K
    rw [← mul_apply_eq_comp, ← map_mul, ← hk]
    exact representedIdealVector_mem ι π k w
  exact ((Submodule.span ℂ _).topologicalClosure_minimal hbase hRclosed) hv

omit [PartialOrder J] [StarOrderedRing J] in
/-- The actual limiting ideal projection commutes with every ambient
operator, because the ideal-generated subspace is invariant for both the
operator and its adjoint. -/
theorem representedIdealProjection_commutes
    (ι : J →⋆ₙₐ[ℂ] D) (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hleft : ∀ a : D, ∀ j : J, ∃ k : J, ι k = a * ι j)
    (a : D) (v : H) :
    (representedIdealSubmodule ι π).starProjection (π a v) =
      π a ((representedIdealSubmodule ι π).starProjection v) := by
  apply starProjection_commutes_of_adjoint_invariant
  · exact fun x hx => representedIdealSubmodule_invariant ι π hleft a hx
  · intro x hx
    have hstar : ContinuousLinearMap.adjoint (π a) = π (star a) := by
      change star (π a) = _
      exact (map_star π a).symm
    rw [hstar]
    exact representedIdealSubmodule_invariant ι π hleft (star a) hx

end RepresentedIdeal

section MappedApproximateUnit

open scoped CStarAlgebra

variable {J : Type*} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- Every actual ideal automorphism carries an increasing coefficient
approximate-unit filter to an increasing coefficient approximate-unit
filter. Its order and norm data follow from genuine ⋆-square positivity and
the norm isometry of a ⋆-algebra equivalence. -/
theorem increasingApproximateUnit_map_starAlgEquiv
    {l : Filter J} (hau : l.IsIncreasingApproximateUnit) (α : J ≃⋆ₐ[ℂ] J) :
    (Filter.map α l).IsIncreasingApproximateUnit where
  neBot := hau.neBot.map α
  tendsto_mul_left a := by
    rw [Filter.tendsto_map'_iff]
    have h := (NonUnitalStarAlgHom.isometry α α.injective).continuous.continuousAt.tendsto.comp
      (hau.tendsto_mul_left (α.symm a))
    simpa only [Function.comp_def, map_mul, α.apply_symm_apply] using h
  tendsto_mul_right a := by
    rw [Filter.tendsto_map'_iff]
    have h := (NonUnitalStarAlgHom.isometry α α.injective).continuous.continuousAt.tendsto.comp
      (hau.tendsto_mul_right (α.symm a))
    simpa only [Function.comp_def, map_mul, α.apply_symm_apply] using h
  eventually_nonneg := by
    change ∀ᶠ e in l, 0 ≤ α e
    filter_upwards [hau.eventually_nonneg] with e he
    obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp he
    simpa only [map_mul, map_star] using star_mul_self_nonneg (α b)
  eventually_norm := by
    change ∀ᶠ e in l, ‖α e‖ ≤ 1
    simpa only [StarAlgEquiv.norm_map] using hau.eventually_norm

end MappedApproximateUnit

section PositiveWeakErrors

open scoped CStarAlgebra

variable {J : Type*} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

omit [StarOrderedRing J] in
/-- The genuine ideal approximate unit has vanishing ambient commutator
errors under every positive bounded functional, by actual unital GNS and
the proved strong ideal-projection limit. -/
theorem tendsto_positiveFunctional_ideal_commutator
    (ι : J →⋆ₙₐ[ℂ] A)
    (hleft : ∀ a : A, ∀ j : J, ∃ k : J, ι k = a * ι j)
    {l : Filter J} (hau : l.IsIncreasingApproximateUnit)
    (f : A →ₚ[ℂ] ℂ) (a : A) :
    Filter.Tendsto (fun e => f (ι e * a - a * ι e)) l (𝓝 0) := by
  let π := f.gnsNonUnitalStarAlgHom
  let ζ := unitalGNSCyclicVector f
  have hleftlim := tendsto_represented_ideal_approximateUnit ι π hau (π a ζ)
  have hrightlim := (π a).continuous.continuousAt.tendsto.comp
    (tendsto_represented_ideal_approximateUnit ι π hau ζ)
  have hcomm := representedIdealProjection_commutes ι π hleft a ζ
  have hvector : Filter.Tendsto
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

/-- Every ideal automorphic image of the actual approximate unit has the
same represented support projection, so positive functionals see its
invariance error tend to zero. No amenability hypothesis is used. -/
theorem tendsto_positiveFunctional_ideal_automorphism_error
    (ι : J →⋆ₙₐ[ℂ] A) {l : Filter J} (hau : l.IsIncreasingApproximateUnit)
    (f : A →ₚ[ℂ] ℂ) (α : J ≃⋆ₐ[ℂ] J) :
    Filter.Tendsto (fun e => f (ι (α e) - ι e)) l (𝓝 0) := by
  let π := f.gnsNonUnitalStarAlgHom
  let ζ := unitalGNSCyclicVector f
  have hαau := increasingApproximateUnit_map_starAlgEquiv hau α
  have hα := tendsto_represented_ideal_approximateUnit ι π hαau ζ
  rw [Filter.tendsto_map'_iff] at hα
  have hzero : Filter.Tendsto (fun e => π (ι (α e)) ζ - π (ι e) ζ)
      l (𝓝 (0 : f.GNS)) := by
    simpa only [Function.comp_def, sub_self] using hα.sub
      (tendsto_represented_ideal_approximateUnit ι π hau ζ)
  have hpair := (tendsto_const_nhds (x := ζ)).inner (𝕜 := ℂ) hzero
  have heq (e : J) : f (ι (α e) - ι e) =
      ⟪ζ, π (ι (α e)) ζ - π (ι e) ζ⟫_ℂ := by
    have h := unitalGNS_cyclic_pairing f (ι (α e) - ι e)
    symm
    change ⟪ζ, π (ι (α e) - ι e) ζ⟫_ℂ = _ at h
    simpa only [map_sub, sub_apply] using h
  simpa only [heq, inner_zero_right] using hpair

end PositiveWeakErrors

section GeneralWeakErrors

open scoped CStarAlgebra

variable {J : Type*} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder J] [StarOrderedRing J] in
/-- Complex Hahn–Banach extends every ideal dual functional along an
injective C⋆-homomorphism; its isometry is proved by the C⋆-norm theorem. -/
theorem exists_strongDual_extension_along_injective_cstarHom
    (ι : J →⋆ₙₐ[ℂ] A) (hι : Function.Injective ι) (f : StrongDual ℂ J) :
    ∃ F : StrongDual ℂ A, ∀ j : J, F (ι j) = f j := by
  let L : J →ₗᵢ[ℂ] A :=
    { toLinearMap := (ι : J →ₗ[ℂ] A)
      norm_map' := NonUnitalStarAlgHom.norm_map ι hι }
  let e := L.equivRange.toContinuousLinearEquiv
  let frange : StrongDual ℂ L.toLinearMap.range := f.comp e.symm.toContinuousLinearMap
  obtain ⟨F, hF, _⟩ := exists_extension_norm_eq L.toLinearMap.range frange
  refine ⟨F, fun j => ?_⟩
  have h := hF (e j)
  have he : ((e j : L.toLinearMap.range) : A) = ι j := rfl
  rw [he] at h
  change F (ι j) = f (e.symm (e j)) at h
  rwa [e.symm_apply_apply] at h

omit [StarOrderedRing J] in
/-- Every ambient bounded complex functional sees the actual ideal AU
commutator errors tend to zero, without assuming weak convergence. -/
theorem tendsto_strongDual_ideal_commutator [Nontrivial A]
    (ι : J →⋆ₙₐ[ℂ] A)
    (hleft : ∀ a : A, ∀ j : J, ∃ k : J, ι k = a * ι j)
    {l : Filter J} (hau : l.IsIncreasingApproximateUnit)
    (f : StrongDual ℂ A) (a : A) :
    Filter.Tendsto (fun e => f (ι e * a - a * ι e)) l (𝓝 0) := by
  obtain ⟨p, q, r, s, hf⟩ := exists_four_positive_functionals_decomposition f
  have hp := tendsto_positiveFunctional_ideal_commutator ι hleft hau p a
  have hq := tendsto_positiveFunctional_ideal_commutator ι hleft hau q a
  have hr := tendsto_positiveFunctional_ideal_commutator ι hleft hau r a
  have hs := tendsto_positiveFunctional_ideal_commutator ι hleft hau s a
  simpa only [← hf, sub_self, mul_zero, zero_add] using
    (hp.sub hq).add ((hr.sub hs).const_mul Complex.I)

/-- Every ambient bounded complex functional sees every actual ideal
automorphism error of the AU tend to zero. -/
theorem tendsto_strongDual_ideal_automorphism_error [Nontrivial A]
    (ι : J →⋆ₙₐ[ℂ] A) {l : Filter J} (hau : l.IsIncreasingApproximateUnit)
    (f : StrongDual ℂ A) (α : J ≃⋆ₐ[ℂ] J) :
    Filter.Tendsto (fun e => f (ι (α e) - ι e)) l (𝓝 0) := by
  obtain ⟨p, q, r, s, hf⟩ := exists_four_positive_functionals_decomposition f
  have hp := tendsto_positiveFunctional_ideal_automorphism_error ι hau p α
  have hq := tendsto_positiveFunctional_ideal_automorphism_error ι hau q α
  have hr := tendsto_positiveFunctional_ideal_automorphism_error ι hau r α
  have hs := tendsto_positiveFunctional_ideal_automorphism_error ι hau s α
  simpa only [← hf, sub_self, mul_zero, zero_add] using
    (hp.sub hq).add ((hr.sub hs).const_mul Complex.I)

/-- The ideal dual convergence for group errors follows from the actual
norm-isometric inclusion and complex Hahn–Banach extension. -/
theorem tendsto_idealStrongDual_automorphism_error [Nontrivial A]
    (ι : J →⋆ₙₐ[ℂ] A) (hι : Function.Injective ι)
    {l : Filter J} (hau : l.IsIncreasingApproximateUnit)
    (f : StrongDual ℂ J) (α : J ≃⋆ₐ[ℂ] J) :
    Filter.Tendsto (fun e => f (α e - e)) l (𝓝 0) := by
  obtain ⟨F, hF⟩ := exists_strongDual_extension_along_injective_cstarHom ι hι f
  have h := tendsto_strongDual_ideal_automorphism_error ι hau F α
  simpa only [← map_sub, hF] using h

end GeneralWeakErrors

section RealWeakConvergence

variable {V κ ι : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {l : Filter ι}

/-- Complex dual convergence implies the real weak convergence needed for
positive real convex combinations. Real functionals are recovered as the
real parts of their genuine complex extensions. -/
theorem tendsto_realWeakSpace_of_complex_dual (u : ι → V)
    (hu : ∀ f : StrongDual ℂ V, Filter.Tendsto (fun i => f (u i)) l (𝓝 0)) :
    Filter.Tendsto (fun i => toWeakSpace ℝ V (u i)) l (𝓝 0) := by
  apply (WeakBilin.tendsto_iff_forall_eval_tendsto
    (B := (topDualPairing ℝ V).flip) (fun x y h => by
      by_contra hne
      obtain ⟨f, hf⟩ := SeparatingDual.exists_separating_of_ne (R := ℝ) hne
      exact hf (DFunLike.congr_fun h f))).mpr
  intro f
  change Filter.Tendsto (fun i => f (u i)) l (𝓝 (f 0))
  rw [map_zero]
  have hre (i : ι) : ((StrongDual.extendRCLike (𝕜 := ℂ) f) (u i)).re = f (u i) :=
    StrongDual.re_extendRCLike_apply (𝕜 := ℂ) f (u i)
  simpa only [Function.comp_def, hre, Complex.zero_re] using
    (Complex.continuous_re.tendsto (0 : ℂ)).comp
      (hu (StrongDual.extendRCLike (𝕜 := ℂ) f))

/-- A finite family of errors whose every complex dual coordinate tends to
zero is weakly null as one real normed product vector. -/
theorem tendsto_realWeakSpace_finitePi_of_complex_dual [Fintype κ]
    (u : ι → κ → V)
    (hu : ∀ k, ∀ f : StrongDual ℂ V,
      Filter.Tendsto (fun i => f (u i k)) l (𝓝 0)) :
    Filter.Tendsto (fun i => toWeakSpace ℝ (κ → V) (u i)) l (𝓝 0) := by
  classical
  apply tendsto_realWeakSpace_of_complex_dual
  intro f
  have hsum : Filter.Tendsto
      (fun i => ∑ k : κ, f (Pi.single k (u i k))) l (𝓝 0) := by
    simpa [ContinuousLinearMap.single] using
      tendsto_finsetSum (Finset.univ : Finset κ) (fun k _ =>
        hu k (f.comp (ContinuousLinearMap.single ℂ (fun _ : κ => V) k)))
  have heq (i : ι) : ∑ k : κ, f (Pi.single k (u i k)) = f (u i) := by
    rw [← map_sum, Finset.univ_sum_single]
  simpa only [heq] using hsum

end RealWeakConvergence

section PositiveConvexification

variable {J V ι : Type*} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {l : Filter ι} [l.NeBot]

/-- Weakly vanishing affine error vectors yield an actual positive
contractive coefficient from the convex hull of any specified good tail.
Finite approximate-unit, commutator, and group-invariance errors can be
combined in the target vector space. -/
theorem exists_positive_contraction_affine_error_lt_of_weak_tendsto
    (u : ι → J) (L : J →ₗ[ℝ] V) (c : V)
    (hweak : Filter.Tendsto (fun i => toWeakSpace ℝ V (L (u i) - c)) l (𝓝 0))
    (s : Set ι) (hs : s ∈ l)
    (hs0 : ∀ i ∈ s, 0 ≤ u i) (hs1 : ∀ i ∈ s, ‖u i‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ e : J, 0 ≤ e ∧ ‖e‖ ≤ 1 ∧ e ∈ convexHull ℝ (u '' s) ∧ ‖L e - c‖ < ε := by
  classical
  obtain ⟨κ, hκ, w, j, hw0, hw1, hj, herr⟩ :=
    exists_finite_convex_combination_norm_lt_of_weak_tendsto
      (fun i => L (u i) - c) hweak s hs ε hε
  let : Fintype κ := hκ
  let e := ∑ i, w i • u (j i)
  have he := positive_contraction_finite_convex_combination w (fun i => u (j i))
    hw0 hw1 (fun i => hs0 _ (hj i)) (fun i => hs1 _ (hj i))
  refine ⟨e, he.1, he.2, ?_, ?_⟩
  · exact mem_convexHull_of_exists_fintype w (fun i => u (j i)) hw0 hw1
      (fun i => ⟨j i, hj i, rfl⟩) rfl
  · have herror : L e - c = ∑ i, w i • (L (u (j i)) - c) := by
      simp only [e, map_sum, map_smul, smul_sub, Finset.sum_sub_distrib,
        ← Finset.sum_smul, hw1, one_smul]
    rwa [← herror] at herr

end PositiveConvexification

section FiniteAmbientSelection

variable {J : Type*} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- An actual ideal approximate unit admits positive contractive convex
selections with simultaneously small finite ambient commutator, arbitrary
ideal-automorphism, and two-sided ideal approximation errors. -/
theorem exists_positive_contraction_finite_ambient_errors_in_convexHull_tail [Nontrivial A]
    (ι : J →⋆ₙₐ[ℂ] A) (hι : Function.Injective ι)
    (hleft : ∀ a : A, ∀ j : J, ∃ k : J, ι k = a * ι j)
    {l : Filter J} (hau : l.IsIncreasingApproximateUnit)
    (sA : Finset A) (sΓ : Finset (J ≃⋆ₐ[ℂ] J)) (sJ : Finset J)
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
  have hweak : Filter.Tendsto
      (fun e => toWeakSpace ℝ (κ → A) (L e - c)) l (𝓝 0) := by
    apply tendsto_realWeakSpace_finitePi_of_complex_dual
    intro k f
    rcases k with a | k
    · simpa [L, maps, c] using tendsto_strongDual_ideal_commutator ι hleft hau f a.1
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
  have hgoodTail : goodTail ∈ l :=
    Filter.inter_mem hs (hau.eventually_nonneg.and hau.eventually_norm)
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

/-- Finite ambient, automorphism, and ideal errors can be made small by an
actual positive contractive coefficient of the ideal. -/
theorem exists_positive_contraction_finite_ambient_errors [Nontrivial A]
    (ι : J →⋆ₙₐ[ℂ] A) (hι : Function.Injective ι)
    (hleft : ∀ a : A, ∀ j : J, ∃ k : J, ι k = a * ι j)
    {l : Filter J} (hau : l.IsIncreasingApproximateUnit)
    (sA : Finset A) (sΓ : Finset (J ≃⋆ₐ[ℂ] J)) (sJ : Finset J)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ e : J, 0 ≤ e ∧ ‖e‖ ≤ 1 ∧ star e = e ∧
      (∀ a ∈ sA, ‖ι e * a - a * ι e‖ < ε) ∧
      (∀ α ∈ sΓ, ‖α e - e‖ < ε) ∧
      (∀ j ∈ sJ, ‖j * e - j‖ < ε ∧ ‖e * j - j‖ < ε) := by
  obtain ⟨e, he0, he1, hestar, _, heA, heΓ, heJ⟩ :=
    exists_positive_contraction_finite_ambient_errors_in_convexHull_tail
      ι hι hleft hau sA sΓ sJ Set.univ Filter.univ_mem ε hε
  exact ⟨e, he0, he1, hestar, heA, heΓ, heJ⟩

end FiniteAmbientSelection

section CountableAmbientSelection

variable {J Γ : Type*} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Ambient commutator errors of contractions extend uniformly from dense
test elements. -/
theorem norm_ambient_commutator_error_le (e a b : A) (he : ‖e‖ ≤ 1) :
    ‖e * a - a * e‖ ≤ 2 * ‖a - b‖ + ‖e * b - b * e‖ := by
  have hl : ‖e * (a - b)‖ ≤ ‖a - b‖ := by
    calc
      ‖e * (a - b)‖ ≤ ‖e‖ * ‖a - b‖ := norm_mul_le _ _
      _ ≤ 1 * ‖a - b‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
      _ = ‖a - b‖ := one_mul _
  have hr : ‖(a - b) * e‖ ≤ ‖a - b‖ := by
    calc
      ‖(a - b) * e‖ ≤ ‖a - b‖ * ‖e‖ := norm_mul_le _ _
      _ ≤ ‖a - b‖ * 1 := mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ = ‖a - b‖ := mul_one _
  calc
    ‖e * a - a * e‖ = ‖(e * (a - b) + (e * b - b * e)) - (a - b) * e‖ := by
      congr 1
      noncomm_ring
    _ ≤ ‖e * (a - b)‖ + ‖e * b - b * e‖ + ‖(a - b) * e‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ 2 * ‖a - b‖ + ‖e * b - b * e‖ := by linarith

omit [PartialOrder A] [StarOrderedRing A] [StarOrderedRing J] in
/-- A finite-selection theorem yields a genuine sequence for all ambient
and ideal elements and every element of a countable group. An additional
exact property, such as evenness, survives the diagonal selection. -/
theorem exists_ambient_quasicentral_sequence_of_finite_selection
    [SeparableSpace A] [SeparableSpace J] [Nonempty Γ] [Countable Γ]
    (ι : J →⋆ₙₐ[ℂ] A) (hι : Function.Injective ι)
    (α : Γ → J ≃⋆ₐ[ℂ] J) (P : J → Prop)
    (hfinite : ∀ (sA : Finset A) (sΓ : Finset Γ) (sJ : Finset J)
      (ε : ℝ), 0 < ε → ∃ e : J, P e ∧ 0 ≤ e ∧ ‖e‖ ≤ 1 ∧ star e = e ∧
        (∀ a ∈ sA, ‖ι e * a - a * ι e‖ < ε) ∧
        (∀ g ∈ sΓ, ‖α g e - e‖ < ε) ∧
        (∀ j ∈ sJ, ‖j * e - j‖ < ε ∧ ‖e * j - j‖ < ε)) :
    ∃ u : ℕ → J, (∀ n, P (u n)) ∧ (∀ n, 0 ≤ u n) ∧
      (∀ n, ‖u n‖ ≤ 1) ∧ (∀ n, star (u n) = u n) ∧
      (∀ j : J, Filter.Tendsto (fun n => j * u n) Filter.atTop (𝓝 j)) ∧
      (∀ j : J, Filter.Tendsto (fun n => u n * j) Filter.atTop (𝓝 j)) ∧
      (∀ a : A, Filter.Tendsto (fun n => ι (u n) * a - a * ι (u n))
        Filter.atTop (𝓝 0)) ∧
      (∀ g : Γ, Filter.Tendsto (fun n => α g (u n) - u n) Filter.atTop (𝓝 0)) := by
  classical
  let dA := denseSeq A
  let dJ := denseSeq J
  have hdA : DenseRange dA := denseRange_denseSeq A
  have hdJ : DenseRange dJ := denseRange_denseSeq J
  obtain ⟨γ, hγ⟩ := exists_surjective_nat Γ
  have hchoice : ∀ n : ℕ, ∃ e : J, P e ∧ 0 ≤ e ∧ ‖e‖ ≤ 1 ∧ star e = e ∧
      (∀ k ≤ n, ‖ι e * dA k - dA k * ι e‖ < 1 / ((n : ℝ) + 1)) ∧
      (∀ k ≤ n, ‖α (γ k) e - e‖ < 1 / ((n : ℝ) + 1)) ∧
      (∀ k ≤ n, ‖dJ k * e - dJ k‖ < 1 / ((n : ℝ) + 1) ∧
        ‖e * dJ k - dJ k‖ < 1 / ((n : ℝ) + 1)) := by
    intro n
    obtain ⟨e, heP, he0, he1, hestar, heA, heΓ, heJ⟩ := hfinite
      ((Finset.range (n + 1)).image dA) ((Finset.range (n + 1)).image γ)
      ((Finset.range (n + 1)).image dJ) (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨e, heP, he0, he1, hestar,
      fun k hk => heA _ (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩),
      fun k hk => heΓ _ (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩),
      fun k hk => heJ _ (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩)⟩
  choose u huP hu0 hu1 hustar huA huΓ huJ using hchoice
  refine ⟨u, huP, hu0, hu1, hustar, ?_, ?_, ?_, ?_⟩
  · intro j
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp hdJ j (ε / 4) (by positivity)
    have hsmall : ∀ᶠ n : ℕ in Filter.atTop, 1 / ((n : ℝ) + 1) < ε / 2 :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
        (gt_mem_nhds (by positivity : 0 < ε / 2))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hsmall
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
    have hsmall : ∀ᶠ n : ℕ in Filter.atTop, 1 / ((n : ℝ) + 1) < ε / 2 :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
        (gt_mem_nhds (by positivity : 0 < ε / 2))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hsmall
    refine ⟨max k N, fun n hn => ?_⟩
    have hkn : k ≤ n := (le_max_left k N).trans hn
    have hNn : N ≤ n := (le_max_right k N).trans hn
    have hsample := (huJ n k hkn).2
    have herror := norm_left_unit_error_le (u n) j (dJ k) (hu1 n)
    rw [dist_eq_norm] at hk ⊢
    have htail := hN n hNn
    linarith
  · intro a
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp hdA a (ε / 4) (by positivity)
    have hsmall : ∀ᶠ n : ℕ in Filter.atTop, 1 / ((n : ℝ) + 1) < ε / 2 :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
        (gt_mem_nhds (by positivity : 0 < ε / 2))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hsmall
    refine ⟨max k N, fun n hn => ?_⟩
    have hkn : k ≤ n := (le_max_left k N).trans hn
    have hNn : N ≤ n := (le_max_right k N).trans hn
    have hsample := huA n k hkn
    have hnorm : ‖ι (u n)‖ ≤ 1 := by rw [NonUnitalStarAlgHom.norm_map ι hι]; exact hu1 n
    have herror := norm_ambient_commutator_error_le (ι (u n)) a (dA k) hnorm
    rw [dist_eq_norm] at hk
    rw [dist_zero_right]
    have htail := hN n hNn
    linarith
  · intro g
    obtain ⟨k, rfl⟩ := hγ g
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hsmall : ∀ᶠ n : ℕ in Filter.atTop, 1 / ((n : ℝ) + 1) < ε :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hε)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hsmall
    refine ⟨max k N, fun n hn => ?_⟩
    have hkn : k ≤ n := (le_max_left k N).trans hn
    have hNn : N ≤ n := (le_max_right k N).trans hn
    rw [dist_zero_right]
    exact (huΓ n k hkn).trans (hN n hNn)

/-- Every ideal in a separable unital ambient C⋆-algebra has an actual
positive contractive sequential approximate unit quasicentral in the
ambient algebra and asymptotically invariant under any countable family
of ideal automorphisms. -/
theorem exists_positive_contractive_ambient_quasicentral_sequence
    [Nontrivial A] [SeparableSpace A] [SeparableSpace J] [Nonempty Γ] [Countable Γ]
    (ι : J →⋆ₙₐ[ℂ] A) (hι : Function.Injective ι)
    (hleft : ∀ a : A, ∀ j : J, ∃ k : J, ι k = a * ι j)
    (α : Γ → J ≃⋆ₐ[ℂ] J) :
    ∃ u : ℕ → J, (∀ n, 0 ≤ u n) ∧ (∀ n, ‖u n‖ ≤ 1) ∧
      (∀ n, star (u n) = u n) ∧
      (∀ j : J, Filter.Tendsto (fun n => j * u n) Filter.atTop (𝓝 j)) ∧
      (∀ j : J, Filter.Tendsto (fun n => u n * j) Filter.atTop (𝓝 j)) ∧
      (∀ a : A, Filter.Tendsto (fun n => ι (u n) * a - a * ι (u n))
        Filter.atTop (𝓝 0)) ∧
      (∀ g : Γ, Filter.Tendsto (fun n => α g (u n) - u n) Filter.atTop (𝓝 0)) := by
  classical
  have hfinite : ∀ (sA : Finset A) (sΓ : Finset Γ) (sJ : Finset J)
      (ε : ℝ), 0 < ε → ∃ e : J, True ∧ 0 ≤ e ∧ ‖e‖ ≤ 1 ∧ star e = e ∧
        (∀ a ∈ sA, ‖ι e * a - a * ι e‖ < ε) ∧
        (∀ g ∈ sΓ, ‖α g e - e‖ < ε) ∧
        (∀ j ∈ sJ, ‖j * e - j‖ < ε ∧ ‖e * j - j‖ < ε) := by
    intro sA sΓ sJ ε hε
    obtain ⟨e, he0, he1, hestar, heA, heΓ, heJ⟩ :=
      exists_positive_contraction_finite_ambient_errors ι hι hleft
        (CStarAlgebra.increasingApproximateUnit J) sA (sΓ.image α) sJ ε hε
    refine ⟨e, trivial, he0, he1, hestar, heA, ?_, heJ⟩
    intro g hg
    exact heΓ _ (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
  obtain ⟨u, _, hu0, hu1, hustar, hleft, hright, hcomm, hΓ⟩ :=
    exists_ambient_quasicentral_sequence_of_finite_selection ι hι α (fun _ => True) hfinite
  exact ⟨u, hu0, hu1, hustar, hleft, hright, hcomm, hΓ⟩

end CountableAmbientSelection

section NonunitalAmbientSelection

variable {D J Γ : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

omit [PartialOrder D] [StarOrderedRing D] [PartialOrder J] [StarOrderedRing J] in
/-- Unitization preserves the actual left-ideal range property of a complex
C⋆-homomorphism. Scalar terms are absorbed by its complex linearity. -/
theorem unitized_inclusion_has_leftIdeal_range
    (ι : J →⋆ₙₐ[ℂ] D)
    (hleft : ∀ a : D, ∀ j : J, ∃ k : J, ι k = a * ι j) :
    ∀ a : Unitization ℂ D, ∀ j : J, ∃ k : J,
      ((Unitization.inrNonUnitalStarAlgHom ℂ D).comp ι) k =
        a * ((Unitization.inrNonUnitalStarAlgHom ℂ D).comp ι) j := by
  intro a j
  obtain ⟨k, hk⟩ := hleft a.snd j
  refine ⟨a.fst • j + k, ?_⟩
  ext <;> simp [hk]

omit [PartialOrder D] [StarOrderedRing D] in
/-- The genuine ambient quasicentral, asymptotically invariant sequence
exists in a possibly nonunital separable ambient C⋆-algebra. Unitization
supplies a nontrivial unital algebra even when the original algebra is zero. -/
theorem exists_positive_contractive_nonunital_ambient_quasicentral_sequence
    [SeparableSpace D] [SeparableSpace J] [Nonempty Γ] [Countable Γ]
    (ι : J →⋆ₙₐ[ℂ] D) (hι : Function.Injective ι)
    (hleft : ∀ a : D, ∀ j : J, ∃ k : J, ι k = a * ι j)
    (α : Γ → J ≃⋆ₐ[ℂ] J) :
    ∃ u : ℕ → J, (∀ n, 0 ≤ u n) ∧ (∀ n, ‖u n‖ ≤ 1) ∧
      (∀ n, star (u n) = u n) ∧
      (∀ j : J, Filter.Tendsto (fun n => j * u n) Filter.atTop (𝓝 j)) ∧
      (∀ j : J, Filter.Tendsto (fun n => u n * j) Filter.atTop (𝓝 j)) ∧
      (∀ a : D, Filter.Tendsto (fun n => ι (u n) * a - a * ι (u n))
        Filter.atTop (𝓝 0)) ∧
      (∀ g : Γ, Filter.Tendsto (fun n => α g (u n) - u n) Filter.atTop (𝓝 0)) := by
  let η := (Unitization.inrNonUnitalStarAlgHom ℂ D).comp ι
  have hη : Function.Injective η := Unitization.inr_injective.comp hι
  have hηleft := unitized_inclusion_has_leftIdeal_range ι hleft
  let : SeparableSpace (Unitization ℂ D) :=
    (Unitization.uniformEquivProd (𝕜 := ℂ) (A := D)).symm.surjective.denseRange.separableSpace
      (Unitization.uniformEquivProd (𝕜 := ℂ) (A := D)).symm.toHomeomorph.continuous
  obtain ⟨u, hu0, hu1, hustar, hleft, hright, hcomm, hΓ⟩ :=
    exists_positive_contractive_ambient_quasicentral_sequence η hη hηleft α
  refine ⟨u, hu0, hu1, hustar, hleft, hright, ?_, hΓ⟩
  intro a
  apply (Unitization.isometry_inr (𝕜 := ℂ) (A := D)).tendsto_nhds_iff.mpr
  simpa [η, Function.comp_def, ← Unitization.inr_mul, ← Unitization.inr_sub] using
    hcomm (Unitization.inr a)

end NonunitalAmbientSelection

section ExactEvenFiniteSelection

variable {J : Type*} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

private theorem norm_half_add_lt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x y : V) {ε : ℝ} (hx : ‖x‖ < ε) (hy : ‖y‖ < ε) :
    ‖(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y‖ < ε := by
  calc
    ‖(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y‖ ≤
        (1 / 2 : ℝ) * ‖x‖ + (1 / 2 : ℝ) * ‖y‖ := by
      simpa [norm_smul] using norm_add_le ((1 / 2 : ℝ) • x) ((1 / 2 : ℝ) • y)
    _ < ε := by linarith

/-- Averaging an actual finite-error selection with a compatible grading
involution gives exact evenness while preserving finite quasicentral,
automorphism, and approximate-unit control. -/
theorem exists_even_positive_contraction_finite_ambient_errors [Nontrivial A]
    (ι : J →⋆ₙₐ[ℂ] A) (hι : Function.Injective ι)
    (hleft : ∀ a : A, ∀ j : J, ∃ k : J, ι k = a * ι j)
    (δ : J ≃⋆ₐ[ℂ] J) (hδ : ∀ j, δ (δ j) = j)
    (Δ : A ≃⋆ₐ[ℂ] A) (hgrade : ∀ j, ι (δ j) = Δ (ι j))
    (sA : Finset A) (sΓ : Finset (J ≃⋆ₐ[ℂ] J)) (sJ : Finset J)
    (hcomm : ∀ α ∈ sΓ, ∀ j, δ (α j) = α (δ j))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ e : J, δ e = e ∧ 0 ≤ e ∧ ‖e‖ ≤ 1 ∧ star e = e ∧
      (∀ a ∈ sA, ‖ι e * a - a * ι e‖ < ε) ∧
      (∀ α ∈ sΓ, ‖α e - e‖ < ε) ∧
      (∀ j ∈ sJ, ‖j * e - j‖ < ε ∧ ‖e * j - j‖ < ε) := by
  classical
  obtain ⟨e, he0, he1, _, heA, heΓ, heJ⟩ :=
    exists_positive_contraction_finite_ambient_errors ι hι hleft
      (CStarAlgebra.increasingApproximateUnit J)
      (sA ∪ sA.image Δ.symm) sΓ (sJ ∪ sJ.image δ) ε hε
  let v : J := (1 / 2 : ℝ) • e + (1 / 2 : ℝ) • δ e
  have hδe0 : 0 ≤ δ e := by
    obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp he0
    simpa only [map_mul, map_star] using star_mul_self_nonneg (δ b)
  have hv0 : 0 ≤ v := add_nonneg
    (smul_nonneg (by norm_num) he0) (smul_nonneg (by norm_num) hδe0)
  have hv1 : ‖v‖ ≤ 1 := by
    calc
      ‖v‖ ≤ ‖(1 / 2 : ℝ) • e‖ + ‖(1 / 2 : ℝ) • δ e‖ := norm_add_le _ _
      _ = ‖e‖ := by simp [norm_smul, StarAlgEquiv.norm_map]; ring
      _ ≤ 1 := he1
  have hvδ : δ v = v := by
    simp only [v, map_add, LinearMapClass.map_smul_of_tower (S := ℂ), hδ]
    exact add_comm _ _
  refine ⟨v, hvδ, hv0, hv1, (IsSelfAdjoint.of_nonneg hv0).star_eq, ?_, ?_, ?_⟩
  · intro a ha
    have hfirst := heA a (Finset.mem_union_left _ ha)
    have hsecond0 := heA (Δ.symm a) (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨a, ha, rfl⟩))
    have hsecond : ‖ι (δ e) * a - a * ι (δ e)‖ < ε := by
      have heq : ι (δ e) * a - a * ι (δ e) =
          Δ (ι e * Δ.symm a - Δ.symm a * ι e) := by
        rw [map_sub, map_mul, map_mul, Δ.apply_symm_apply, ← hgrade]
      rwa [heq, StarAlgEquiv.norm_map]
    have heq : ι v * a - a * ι v =
        (1 / 2 : ℝ) • (ι e * a - a * ι e) +
          (1 / 2 : ℝ) • (ι (δ e) * a - a * ι (δ e)) := by
      simp only [v, map_add, LinearMapClass.map_smul_of_tower (S := ℂ),
        add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
      module
    rw [heq]
    exact norm_half_add_lt _ _ hfirst hsecond
  · intro α hα
    have hfirst := heΓ α hα
    have hsecond : ‖α (δ e) - δ e‖ < ε := by
      have heq : α (δ e) - δ e = δ (α e - e) := by
        rw [map_sub, hcomm α hα]
      rwa [heq, StarAlgEquiv.norm_map]
    have heq : α v - v = (1 / 2 : ℝ) • (α e - e) +
        (1 / 2 : ℝ) • (α (δ e) - δ e) := by
      simp only [v, map_add, LinearMapClass.map_smul_of_tower (S := ℂ)]
      module
    rw [heq]
    exact norm_half_add_lt _ _ hfirst hsecond
  · intro j hj
    have hfirst := heJ j (Finset.mem_union_left _ hj)
    have hsecond0 := heJ (δ j) (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨j, hj, rfl⟩))
    have hsecondL : ‖j * δ e - j‖ < ε := by
      have heq : j * δ e - j = δ (δ j * e - δ j) := by rw [map_sub, map_mul, hδ]
      rw [heq, StarAlgEquiv.norm_map]
      exact hsecond0.1
    have hsecondR : ‖δ e * j - j‖ < ε := by
      have heq : δ e * j - j = δ (e * δ j - δ j) := by rw [map_sub, map_mul, hδ]
      rw [heq, StarAlgEquiv.norm_map]
      exact hsecond0.2
    constructor
    · have heq : j * v - j = (1 / 2 : ℝ) • (j * e - j) +
          (1 / 2 : ℝ) • (j * δ e - j) := by
        simp only [v, mul_add, mul_smul_comm]
        module
      rw [heq]
      exact norm_half_add_lt _ _ hfirst.1 hsecondL
    · have heq : v * j - j = (1 / 2 : ℝ) • (e * j - j) +
          (1 / 2 : ℝ) • (δ e * j - j) := by
        simp only [v, add_mul, smul_mul_assoc]
        module
      rw [heq]
      exact norm_half_add_lt _ _ hfirst.2 hsecondR

/-- A compatible grading and any countable family of commuting ideal
automorphisms allow one actual even positive contractive ambient
quasicentral approximate-unit sequence. -/
theorem exists_even_positive_contractive_ambient_quasicentral_sequence
    {Γ : Type*} [Nontrivial A] [SeparableSpace A] [SeparableSpace J]
    [Nonempty Γ] [Countable Γ]
    (ι : J →⋆ₙₐ[ℂ] A) (hι : Function.Injective ι)
    (hleft : ∀ a : A, ∀ j : J, ∃ k : J, ι k = a * ι j)
    (δ : J ≃⋆ₐ[ℂ] J) (hδ : ∀ j, δ (δ j) = j)
    (Δ : A ≃⋆ₐ[ℂ] A) (hgrade : ∀ j, ι (δ j) = Δ (ι j))
    (α : Γ → J ≃⋆ₐ[ℂ] J) (hcomm : ∀ g j, δ (α g j) = α g (δ j)) :
    ∃ u : ℕ → J, (∀ n, δ (u n) = u n) ∧ (∀ n, 0 ≤ u n) ∧
      (∀ n, ‖u n‖ ≤ 1) ∧ (∀ n, star (u n) = u n) ∧
      (∀ j : J, Filter.Tendsto (fun n => j * u n) Filter.atTop (𝓝 j)) ∧
      (∀ j : J, Filter.Tendsto (fun n => u n * j) Filter.atTop (𝓝 j)) ∧
      (∀ a : A, Filter.Tendsto (fun n => ι (u n) * a - a * ι (u n))
        Filter.atTop (𝓝 0)) ∧
      (∀ g : Γ, Filter.Tendsto (fun n => α g (u n) - u n) Filter.atTop (𝓝 0)) := by
  classical
  apply exists_ambient_quasicentral_sequence_of_finite_selection ι hι α (fun e => δ e = e)
  intro sA sΓ sJ ε hε
  obtain ⟨e, heδ, he0, he1, hestar, heA, heΓ, heJ⟩ :=
    exists_even_positive_contraction_finite_ambient_errors ι hι hleft δ hδ Δ hgrade
      sA (sΓ.image α) sJ (fun β hβ j => by
        obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hβ
        exact hcomm g j) ε hε
  refine ⟨e, heδ, he0, he1, hestar, heA, ?_, heJ⟩
  intro g hg
  exact heΓ _ (Finset.mem_image.mpr ⟨g, hg, rfl⟩)

end ExactEvenFiniteSelection

section NonunitalEvenAmbientSelection

variable {D J Γ : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- The unitized star map of an actual star algebra equivalence is again an
actual equivalence. -/
def unitizedStarAlgEquiv (Δ : D ≃⋆ₐ[ℂ] D) : Unitization ℂ D ≃⋆ₐ[ℂ] Unitization ℂ D :=
  StarAlgEquiv.ofBijective (Unitization.starMap Δ.toNonUnitalStarAlgHom)
    ⟨Unitization.starMap_injective Δ.injective, Unitization.starMap_surjective Δ.surjective⟩

omit [PartialOrder D] [StarOrderedRing D] in
@[simp] theorem unitizedStarAlgEquiv_inr (Δ : D ≃⋆ₐ[ℂ] D) (a : D) :
    unitizedStarAlgEquiv Δ (Unitization.inr a) = Unitization.inr (Δ a) := by
  change (Unitization.starMap Δ.toNonUnitalStarAlgHom) (Unitization.inr a) = _
  exact Unitization.starMap_inr _ a

omit [PartialOrder D] [StarOrderedRing D] in
/-- Exact evenness, ambient quasicentrality, and countable asymptotic group
invariance hold simultaneously in a possibly nonunital separable ambient
C⋆-algebra. -/
theorem exists_even_positive_contractive_nonunital_ambient_quasicentral_sequence
    [SeparableSpace D] [SeparableSpace J] [Nonempty Γ] [Countable Γ]
    (ι : J →⋆ₙₐ[ℂ] D) (hι : Function.Injective ι)
    (hleft : ∀ a : D, ∀ j : J, ∃ k : J, ι k = a * ι j)
    (δ : J ≃⋆ₐ[ℂ] J) (hδ : ∀ j, δ (δ j) = j)
    (Δ : D ≃⋆ₐ[ℂ] D) (hgrade : ∀ j, ι (δ j) = Δ (ι j))
    (α : Γ → J ≃⋆ₐ[ℂ] J) (hcomm : ∀ g j, δ (α g j) = α g (δ j)) :
    ∃ u : ℕ → J, (∀ n, δ (u n) = u n) ∧ (∀ n, 0 ≤ u n) ∧
      (∀ n, ‖u n‖ ≤ 1) ∧ (∀ n, star (u n) = u n) ∧
      (∀ j : J, Filter.Tendsto (fun n => j * u n) Filter.atTop (𝓝 j)) ∧
      (∀ j : J, Filter.Tendsto (fun n => u n * j) Filter.atTop (𝓝 j)) ∧
      (∀ a : D, Filter.Tendsto (fun n => ι (u n) * a - a * ι (u n))
        Filter.atTop (𝓝 0)) ∧
      (∀ g : Γ, Filter.Tendsto (fun n => α g (u n) - u n) Filter.atTop (𝓝 0)) := by
  let η := (Unitization.inrNonUnitalStarAlgHom ℂ D).comp ι
  have hη : Function.Injective η := Unitization.inr_injective.comp hι
  have hηleft := unitized_inclusion_has_leftIdeal_range ι hleft
  let : SeparableSpace (Unitization ℂ D) :=
    (Unitization.uniformEquivProd (𝕜 := ℂ) (A := D)).symm.surjective.denseRange.separableSpace
      (Unitization.uniformEquivProd (𝕜 := ℂ) (A := D)).symm.toHomeomorph.continuous
  have hηgrade (j : J) : η (δ j) = unitizedStarAlgEquiv Δ (η j) := by
    simp [η, hgrade]
  obtain ⟨u, hueven, hu0, hu1, hustar, hleft, hright, hcomm, hΓ⟩ :=
    exists_even_positive_contractive_ambient_quasicentral_sequence η hη hηleft
      δ hδ (unitizedStarAlgEquiv Δ) hηgrade α hcomm
  refine ⟨u, hueven, hu0, hu1, hustar, hleft, hright, ?_, hΓ⟩
  intro a
  apply (Unitization.isometry_inr (𝕜 := ℂ) (A := D)).tendsto_nhds_iff.mpr
  simpa [η, Function.comp_def, ← Unitization.inr_mul, ← Unitization.inr_sub] using
    hcomm (Unitization.inr a)

end NonunitalEvenAmbientSelection

section CanonicalOrderTailSelection

variable {J : Type*} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- Every positive strict contraction is an eventual lower bound of the
actual canonical approximate-unit filter. -/
theorem eventually_le_coefficient_approximateUnit (p : J) (hp0 : 0 ≤ p) (hp1 : ‖p‖ < 1) :
    ∀ᶠ e : J in CStarAlgebra.approximateUnit J, p ≤ e := by
  apply (CStarAlgebra.hasBasis_approximateUnit J).eventually_iff.mpr
  exact ⟨p, ⟨hp0, hp1⟩, fun _ h => h.1⟩

/-- Finite ambient, automorphism, and ideal error selection can dominate
any specified positive strict contraction. This uses actual canonical
order tails and their real convexity. -/
theorem exists_positive_contraction_finite_ambient_errors_above [Nontrivial A]
    (ι : J →⋆ₙₐ[ℂ] A) (hι : Function.Injective ι)
    (hleft : ∀ a : A, ∀ j : J, ∃ k : J, ι k = a * ι j)
    (p : J) (hp0 : 0 ≤ p) (hp1 : ‖p‖ < 1)
    (sA : Finset A) (sΓ : Finset (J ≃⋆ₐ[ℂ] J)) (sJ : Finset J)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ e : J, p ≤ e ∧ 0 ≤ e ∧ ‖e‖ ≤ 1 ∧ star e = e ∧
      (∀ a ∈ sA, ‖ι e * a - a * ι e‖ < ε) ∧
      (∀ α ∈ sΓ, ‖α e - e‖ < ε) ∧
      (∀ j ∈ sJ, ‖j * e - j‖ < ε ∧ ‖e * j - j‖ < ε) := by
  obtain ⟨e, he0, he1, hestar, heHull, heA, heΓ, heJ⟩ :=
    exists_positive_contraction_finite_ambient_errors_in_convexHull_tail ι hι hleft
      (CStarAlgebra.increasingApproximateUnit J) sA sΓ sJ (Set.Ici p)
      (eventually_le_coefficient_approximateUnit p hp0 hp1) ε hε
  have heabove : p ≤ e := by
    change e ∈ Set.Ici p
    rwa [(convex_Ici (𝕜 := ℝ) p).convexHull_eq] at heHull
  exact ⟨e, heabove, he0, he1, hestar, heA, heΓ, heJ⟩

end CanonicalOrderTailSelection

section StrictCanonicalOrderSelection

variable {J : Type*} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- A finite quasicentral approximate-unit selection can both dominate a
previous positive strict contraction and remain a strict contraction. The
small scalar perturbation controls the only nonhomogeneous errors, the
two-sided approximate-unit errors on the finite ideal tests. -/
theorem exists_positive_strict_contraction_finite_ambient_errors_above [Nontrivial A]
    (ι : J →⋆ₙₐ[ℂ] A) (hι : Function.Injective ι)
    (hleft : ∀ a : A, ∀ j : J, ∃ k : J, ι k = a * ι j)
    (p : J) (hp0 : 0 ≤ p) (hp1 : ‖p‖ < 1)
    (sA : Finset A) (sΓ : Finset (J ≃⋆ₐ[ℂ] J)) (sJ : Finset J)
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
    exists_positive_contraction_finite_ambient_errors_above ι hι hleft q hq0 hq1
      sA sΓ sJ (ε / 2) (by positivity)
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

end StrictCanonicalOrderSelection

end BC4lean.KKTheory
