import BC4lean.LocalizedModuleFunctionalCalculus
import BC4lean.OddFredholmPolarCompact

/-! # Exact functional calculus and polar preservation of an identity tail

A genuine scalar eigenspace is preserved by continuous functional calculus,
proved by continuous-function induction on the actual spectrum with that
scalar added. This gives exact identity-tail preservation by square roots,
ring inverse, and the actual polar correction. No tail compactness is used.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped Ring CStarAlgebra

variable {A : Type*} [CStarAlgebra A]

theorem oddFredholm_cfc_sub_value_mul_eq_zero
    (Q R : A) (hQ : IsSelfAdjoint Q) (r : ℝ)
    (hQR : (Q - algebraMap ℝ A r) * R = 0)
    (f : ℝ → ℝ) (hf : Continuous f) :
    (cfc f Q - algebraMap ℝ A (f r)) * R = 0 := by
  let K : Set ℝ := spectrum ℝ Q ∪ {r}
  have hK : IsCompact K := (spectrum.isCompact Q).union (isCompact_singleton (x := r))
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hσ : spectrum ℝ Q ⊆ K := Set.subset_union_left
  let Φ : C(K, ℝ) →⋆ₐ[ℝ] A := cfcHomSuperset hQ hσ
  let z : K := ⟨r, Set.mem_union_right _ (Set.mem_singleton r)⟩
  have hΦ : Continuous Φ := cfcHomSuperset_continuous hQ hσ
  have hΦid : Φ (ContinuousMap.restrict K (ContinuousMap.id ℝ)) = Q := cfcHomSuperset_id hQ hσ
  have hgen : (Φ (ContinuousMap.restrict K (ContinuousMap.id ℝ)) -
      algebraMap ℝ A ((ContinuousMap.restrict K (ContinuousMap.id ℝ)) z)) * R = 0 := by
    simpa only [hΦid, ContinuousMap.restrict_apply, ContinuousMap.id_apply] using hQR
  have hall : ∀ g : C(K, ℝ), (Φ g - algebraMap ℝ A (g z)) * R = 0 := by
    intro g
    induction g using ContinuousMap.induction_on_of_compact with
    | const c =>
      have hconst : Φ (ContinuousMap.const K c) = algebraMap ℝ A c := Φ.commutes c
      simp only [hconst, ContinuousMap.const_apply, sub_self, zero_mul]
    | id => exact hgen
    | star_id =>
      have heq : star (ContinuousMap.restrict K (ContinuousMap.id ℝ)) =
          ContinuousMap.restrict K (ContinuousMap.id ℝ) := by ext x; simp
      rw [heq]
      exact hgen
    | add g h hg hh =>
      have heq : (Φ (g + h) - algebraMap ℝ A ((g + h) z)) * R =
          (Φ g - algebraMap ℝ A (g z)) * R +
            (Φ h - algebraMap ℝ A (h z)) * R := by
        rw [map_add, ContinuousMap.add_apply, map_add]
        noncomm_ring
      rw [heq, hg, hh, zero_add]
    | mul g h hg hh =>
      have heq : (Φ (g * h) - algebraMap ℝ A ((g * h) z)) * R =
          Φ g * ((Φ h - algebraMap ℝ A (h z)) * R) +
            algebraMap ℝ A (h z) * ((Φ g - algebraMap ℝ A (g z)) * R) := by
        rw [map_mul, ContinuousMap.mul_apply]
        simp only [Algebra.algebraMap_eq_smul_one, sub_mul, mul_sub,
          smul_mul_assoc, mul_smul_comm, one_mul, mul_assoc, smul_smul]
        module
      rw [heq, hg, hh, mul_zero, mul_zero, zero_add]
    | frequently g hg =>
      have hcont : Continuous (fun h : C(K, ℝ) =>
          (Φ h - algebraMap ℝ A (h z)) * R) :=
        (hΦ.sub ((continuous_algebraMap ℝ A).comp (continuous_eval_const z))).mul continuous_const
      exact (isClosed_eq hcont continuous_const).mem_of_frequently_of_tendsto hg
        Filter.tendsto_id
  let F : C(K, ℝ) := ⟨fun x => f x, hf.comp continuous_subtype_val⟩
  have hF : Φ F = cfc f Q := by
    change cfcHom hQ _ = cfc f Q
    rw [cfc_apply f Q hQ hf.continuousOn]
    congr 1
  have h := hall F
  rw [hF] at h
  exact h

theorem oddFredholmRingInverse_mul_eq_self (a q : A) (ha : IsUnit a)
    (hq : a * q = q) : a⁻¹ʳ * q = q := by
  calc
    _ = a⁻¹ʳ * (a * q) := by rw [hq]
    _ = q := by rw [← mul_assoc, Ring.inverse_mul_cancel a ha, one_mul]

variable [PartialOrder A] [StarOrderedRing A]

/-- The actual polar correction retains an exact identity tail. -/
theorem oddFredholmPolarElement_right_tail (a q : A) (ha : IsUnit a)
    (hq : star q = q) (hRight : a * q = q) (hLeft : q * a = q) :
    oddFredholmPolarElement a * q = q := by
  have hStar : star a * q = q := by
    simpa only [star_mul, hq] using congrArg star hLeft
  have hGram : (star a * a - 1) * q = 0 := by
    rw [sub_mul, mul_assoc, hRight, hStar, one_mul, sub_self]
  have hSqrt := oddFredholm_cfc_sub_value_mul_eq_zero (star a * a) q
    (IsSelfAdjoint.star_mul_self a) 1 (by simpa only [map_one] using hGram)
      Real.sqrt Real.continuous_sqrt
  have hs : CFC.sqrt (star a * a) * q = q := by
    rw [CFC.sqrt_eq_real_sqrt _ (star_mul_self_nonneg a), cfcₙ_eq_cfc]
    simpa only [Real.sqrt_one, map_one, sub_mul, one_mul, sub_eq_zero] using hSqrt
  rw [oddFredholmPolarElement, mul_assoc,
    oddFredholmRingInverse_mul_eq_self _ q (oddFredholmGramSqrt_isUnit a ha) hs, hRight]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Genuine unitarity turns an exact right identity tail into the matching
left identity tail. -/
theorem oddFredholmUnitary_left_tail (u : unitary A) (q : A) (hq : star q = q)
    (hRight : (u : A) * q = q) : q * (u : A) = q := by
  have hstar : star (u : A) * q = q := by
    calc
      _ = star (u : A) * ((u : A) * q) := by rw [hRight]
      _ = q := by rw [← mul_assoc, Unitary.coe_star_mul_self, one_mul]
  simpa only [star_mul, star_star, hq] using congrArg star hstar

end BC4lean.KKTheory

