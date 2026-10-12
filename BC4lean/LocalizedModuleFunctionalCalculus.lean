import BC4lean.CompactModuleOperator
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module

/-! # Localized continuous functional calculus for module operators

A scalar defect compact after multiplication by one actual adjointable map
remains compact after real continuous functional calculus. The proof uses
continuous-function induction on the compact spectrum with the scalar added,
and the closed actual Hilbert-module compact ideal. It assumes neither
commutation with the localizing map nor a globally compact scalar defect.
No nontriviality of the operator algebra or underlying module is required.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- A localized defect at a scalar remains localized under real continuous
functional calculus. The proof only uses the closed actual compact ideal;
it does not require the defect to be globally compact or R to commute with Q. -/
theorem cfc_sub_value_mul_isModuleCompact
    (Q R : AdjointableMap B E E) (hQ : IsSelfAdjoint Q) (r : ℝ)
    (hQR : IsModuleCompact ((Q - algebraMap ℝ (AdjointableMap B E E) r) * R))
    (f : ℝ → ℝ) (hf : Continuous f) :
    IsModuleCompact ((cfc f Q - algebraMap ℝ (AdjointableMap B E E) (f r)) * R) := by
  let K : Set ℝ := spectrum ℝ Q ∪ {r}
  have hK : IsCompact K := (spectrum.isCompact Q).union (isCompact_singleton (x := r))
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hσ : spectrum ℝ Q ⊆ K := Set.subset_union_left
  let Φ : C(K, ℝ) →⋆ₐ[ℝ] AdjointableMap B E E := cfcHomSuperset hQ hσ
  let z : K := ⟨r, Set.mem_union_right _ (Set.mem_singleton r)⟩
  have hΦ : Continuous Φ := cfcHomSuperset_continuous hQ hσ
  have hΦid : Φ (ContinuousMap.restrict K (ContinuousMap.id ℝ)) = Q := cfcHomSuperset_id hQ hσ
  have hgen : IsModuleCompact ((Φ (ContinuousMap.restrict K (ContinuousMap.id ℝ)) -
      algebraMap ℝ (AdjointableMap B E E) ((ContinuousMap.restrict K (ContinuousMap.id ℝ)) z)) * R) := by
    simpa only [hΦid, ContinuousMap.restrict_apply, ContinuousMap.id_apply] using hQR
  have hall : ∀ g : C(K, ℝ), IsModuleCompact
      ((Φ g - algebraMap ℝ (AdjointableMap B E E) (g z)) * R) := by
    intro g
    induction g using ContinuousMap.induction_on_of_compact with
    | const c =>
      have hconst : Φ (ContinuousMap.const K c) =
          algebraMap ℝ (AdjointableMap B E E) c := Φ.commutes c
      simp only [hconst, ContinuousMap.const_apply, sub_self, zero_mul]
      exact (moduleCompact B E E).zero_mem
    | id => exact hgen
    | star_id =>
      have heq : star (ContinuousMap.restrict K (ContinuousMap.id ℝ)) =
          ContinuousMap.restrict K (ContinuousMap.id ℝ) := by
        ext x
        simp
      rw [heq]
      exact hgen
    | add g h hg hh =>
      have heq : (Φ (g + h) - algebraMap ℝ (AdjointableMap B E E) ((g + h) z)) * R =
          (Φ g - algebraMap ℝ (AdjointableMap B E E) (g z)) * R +
          (Φ h - algebraMap ℝ (AdjointableMap B E E) (h z)) * R := by
        rw [map_add, ContinuousMap.add_apply, map_add]
        noncomm_ring
      rw [heq]
      exact hg.add hh
    | mul g h hg hh =>
      have heq : (Φ (g * h) - algebraMap ℝ (AdjointableMap B E E) ((g * h) z)) * R =
          Φ g * ((Φ h - algebraMap ℝ (AdjointableMap B E E) (h z)) * R) +
          algebraMap ℝ (AdjointableMap B E E) (h z) *
            ((Φ g - algebraMap ℝ (AdjointableMap B E E) (g z)) * R) := by
        rw [map_mul, ContinuousMap.mul_apply]
        simp only [Algebra.algebraMap_eq_smul_one, sub_mul, mul_sub,
          smul_mul_assoc, mul_smul_comm, one_mul, mul_assoc, smul_smul]
        module
      rw [heq]
      exact IsModuleCompact.add (mul_mem_moduleCompact_left (Φ g) hh)
        (mul_mem_moduleCompact_left (algebraMap ℝ (AdjointableMap B E E) (h z)) hg)
    | frequently g hg =>
      have hcont : Continuous (fun h : C(K, ℝ) =>
          (Φ h - algebraMap ℝ (AdjointableMap B E E) (h z)) * R) :=
        (hΦ.sub ((continuous_algebraMap ℝ (AdjointableMap B E E)).comp
          (continuous_eval_const z))).mul continuous_const
      exact moduleCompact_isClosed.mem_of_frequently_of_tendsto hg (hcont.tendsto g)
  let F : C(K, ℝ) := ⟨fun x => f x, hf.comp continuous_subtype_val⟩
  have hF : Φ F = cfc f Q := by
    change cfcHom hQ _ = cfc f Q
    rw [cfc_apply f Q hQ hf.continuousOn]
    congr 1
  have h := hall F
  rw [hF] at h
  exact h

end BC4lean.KKTheory
