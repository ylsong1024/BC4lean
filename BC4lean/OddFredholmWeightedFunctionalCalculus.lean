import BC4lean.OddFredholmExponential
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! # Continuous functional calculus from an actual weighted intertwiner

A continuous linear coefficient map intertwining multiplication by the real
coordinate with a selfadjoint operator intertwines the whole genuine
continuous functional calculus. The proof is continuous-function induction
on a compact real subset of the complex plane. This is an analytic transfer
lemma; it does not postulate an odd comparison map or an inverse cycle.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped Topology

variable {A : Type*} [CStarAlgebra A]

/-- An actual continuous weighted coefficient map intertwining the coordinate
intertwines full complex CFC, including both polynomial approximation limits
and the actual star generator. -/
theorem oddFredholmWeightedFunctionalCalculus
    (F : selfAdjoint A) (K : Set ℂ) [CompactSpace K]
    (hσ : spectrum ℂ (F : A) ⊆ K)
    (hreal : ∀ z : K, star (z : ℂ) = (z : ℂ))
    (T : C(K, ℂ) →L[ℂ] A) (H : A) (hT1 : T 1 = H)
    (hTX : ∀ g : C(K, ℂ), (F : A) * T g =
      T (((ContinuousMap.id ℂ).restrict K) * g))
    (f : C(K, ℂ)) :
    cfcHomSuperset (show IsStarNormal (F : A) from inferInstance) hσ f * H = T f := by
  let Φ : C(K, ℂ) →⋆ₐ[ℂ] A :=
    cfcHomSuperset (show IsStarNormal (F : A) from inferInstance) hσ
  have hΦ : Continuous Φ := cfcHomSuperset_continuous _ _
  have hΦX : Φ ((ContinuousMap.id ℂ).restrict K) = (F : A) :=
    cfcHomSuperset_id _ _
  have hXstar : star ((ContinuousMap.id ℂ).restrict K) =
      (ContinuousMap.id ℂ).restrict K := by
    ext z
    exact hreal z
  have hall : ∀ f : C(K, ℂ), ∀ g : C(K, ℂ), Φ f * T g = T (f * g) := by
    intro f
    induction f using ContinuousMap.induction_on_of_compact with
    | const c =>
      intro g
      have hconst : Φ (ContinuousMap.const K c) = algebraMap ℂ A c := Φ.commutes c
      have hfun : ContinuousMap.const K c * g = c • g := by
        ext z
        rfl
      rw [hconst, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
        hfun, T.map_smul]
    | id =>
      intro g
      rw [hΦX]
      exact hTX g
    | star_id =>
      intro g
      rw [hXstar, hΦX]
      exact hTX g
    | add f h hf hh =>
      intro g
      rw [map_add, add_mul, hf g, hh g, ← T.map_add, add_mul]
    | mul f h hf hh =>
      intro g
      rw [map_mul, mul_assoc, hh g, hf (h * g), mul_assoc]
    | frequently f hf =>
      intro g
      have hclosed : IsClosed {h : C(K, ℂ) | Φ h * T g = T (h * g)} :=
        isClosed_eq (hΦ.mul continuous_const)
          (T.continuous.comp (continuous_id.mul continuous_const))
      have hfreq : ∃ᶠ h in 𝓝 f, Φ h * T g = T (h * g) :=
        hf.mono (fun h hh => hh g)
      exact hclosed.mem_of_frequently_of_tendsto hfreq Filter.tendsto_id
  have h := hall f 1
  rw [hT1, mul_one] at h
  exact h

/-- The same transfer lemma for an ordinary globally continuous function,
with its actual full complex functional calculus rather than a new quotient
or an alternative K-group. -/
theorem oddFredholmWeightedFunctionalCalculus_cfc
    (F : selfAdjoint A) (K : Set ℂ) [CompactSpace K]
    (hσ : spectrum ℂ (F : A) ⊆ K)
    (hreal : ∀ z : K, star (z : ℂ) = (z : ℂ))
    (T : C(K, ℂ) →L[ℂ] A) (H : A) (hT1 : T 1 = H)
    (hTX : ∀ g : C(K, ℂ), (F : A) * T g =
      T (((ContinuousMap.id ℂ).restrict K) * g))
    (f : ℂ → ℂ) (hf : Continuous f) :
    cfc f (F : A) * H = T ⟨fun z => f z, hf.comp continuous_subtype_val⟩ := by
  let fK : C(K, ℂ) := ⟨fun z => f z, hf.comp continuous_subtype_val⟩
  have h := oddFredholmWeightedFunctionalCalculus F K hσ hreal T H hT1 hTX fK
  have heval : cfcHomSuperset (show IsStarNormal (F : A) from inferInstance) hσ fK =
      cfc f (F : A) := by
    change cfcHom (show IsStarNormal (F : A) from inferInstance) _ = cfc f (F : A)
    rw [cfc_apply f (F : A) (show IsStarNormal (F : A) from inferInstance) hf.continuousOn]
    congr 1
  rw [heval] at h
  exact h

end BC4lean.KKTheory
