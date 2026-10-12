import BC4lean.CompactModuleOperator
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! # Genuine rectangular CFC intertwining modulo module compacts

Two actual selfadjoint operators acting on different Hilbert modules
intertwine continuous real functional calculus modulo the genuine compact
rectangular maps whenever their original intertwining error is compact.
The proof uses a common compact spectral set, genuine continuous-function
induction and closedness of the rectangular compact ideal.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

/-- Actual rectangular compact intertwining passes to real CFC. -/
theorem cfc_intertwining_isModuleCompact
    (T : AdjointableMap B F F) (S : AdjointableMap B E E)
    (hT : IsSelfAdjoint T) (hS : IsSelfAdjoint S) (X : AdjointableMap B E F)
    (hX : IsModuleCompact (T.comp X - X.comp S))
    (f : ℝ → ℝ) (hf : Continuous f) :
    IsModuleCompact ((cfc f T).comp X - X.comp (cfc f S)) := by
  let K : Set ℝ := spectrum ℝ T ∪ spectrum ℝ S
  have hK : IsCompact K := (spectrum.isCompact T).union (spectrum.isCompact S)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hσT : spectrum ℝ T ⊆ K := Set.subset_union_left
  have hσS : spectrum ℝ S ⊆ K := Set.subset_union_right
  let ΦT : C(K, ℝ) →⋆ₐ[ℝ] AdjointableMap B F F := cfcHomSuperset hT hσT
  let ΦS : C(K, ℝ) →⋆ₐ[ℝ] AdjointableMap B E E := cfcHomSuperset hS hσS
  have hΦT : Continuous ΦT := cfcHomSuperset_continuous hT hσT
  have hΦS : Continuous ΦS := cfcHomSuperset_continuous hS hσS
  have hall : ∀ g : C(K, ℝ), IsModuleCompact ((ΦT g).comp X - X.comp (ΦS g)) := by
    intro g
    induction g using ContinuousMap.induction_on_of_compact with
    | const r =>
      have hconstT : ΦT (ContinuousMap.const K r) = algebraMap ℝ (AdjointableMap B F F) r := ΦT.commutes r
      have hconstS : ΦS (ContinuousMap.const K r) = algebraMap ℝ (AdjointableMap B E E) r := ΦS.commutes r
      have hrealT : algebraMap ℝ (AdjointableMap B F F) r = (r : ℂ) • (1 : AdjointableMap B F F) := by
        rw [Algebra.algebraMap_eq_smul_one]
        rfl
      have hrealS : algebraMap ℝ (AdjointableMap B E E) r = (r : ℂ) • (1 : AdjointableMap B E E) := by
        rw [Algebra.algebraMap_eq_smul_one]
        rfl
      rw [hconstT, hconstS, hrealT, hrealS]
      have heq : ((r : ℂ) • (1 : AdjointableMap B F F)).comp X -
          X.comp ((r : ℂ) • (1 : AdjointableMap B E E)) = 0 := by
        ext x
        simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
          AdjointableMap.coe_smul_apply, AdjointableMap.one_apply,
          AdjointableMap.coe_zero_apply, map_smul, sub_self]
      rw [heq]
      exact IsModuleCompact.zero
    | id =>
      simpa only [ΦT, ΦS, cfcHomSuperset_id hT hσT, cfcHomSuperset_id hS hσS] using hX
    | star_id =>
      have heq : star (ContinuousMap.restrict K (ContinuousMap.id ℝ)) =
          ContinuousMap.restrict K (ContinuousMap.id ℝ) := by
        ext x
        simp
      rw [heq]
      simpa only [ΦT, ΦS, cfcHomSuperset_id hT hσT, cfcHomSuperset_id hS hσS] using hX
    | add g h hg hh =>
      have heq : (ΦT (g + h)).comp X - X.comp (ΦS (g + h)) =
          ((ΦT g).comp X - X.comp (ΦS g)) + ((ΦT h).comp X - X.comp (ΦS h)) := by
        rw [map_add, map_add]
        ext x
        simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
          AdjointableMap.coe_add_apply, map_add]
        abel
      rw [heq]
      exact hg.add hh
    | mul g h hg hh =>
      have heq : (ΦT (g * h)).comp X - X.comp (ΦS (g * h)) =
          (ΦT g).comp ((ΦT h).comp X - X.comp (ΦS h)) +
            ((ΦT g).comp X - X.comp (ΦS g)).comp (ΦS h) := by
        rw [map_mul, map_mul]
        ext x
        simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
          AdjointableMap.coe_add_apply, AdjointableMap.mul_apply, map_sub]
        abel
      rw [heq]
      exact (hh.comp_left (ΦT g)).add (hg.comp_right (ΦS h))
    | frequently g hg =>
      let L : AdjointableMap B F F →L[ℂ] AdjointableMap B E F :=
        AdjointableMap.compRightContinuousLinearMap X
      let R : AdjointableMap B E E →L[ℂ] AdjointableMap B E F :=
        AdjointableMap.compLeftContinuousLinearMap X
      have hcont : Continuous (fun h : C(K, ℝ) => (ΦT h).comp X - X.comp (ΦS h)) :=
        (L.continuous.comp hΦT).sub (R.continuous.comp hΦS)
      exact moduleCompact_isClosed.mem_of_frequently_of_tendsto hg (hcont.tendsto g)
  let Ff : C(K, ℝ) := ⟨fun x => f x, hf.comp continuous_subtype_val⟩
  have heqT : ΦT Ff = cfc f T := by
    change cfcHom hT _ = cfc f T
    rw [cfc_apply f T hT hf.continuousOn]
    congr 1
  have heqS : ΦS Ff = cfc f S := by
    change cfcHom hS _ = cfc f S
    rw [cfc_apply f S hS hf.continuousOn]
    congr 1
  simpa only [heqT, heqS] using hall Ff

section EndomorphismConsequences
variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- Ordinary compact commutators pass to actual real CFC. -/
theorem moduleCFC_commutator_isModuleCompact
    (Q X : AdjointableMap B E E) (hQ : IsSelfAdjoint Q)
    (hcomm : IsModuleCompact (Q * X - X * Q)) (f : ℝ → ℝ) (hf : Continuous f) :
    IsModuleCompact (cfc f Q * X - X * cfc f Q) :=
  cfc_intertwining_isModuleCompact Q Q hQ hQ X hcomm f hf

/-- Two actual selfadjoint operators whose difference is compact after
localization have CFC difference compact after that localization when the
second operator has an ordinary compact localization commutator. -/
theorem cfc_sub_mul_isModuleCompact_of_localized_intertwining
    (Q' Q X : AdjointableMap B E E) (hQ' : IsSelfAdjoint Q') (hQ : IsSelfAdjoint Q)
    (hdiff : IsModuleCompact ((Q' - Q) * X))
    (hcomm : IsModuleCompact (Q * X - X * Q)) (f : ℝ → ℝ) (hf : Continuous f) :
    IsModuleCompact ((cfc f Q' - cfc f Q) * X) := by
  have heq : Q' * X - X * Q = (Q' - Q) * X + (Q * X - X * Q) := by noncomm_ring
  have hint : IsModuleCompact (Q' * X - X * Q) := by rw [heq]; exact hdiff.add hcomm
  have h₁ := cfc_intertwining_isModuleCompact Q' Q hQ' hQ X hint f hf
  have h₂ := moduleCFC_commutator_isModuleCompact Q X hQ hcomm f hf
  have hfinal : (cfc f Q' - cfc f Q) * X =
      (cfc f Q' * X - X * cfc f Q) - (cfc f Q * X - X * cfc f Q) := by noncomm_ring
  rw [hfinal]
  exact h₁.sub h₂

end EndomorphismConsequences
end BC4lean.KKTheory
