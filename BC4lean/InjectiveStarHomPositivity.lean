import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.Normed.Order.Lattice

/-! # Positivity reflected by injective complex star homomorphisms

An injective nonunital complex star homomorphism between actual C⋆-algebras
reflects positivity for their given star-compatible orders. The proof reflects
selfadjointness and commutes with the negative part through the continuous
functional calculus. It does not replace either algebra's order.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {A D : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra D]

/-- Injectivity reflects the actual selfadjointness equation. -/
theorem injectiveStarHom_isSelfAdjoint_iff (f : A →⋆ₙₐ[ℂ] D)
    (hf : Function.Injective f) (a : A) : IsSelfAdjoint (f a) ↔ IsSelfAdjoint a := by
  constructor
  · intro h
    show star a = a
    apply hf
    simpa only [map_star] using h.star_eq
  · intro h
    exact h.map f

/-- An injective star homomorphism commutes with the negative part of a
selfadjoint element; its isometry supplies the needed continuity. -/
theorem injectiveStarHom_map_negPart (f : A →⋆ₙₐ[ℂ] D)
    (hf : Function.Injective f) (a : A) (ha : IsSelfAdjoint a) :
    f a⁻ = (f a)⁻ := by
  rw [CFC.negPart_def, CFC.negPart_def]
  exact f.map_cfcₙ (fun x : ℝ => x⁻) a
    continuous_negPart.continuousOn (by simp)
    (NonUnitalStarAlgHom.isometry f hf).continuous ha (ha.map f)

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D]

/-- Positivity is reflected by an injective complex nonunital star homomorphism. -/
theorem injectiveStarHom_nonneg_iff (f : A →⋆ₙₐ[ℂ] D)
    (hf : Function.Injective f) (a : A) : 0 ≤ f a ↔ 0 ≤ a := by
  constructor
  · intro hfa
    have ha : IsSelfAdjoint a :=
      (injectiveStarHom_isSelfAdjoint_iff f hf a).mp hfa.isSelfAdjoint
    apply (CFC.negPart_eq_zero_iff a ha).mp
    apply hf
    rw [map_zero, injectiveStarHom_map_negPart f hf a ha]
    exact (CFC.negPart_eq_zero_iff (f a) hfa.isSelfAdjoint).mpr hfa
  · exact map_nonneg f

/-- The same homomorphism reflects comparisons through positivity of differences. -/
theorem injectiveStarHom_le_iff (f : A →⋆ₙₐ[ℂ] D)
    (hf : Function.Injective f) (a b : A) : f a ≤ f b ↔ a ≤ b := by
  constructor
  · intro h
    apply sub_nonneg.mp
    apply (injectiveStarHom_nonneg_iff f hf (b - a)).mp
    simpa only [map_sub] using sub_nonneg.mpr h
  · intro h
    exact OrderHomClass.mono f h

end BC4lean.KKTheory
