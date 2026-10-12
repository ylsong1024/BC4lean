import BC4lean.OddFredholmNormalization
import BC4lean.OddFredholmProjectionFibreEquiv

/-! # Actual functional-calculus normalization naturality

This records the concrete formula already used by odd-cycle normalization.
Every unital complex star-algebra homomorphism preserves its symmetrization
and real continuous functional calculus. The statement concerns operator
algebras; no coefficient tensor identification is asserted.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped CStarAlgebra

section Algebra
variable {A D : Type*} [CStarAlgebra A] [CStarAlgebra D]
local instance oddContinuationOddFredholmNormalizationNaturalityLocalInstance01 : PartialOrder A := CStarAlgebra.spectralOrder _
local instance oddContinuationOddFredholmNormalizationNaturalityLocalInstance02 : StarOrderedRing A := CStarAlgebra.spectralOrderedRing _
local instance oddContinuationOddFredholmNormalizationNaturalityLocalInstance03 : PartialOrder D := CStarAlgebra.spectralOrder _
local instance oddContinuationOddFredholmNormalizationNaturalityLocalInstance04 : StarOrderedRing D := CStarAlgebra.spectralOrderedRing _

def oddFredholmSymmetrizedElement (a : A) : A := a + (2 : ℂ)⁻¹ • (star a - a)

def oddFredholmNormalizedElement (a : A) : A :=
  let s := oddFredholmSymmetrizedElement a
  s * cfc fredholmNormWeight (star s * s)

theorem oddFredholmSymmetrizedElement_map (φ : A →⋆ₐ[ℂ] D) (a : A) :
    φ (oddFredholmSymmetrizedElement a) = oddFredholmSymmetrizedElement (φ a) := by
  simp only [oddFredholmSymmetrizedElement, map_add, map_smul, map_sub, map_star]

theorem oddFredholmNormalizedElement_map (φ : A →⋆ₐ[ℂ] D) (a : A) :
    φ (oddFredholmNormalizedElement a) = oddFredholmNormalizedElement (φ a) := by
  unfold oddFredholmNormalizedElement
  rw [map_mul, φ.map_cfc fredholmNormWeight (star (oddFredholmSymmetrizedElement a) *
    oddFredholmSymmetrizedElement a) continuous_fredholmNormWeight.continuousOn
      (ha := IsSelfAdjoint.star_mul_self _)
      (hφa := by simpa only [map_mul, map_star] using
        IsSelfAdjoint.star_mul_self (φ (oddFredholmSymmetrizedElement a)))]
  simp only [map_mul, map_star, oddFredholmSymmetrizedElement_map]

end Algebra

variable {Γ B E : Type*} [Group Γ] [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ ℂ} {β : CStarAlgebraAction Γ B}

theorem oddFredholmNormalizedElement_cycleOperator (c : OddKasparovCycle α β E) :
    oddFredholmNormalizedElement c.operator = c.normalized.operator := rfl

end BC4lean.KKTheory
