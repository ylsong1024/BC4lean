import BC4lean.CliffordOddConditionalConnection
import BC4lean.CliffordQuarterPhasePositivity

/-! # True positive lifts under grading-controlled Pauli transport

Oddness of the original first operator gives the exact Pauli first
operator after conjugation. Both genuine source-coordinate localized lifts
then form the actual Hilbert-sum lift and transport to the Koszul half
representation. No global or unlocalized positivity is substituted.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordOddConditionalPauli
open CliffordExternalEvenRepresentation

variable {C M : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Cᵐᵒᵖ M] [CStarModule Cᵐᵒᵖ M]
  [CompleteSpace M]
  (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading C) M)

local instance cliffordOddConditionalPositivityLocalInstance1 : CompleteSpace (HilbertModuleSum C M M) := hilbertModuleSum_complete

theorem transport_signed_odd (A : AdjointableMap C M M) (hA : J.IsOdd J A) :
    (hilbertEquiv J).transport (CliffordOddSourceCycle.operator A) = sumMap A A := by
  have hW (T : AdjointableMap C (HilbertModuleSum C M M) (HilbertModuleSum C M M)) :
      (hilbertEquiv J).transport ((hilbertEquiv J).transport T) = T := by
    ext z
    simp only [HilbertModuleEquiv.transport_apply, hilbertEquiv_apply,
      hilbertEquiv_symm_apply, operator_involutive]
  have h := congrArg (hilbertEquiv J).transport (transport_diagonal_odd J A hA)
  rw [hW] at h
  exact h.symm

variable {A : Type*} [NonUnitalCStarAlgebra A]
  (ρ : A →⋆ₙₐ[ℂ] AdjointableMap C M M)
  (hρ : ∀ a, J.toAdjointable * ρ a = ρ a * J.toAdjointable)

theorem localized_positive (T G : AdjointableMap C M M) (hT : J.IsOdd J T)
    (a : A × A)
    (hposP : IsPositiveModuloModuleCompact
      (ρ a.1 * (T * G + G * T) * star (ρ a.1)))
    (hposQ : IsPositiveModuloModuleCompact
      (ρ a.2 * (T * G + G * T) * star (ρ a.2))) :
    IsPositiveModuloModuleCompact
      (sumMap (halfRepresentation ρ J hρ a)
        (halfRepresentation ρ J hρ (cliffordCoefficientGrading.automorphism a)) *
      (sumMap T T * (hilbertEquiv J).transport (CliffordOddSourceCycle.operator G) +
        (hilbertEquiv J).transport (CliffordOddSourceCycle.operator G) * sumMap T T) *
      star (sumMap (halfRepresentation ρ J hρ a)
        (halfRepresentation ρ J hρ (cliffordCoefficientGrading.automorphism a)))) := by
  have h := (hposP.sumMap hposQ).transport (hilbertEquiv J)
  have heq : sumMap (ρ a.1 * (T * G + G * T) * star (ρ a.1))
      (ρ a.2 * (T * G + G * T) * star (ρ a.2)) =
      sumMap (ρ a.1) (ρ a.2) *
        (CliffordOddSourceCycle.operator T * CliffordOddSourceCycle.operator G +
          CliffordOddSourceCycle.operator G * CliffordOddSourceCycle.operator T) *
        star (sumMap (ρ a.1) (ρ a.2)) := by
    rw [CliffordQuarterPhase.signed_anticommutator, ← sumMap_star,
      ← sumMap_mul, ← sumMap_mul]
  rw [heq, HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_mul,
    HilbertModuleEquiv.transport_add, HilbertModuleEquiv.transport_mul,
    HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_star,
    transport_representation J ρ hρ a, transport_signed_odd J T hT] at h
  exact h

end BC4lean.KKTheory.CliffordOddConditionalPauli
