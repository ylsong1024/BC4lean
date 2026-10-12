import BC4lean.CliffordExternalEvenMonoidalConnection
import BC4lean.EssentialModulePositivityFibre
import Mathlib.Tactic.NoncommRing

/-! # Genuine localized positivity under external even Clifford extension

The anticommutator of two odd operators is even. Its Koszul half
localization is exactly the sum of the two original localized operators
compressed by the actual orthogonal grading projections. Positive lifts
therefore transfer, with their real compact errors, before unitary transport.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {C M : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Cᵐᵒᵖ M]
  [CStarModule Cᵐᵒᵖ M] [CompleteSpace M]

theorem IsPositiveModuloModuleCompact.cliffordPairMap
    {S T : AdjointableMap C M M}
    (hS : IsPositiveModuloModuleCompact S) (hT : IsPositiveModuloModuleCompact T) :
    IsPositiveModuloModuleCompact (cliffordPairMap S T) := by
  obtain ⟨V, hV⟩ := hS.exists_star_square
  obtain ⟨W, hW⟩ := hT.exists_star_square
  apply (isPositiveModuloModuleCompact_iff_star_square _).2
  refine ⟨BC4lean.KKTheory.cliffordPairMap V W, ?_⟩
  simpa only [← cliffordPairMap_star, ← cliffordPairMap_mul, ← cliffordPairMap_sub]
    using hV.cliffordPairMap hW

namespace CliffordExternalEvenMonoidal
open CliffordExternalEvenRepresentation CliffordExternalEvenBalancedTensor

variable {A : Type*} [NonUnitalCStarAlgebra A]
  (φ : A →⋆ₙₐ[ℂ] AdjointableMap C M M)
  (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading C) M)
  (hφ : ∀ a, J.toAdjointable * φ a = φ a * J.toAdjointable)
  (V : AdjointableMap C M M) (hV : J.toAdjointable * V = V * J.toAdjointable)

include hV in
theorem plus_commutes_operator : plus J * V = V * plus J := by
  simp only [plus, CliffordOne.plusProjection, smul_mul_assoc, mul_smul_comm,
    add_mul, mul_add, one_mul, mul_one, hV]

include hV in
theorem minus_commutes_operator : minus J * V = V * minus J := by
  simp only [minus, CliffordOne.minusProjection, smul_mul_assoc, mul_smul_comm,
    sub_mul, mul_sub, one_mul, mul_one, hV]

include hV in
theorem half_localization (a : A × A) :
    halfRepresentation φ J hφ a * V * star (halfRepresentation φ J hφ a) =
      plus J * (φ a.1 * V * star (φ a.1)) * star (plus J) +
        minus J * (φ a.2 * V * star (φ a.2)) * star (minus J) := by
  have hstarP (b : A) : plus J * star (φ b) = star (φ b) * plus J := by
    simpa only [map_star] using plus_commutes φ J hφ (star b)
  have hstarM (b : A) : minus J * star (φ b) = star (φ b) * minus J := by
    simpa only [map_star] using minus_commutes φ J hφ (star b)
  have hcrossPM : plus J * V * minus J = 0 := by
    rw [plus_commutes_operator J V hV, mul_assoc, plus_mul_minus, mul_zero]
  have hcrossMP : minus J * V * plus J = 0 := by
    rw [minus_commutes_operator J V hV, mul_assoc, minus_mul_plus, mul_zero]
  have hPM : (φ a.1 * plus J) * V * (minus J * star (φ a.2)) = 0 := by
    calc
      _ = φ a.1 * (plus J * V * minus J) * star (φ a.2) := by noncomm_ring
      _ = 0 := by rw [hcrossPM, mul_zero, zero_mul]
  have hMP : (φ a.2 * minus J) * V * (plus J * star (φ a.1)) = 0 := by
    calc
      _ = φ a.2 * (minus J * V * plus J) * star (φ a.1) := by noncomm_ring
      _ = 0 := by rw [hcrossMP, mul_zero, zero_mul]
  have hPP : (φ a.1 * plus J) * V * (plus J * star (φ a.1)) =
      plus J * (φ a.1 * V * star (φ a.1)) * plus J := by
    rw [← plus_commutes φ J hφ, hstarP]
    noncomm_ring
  have hMM : (φ a.2 * minus J) * V * (minus J * star (φ a.2)) =
      minus J * (φ a.2 * V * star (φ a.2)) * minus J := by
    rw [← minus_commutes φ J hφ, hstarM]
    noncomm_ring
  have hPstar : star (plus J) = plus J := plus_adjoint J
  have hMstar : star (minus J) = minus J := minus_adjoint J
  rw [halfRepresentation_eq]
  change (φ a.1 * plus J + φ a.2 * minus J) * V *
    star (φ a.1 * plus J + φ a.2 * minus J) = _
  simp only [star_add, star_mul, hPstar, hMstar,
    add_mul, mul_add, hPP, hPM, hMP, hMM, add_zero, zero_add]

include hV in
theorem half_localized_positivity
    (hpos : ∀ a, IsPositiveModuloModuleCompact (φ a * V * star (φ a)))
    (a : A × A) :
    IsPositiveModuloModuleCompact
      (halfRepresentation φ J hφ a * V * star (halfRepresentation φ J hφ a)) := by
  rw [half_localization φ J hφ V hV]
  exact ((hpos a.1).star_right_conjugate (plus J)).add
    ((hpos a.2).star_right_conjugate (minus J))

variable {Γ B H F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace H] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C}
  (c : GradedKasparovCycle α β CStarGrading.trivial CStarGrading.trivial H)
  (d : GradedKasparovCycle β γ CStarGrading.trivial CStarGrading.trivial F)
  (R : AdjointableMap C (InteriorModuleTensor (E := H) d.representation)
    (InteriorModuleTensor (E := H) d.representation))
  (hR : IsGradedKasparovProductOperator c d R)

include hR in
theorem productPositivity (a : A × A) :
    IsPositiveModuloModuleCompact (gradedKasparovProductPositivityOperator
      (CliffordExternalEvenCycle.cycle c) (CliffordExternalEvenCycle.cycle d)
        (productOperator d R) a) := by
  let K := gradedKasparovTensorGrading c d
  let ρ := gradedKasparovTensorRepresentation c d
  let T := interiorModuleTensorOperator d.representation c.operator
  let V := T * R + R * T
  have hρ : ∀ b, K.toAdjointable * ρ b = ρ b * K.toAdjointable := by
    intro b
    ext z
    exact gradedKasparovTensorRepresentation_graded c d b z
  have hT : K.IsOdd K T := c.operator_odd.interiorModuleTensorOperator
    d.grading d.representation_graded
  have hVeven : K.IsEven K V :=
    (hT.comp_odd hR.cycleConditions.operator_odd).add
      (hR.cycleConditions.operator_odd.comp_odd hT)
  have hV : K.toAdjointable * V = V * K.toAdjointable := by
    ext z
    exact hVeven z
  have hpos : ∀ b, IsPositiveModuloModuleCompact (ρ b * V * star (ρ b)) := hR.positivity
  have hplus := half_localized_positivity ρ K hρ V hV hpos a
  have hminus := half_localized_positivity ρ K hρ V hV hpos
    (cliffordCoefficientGrading.automorphism a)
  have hpair := hplus.cliffordPairMap hminus
  have htransport : (hilbertEquiv (H := H) d).transport
      (gradedKasparovProductPositivityOperator (CliffordExternalEvenCycle.cycle c)
        (CliffordExternalEvenCycle.cycle d) (productOperator d R) a) =
      cliffordPairMap
        (halfRepresentation ρ K hρ a * V * star (halfRepresentation ρ K hρ a))
        (halfRepresentation ρ K hρ (cliffordCoefficientGrading.automorphism a) * V *
          star (halfRepresentation ρ K hρ (cliffordCoefficientGrading.automorphism a))) := by
    let U := hilbertEquiv (H := H) d
    have hrep : U.transport (gradedKasparovTensorRepresentation
        (CliffordExternalEvenCycle.cycle c) (CliffordExternalEvenCycle.cycle d) a) =
        cliffordPairMap (halfRepresentation ρ K hρ a)
          (halfRepresentation ρ K hρ (cliffordCoefficientGrading.automorphism a)) := by
      have h := transport_representation c d R hR.cycleConditions a
      change U.transport (gradedKasparovTensorRepresentation
        (CliffordExternalEvenCycle.cycle c) (CliffordExternalEvenCycle.cycle d) a) =
        cliffordPairMap (halfRepresentation ρ K hρ a)
          (halfRepresentation ρ K hρ (cliffordCoefficientGrading.automorphism a)) at h
      exact h
    have hfirst : U.transport (interiorModuleTensorOperator
        (CliffordExternalEvenCycle.cycle d).representation (CliffordExternalEvenCycle.cycle c).operator) =
        cliffordPairMap T T := transport_firstOperator c d
    have hop : U.transport (productOperator d R) = cliffordPairMap R R := by
      change U.transport (U.symm.transport (cliffordPairMap R R)) = cliffordPairMap R R
      exact U.transport_symm_symm _
    change U.transport (gradedKasparovTensorRepresentation
      (CliffordExternalEvenCycle.cycle c) (CliffordExternalEvenCycle.cycle d) a *
      (interiorModuleTensorOperator (CliffordExternalEvenCycle.cycle d).representation
        (CliffordExternalEvenCycle.cycle c).operator * productOperator d R +
      productOperator d R * interiorModuleTensorOperator (CliffordExternalEvenCycle.cycle d).representation
        (CliffordExternalEvenCycle.cycle c).operator) *
      star (gradedKasparovTensorRepresentation (CliffordExternalEvenCycle.cycle c)
        (CliffordExternalEvenCycle.cycle d) a)) = _
    rw [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_mul,
      HilbertModuleEquiv.transport_add, HilbertModuleEquiv.transport_mul,
      HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_star, hrep, hfirst, hop]
    simp only [cliffordPairMap_mul, cliffordPairMap_add, cliffordPairMap_star, V]
  have h := hpair.transport (hilbertEquiv (H := H) d).symm
  rw [← htransport, HilbertModuleEquiv.transport_symm] at h
  exact h

include hR in
theorem isProduct : IsGradedKasparovProductOperator
    (CliffordExternalEvenCycle.cycle c) (CliffordExternalEvenCycle.cycle d)
    (productOperator d R) where
  cycleConditions := productConditions c d R hR.cycleConditions
  connection := productConnection c d R hR.connection
  positivity := productPositivity c d R hR

end CliffordExternalEvenMonoidal
end BC4lean.KKTheory
