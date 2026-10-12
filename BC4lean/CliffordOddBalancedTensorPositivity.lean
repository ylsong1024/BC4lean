import BC4lean.CliffordOddBalancedTensorConnection
import BC4lean.GradedKasparovProductCriterion
import BC4lean.EssentialModulePositivityFibre

/-! # Actual localized odd-by-odd positivity before matrix Morita reduction

The first factor is the genuine signed diagonal (F tensor 1, minus F
tensor 1). The completed balanced coefficient-form unitary sends the
whole localized anticommutator to exactly the coordinate localization.
Positive lifts and their actual compact errors transfer with that unitary.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordOddBalancedTensor

variable {B C E F : Type*}
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)

local instance cliffordOddBalancedTensorPositivityLocalInstance1 : CompleteSpace (HilbertModuleSum C F F) := hilbertModuleSum_complete
local instance cliffordOddBalancedTensorPositivityLocalInstance2 : CompleteSpace (Target (E := E) φ) := hilbertModuleSum_complete

theorem transport_firstFactor (S T : AdjointableMap B E E) :
    (hilbertEquiv (E := E) φ).transport
      (interiorModuleTensorOperator (CliffordOddSourceCycle.representation φ)
        (cliffordPairMap S T)) =
      sumMap (interiorModuleTensorOperator φ S) (interiorModuleTensorOperator φ T) := by
  ext z
  change hilbertEquiv φ
    (interiorModuleTensorOperator (CliffordOddSourceCycle.representation φ)
      (cliffordPairMap S T) ((hilbertEquiv φ).symm z)) = _
  rw [hilbertEquiv_firstFactor, HilbertModuleEquiv.apply_symm_apply]

theorem transport_signedFirstFactor (T : AdjointableMap B E E) :
    (hilbertEquiv (E := E) φ).transport
      (interiorModuleTensorOperator (CliffordOddSourceCycle.representation φ)
        (cliffordPairMap T (-T))) =
      sumMap (interiorModuleTensorOperator φ T) (-interiorModuleTensorOperator φ T) := by
  rw [transport_firstFactor]
  exact congrArg (sumMap (interiorModuleTensorOperator φ T))
    (map_neg (interiorModuleTensorOperatorHom φ) T)

variable {Γ A : Type*} [Group Γ] [NonUnitalCStarAlgebra A]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C}
  (c : OddKasparovCycle α β E) (d : OddKasparovCycle β γ F)

def coordinateRepresentation : A →⋆ₙₐ[ℂ]
    AdjointableMap C (Target (E := E) d.representation)
      (Target (E := E) d.representation) :=
  sumRepresentation
    ((interiorModuleTensorOperatorHom d.representation).toNonUnitalStarAlgHom.comp c.representation)
    ((interiorModuleTensorOperatorHom d.representation).toNonUnitalStarAlgHom.comp c.representation)

theorem transport_representation (a : A) :
    (hilbertEquiv (E := E) d.representation).transport
      (gradedKasparovTensorRepresentation c.cliffordExpansion (CliffordOddSourceCycle.cycle d) a) =
      coordinateRepresentation c d a :=
  transport_firstFactor d.representation (c.representation a) (c.representation a)

def coordinatePositivityOperator
    (R : AdjointableMap C (Source (E := E) d.representation)
      (Source (E := E) d.representation)) (a : A) :
    AdjointableMap C (Target (E := E) d.representation)
      (Target (E := E) d.representation) :=
  coordinateRepresentation c d a *
    (sumMap (interiorModuleTensorOperator d.representation c.operator)
        (-interiorModuleTensorOperator d.representation c.operator) *
          coordinateOperator d.representation R +
      coordinateOperator d.representation R *
        sumMap (interiorModuleTensorOperator d.representation c.operator)
          (-interiorModuleTensorOperator d.representation c.operator)) *
    star (coordinateRepresentation c d a)

theorem transport_productPositivity
    (R : AdjointableMap C (Source (E := E) d.representation)
      (Source (E := E) d.representation)) (a : A) :
    (hilbertEquiv (E := E) d.representation).transport
      (gradedKasparovProductPositivityOperator c.cliffordExpansion
        (CliffordOddSourceCycle.cycle d) R a) = coordinatePositivityOperator c d R a := by
  let ρa : AdjointableMap C (Source (E := E) d.representation)
      (Source (E := E) d.representation) :=
    gradedKasparovTensorRepresentation c.cliffordExpansion (CliffordOddSourceCycle.cycle d) a
  let Q : AdjointableMap C (Source (E := E) d.representation)
      (Source (E := E) d.representation) :=
    interiorModuleTensorOperator (E := CliffordPairModule B E)
      (CliffordOddSourceCycle.representation d.representation)
      (cliffordPairMap c.operator (-c.operator))
  change (hilbertEquiv (E := E) d.representation).transport
      (ρa * (Q * R + R * Q) * star ρa) = coordinatePositivityOperator c d R a
  let T : AdjointableMap C (Source (E := E) d.representation)
      (Source (E := E) d.representation) ≃⋆ₐ[ℂ]
        AdjointableMap C (Target (E := E) d.representation)
          (Target (E := E) d.representation) :=
    (hilbertEquiv (E := E) d.representation).transportStarAlgEquiv
  have hρ : T ρa = coordinateRepresentation c d a := by
    change (hilbertEquiv (E := E) d.representation).transport ρa = _
    exact transport_representation c d a
  have hQ : T Q = sumMap (interiorModuleTensorOperator d.representation c.operator)
      (-interiorModuleTensorOperator d.representation c.operator) := by
    change (hilbertEquiv (E := E) d.representation).transport Q = _
    exact transport_signedFirstFactor d.representation c.operator
  change T (ρa * (Q * R + R * Q) * star ρa) =
    coordinateRepresentation c d a *
      (sumMap (interiorModuleTensorOperator d.representation c.operator)
          (-interiorModuleTensorOperator d.representation c.operator) * T R +
        T R * sumMap (interiorModuleTensorOperator d.representation c.operator)
          (-interiorModuleTensorOperator d.representation c.operator)) *
      star (coordinateRepresentation c d a)
  simp only [map_mul, map_add, map_star, hρ, hQ]

theorem coordinate_productPositivity
    (R : AdjointableMap C (Source (E := E) d.representation)
      (Source (E := E) d.representation))
    (hR : IsGradedKasparovProductOperator c.cliffordExpansion (CliffordOddSourceCycle.cycle d) R)
    (a : A) : IsPositiveModuloModuleCompact (coordinatePositivityOperator c d R a) := by
  rw [← transport_productPositivity]
  exact (hR.positivity a).transport (hilbertEquiv d.representation)

end BC4lean.KKTheory.CliffordOddBalancedTensor
