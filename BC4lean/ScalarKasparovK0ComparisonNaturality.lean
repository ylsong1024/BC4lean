import BC4lean.ScalarKasparovK0ComparisonAddEquiv
import BC4lean.ScalarRelativeProjectionCoefficientNaturality
import BC4lean.GroupUniverseOrdinaryEvenShrink

/-! # Genuine even KK and operator K₀ comparison naturality

The actual equal-scalar normal form extends finite generator naturality to
every scalar-kernel element. The independently defined coefficient Kasparov
product commutes with actual module shrinking through whole tensor cycle
unitaries. The two proved comparison inverses therefore give naturality for
arbitrary nonunital coefficient maps, including zero maps, and independent
coefficient and module universes.
-/

noncomputable section
universe uB uC uE
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory

variable {B : Type uB} {C : Type uC}
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C]
local notation "α₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
local notation "β₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B)
local notation "γ₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit C)

local instance standardScalarKasparovK0ComparisonNaturalityLocalInstance01 (A : Type*) [CStarAlgebra A] : PartialOrder A := CStarAlgebra.spectralOrder A
local instance standardScalarKasparovK0ComparisonNaturalityLocalInstance02 (A : Type*) [CStarAlgebra A] : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

/-- The actual forward map commutes with the actual product after the genuine zero-universe shrink. -/
theorem nonunitalRelativeK0KasparovMapAtZero_natural (f : B →⋆ₙₐ[ℂ] C) (x : OperatorK0 B) :
    GroupUniverseOrdinaryEven.coefficientPushforward f
      (nonunitalRelativeK0KasparovMapAtUniverse.{uB, 0} x) =
        nonunitalRelativeK0KasparovMap (operatorK0Map f x) := by
  obtain ⟨ι, hι, dι, P, Q, hP, hQ, hs, hx⟩ := unitizationRelativeProjectionK0_surjective x
  let := hι
  let := dι
  let p : MatrixProjection (Unitization ℂ B) ι := ⟨P, hP⟩
  let q : MatrixProjection (Unitization ℂ B) ι := ⟨Q, hQ⟩
  have h : ∀ i j, (p.val i j).fst = (q.val i j).fst :=
    fun i j => congrArg (fun M : CStarMatrix ι ι ℂ => M i j) hs
  have heq : equalScalarProjectionDifference p q h = x := by
    rw [← hx]
    apply operatorK0Inclusion_injective B
    rw [equalScalarProjectionDifference_inclusion,
      operatorK0Inclusion_unitizationRelativeProjectionK0]
    simp only [k0Projection_finiteProjectionOfMatrix, unitizationFiniteProjection, p, q]
  rw [← heq]
  exact nonunitalRelativeK0KasparovMapAtZero_equalScalarPair_natural f p q h

/-- The actual independently constructed Julia index commutes with every coefficient product. -/
theorem scalarKKOperatorK0Index_coefficientPushforward (f : B →⋆ₙₐ[ℂ] C)
    (z : KasparovHomotopyClass.{0, 0, uB, uE} α₁ β₁) :
    scalarKKOperatorK0Index (GroupUniverseOrdinaryEven.coefficientPushforward f z) =
      operatorK0Map f (scalarKKOperatorK0Index z) := by
  let z₀ := GroupShrinkEvenBridge.addEquivalence.{0, 0, uB, uE, 0} z
  have hForward := nonunitalRelativeK0KasparovMapAtZero_natural f (scalarKKOperatorK0Index z₀)
  rw [nonunitalRelativeK0KasparovMapAtUniverse_rightInverse] at hForward
  have hZero : scalarKKOperatorK0Index (GroupUniverseOrdinaryEven.coefficientPushforward f z₀) =
      operatorK0Map f (scalarKKOperatorK0Index z₀) := by
    rw [hForward]
    exact scalarKKOperatorK0Index_nonunitalRelativeK0KasparovMap_leftInverse _
  calc
    _ = scalarKKOperatorK0Index
        (GroupShrinkEvenBridge.addEquivalence.{0, 0, uC, max uE uC, uC}
          (GroupUniverseOrdinaryEven.coefficientPushforward f z)) :=
      (scalarKKOperatorK0Index_universe (GroupUniverseOrdinaryEven.coefficientPushforward f z)).symm
    _ = scalarKKOperatorK0Index (GroupUniverseOrdinaryEven.coefficientPushforward f z₀) := by
      rw [GroupUniverseOrdinaryEven.coefficientPushforward_shrink_zero]
    _ = operatorK0Map f (scalarKKOperatorK0Index z₀) := hZero
    _ = operatorK0Map f (scalarKKOperatorK0Index z) := by
      rw [scalarKKOperatorK0Index_universe]

/-- Naturality of the actual additive comparison, with independent coefficient and carrier universes. -/
theorem scalarKKOperatorK0AddEquiv_natural (f : B →⋆ₙₐ[ℂ] C)
    (z : KasparovHomotopyClass.{0, 0, uB, uE} α₁ β₁) :
    scalarKKOperatorK0AddEquiv (GroupUniverseOrdinaryEven.coefficientPushforward f z) =
      operatorK0Map f (scalarKKOperatorK0AddEquiv z) :=
  scalarKKOperatorK0Index_coefficientPushforward f z

/-- The same naturality is equality of the genuinely defined additive homomorphisms. -/
theorem scalarKKOperatorK0IndexHom_natural (f : B →⋆ₙₐ[ℂ] C) :
    (scalarKKOperatorK0IndexHom (B := C)).comp (GroupUniverseOrdinaryEven.coefficientPushforwardHom f) =
      (operatorK0Map f).comp (scalarKKOperatorK0IndexHom (B := B)) := by
  ext z
  exact scalarKKOperatorK0Index_coefficientPushforward f z

end BC4lean.KKTheory
