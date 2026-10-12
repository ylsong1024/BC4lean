import BC4lean.UnitizedRelativeProjectionCoefficientTensor
import BC4lean.OrdinaryScalarCoefficientTensorIso
import BC4lean.GroupUniverseOrdinaryEven
import BC4lean.ScalarKasparovK0IndexUniverse

/-! # Actual coefficient naturality on finite relative projection generators

The ordinary coefficient map is the independently defined homomorphism-cycle
Kasparov product. Its true completed tensor representative is transported
from the small source carrier to the actual image cycle. The genuine image
interval then identifies it with the mapped pair on the full target module.
The source and target coefficient universes remain independent.
-/

noncomputable section
universe uB uC
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory

variable {B : Type uB} {C : Type uC}
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local notation "α₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
local notation "β₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B)
local notation "γ₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit C)

local instance standardScalarRelativeProjectionCoefficientNaturalityLocalInstance01 (A : Type*) [CStarAlgebra A] : PartialOrder A := CStarAlgebra.spectralOrder A
local instance standardScalarRelativeProjectionCoefficientNaturalityLocalInstance02 (A : Type*) [CStarAlgebra A] : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance standardScalarRelativeProjectionCoefficientNaturalityLocalInstance03 : CompleteSpace (FiniteStandardModule B ι) := finiteStandardModule_complete
local instance standardScalarRelativeProjectionCoefficientNaturalityLocalInstance04 {M N : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Bᵐᵒᵖ M]
    [CStarModule Bᵐᵒᵖ M] [CompleteSpace M] [NormedAddCommGroup N] [NormedSpace ℂ N]
    [SMul Bᵐᵒᵖ N] [CStarModule Bᵐᵒᵖ N] [CompleteSpace N] :
    CompleteSpace (HilbertModuleSum B M N) := hilbertModuleSum_complete
local instance standardScalarRelativeProjectionCoefficientNaturalityLocalInstance05 (f : B →⋆ₙₐ[ℂ] C) :
    CompleteSpace (FiniteHilbertModuleSum C (CoefficientImageRightModule f) ι) := finiteHilbertModuleSum_complete
local instance standardScalarRelativeProjectionCoefficientNaturalityLocalInstance06 {M N : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Cᵐᵒᵖ M]
    [CStarModule Cᵐᵒᵖ M] [CompleteSpace M] [NormedAddCommGroup N] [NormedSpace ℂ N]
    [SMul Cᵐᵒᵖ N] [CStarModule Cᵐᵒᵖ N] [CompleteSpace N] :
    CompleteSpace (HilbertModuleSum C M N) := hilbertModuleSum_complete

/-- The existing scalar-kernel coefficient homomorphism maps the genuine finite pair. -/
theorem operatorK0Map_equalScalarProjectionDifference (f : B →⋆ₙₐ[ℂ] C)
    (p q : MatrixProjection (Unitization ℂ B) ι)
    (h : ∀ i j, (p.val i j).fst = (q.val i j).fst) :
    operatorK0Map f (equalScalarProjectionDifference p q h) =
      equalScalarProjectionDifference (matrixProjectionMap (Unitization.starMap f) p)
        (matrixProjectionMap (Unitization.starMap f) q)
        (coefficientImageRelativeProjection_scalar_map f p q h) := by
  apply Subtype.ext
  change k0Map (Unitization.starMap f)
      (k0Projection (finiteProjectionOfMatrix p) - k0Projection (finiteProjectionOfMatrix q)) =
    k0Projection (finiteProjectionOfMatrix (matrixProjectionMap (Unitization.starMap f) p)) -
      k0Projection (finiteProjectionOfMatrix (matrixProjectionMap (Unitization.starMap f) q))
  simp only [k0Projection_finiteProjectionOfMatrix]
  rw [map_sub, k0Map_projection, k0Map_projection]
  rfl

/-- Actual product naturality on a finite pair after a genuine module-zero shrink. -/
theorem nonunitalRelativeK0KasparovMapAtZero_equalScalarPair_natural
    (f : B →⋆ₙₐ[ℂ] C) (p q : MatrixProjection (Unitization ℂ B) ι)
    (h : ∀ i j, (p.val i j).fst = (q.val i j).fst) :
    GroupUniverseOrdinaryEven.coefficientPushforward f
      (nonunitalRelativeK0KasparovMapAtUniverse.{uB, 0} (equalScalarProjectionDifference p q h)) =
      nonunitalRelativeK0KasparovMap (operatorK0Map f (equalScalarProjectionDifference p q h)) := by
  let c : BundledKasparovCycle.{0, 0, uB, uB} α₁ β₁ :=
    BundledKasparovCycle.of (unitizedRelativeProjectionCycle (Γ := PUnit) p q h)
  let c₀ : BundledKasparovCycle.{0, 0, uB, 0} α₁ β₁ := c.shrink
  let d := coefficientImageRelativeProjectionCycle f p q h
  have hIso : KasparovCycleIso (c₀.cycle.scalarCoefficientTensor f) d :=
    (c.shrinkIso.symm.scalarCoefficientTensor f).trans
      (unitizedRelativeProjectionCoefficientTensorIso f p q h)
  calc
    _ = KasparovHomotopyClass.mk (BundledKasparovCycle.of (c₀.cycle.scalarCoefficientTensor f)) := by
      unfold nonunitalRelativeK0KasparovMapAtUniverse
      rw [AddMonoidHom.comp_apply, nonunitalRelativeK0KasparovMap_equalScalarProjectionDifference,
        GroupShrinkEvenBridge.addEquivalence_mk]
      simpa only [c₀, c, BundledKasparovCycle.of_storedCycle] using
        GroupUniverseOrdinaryEven.coefficientPushforward_mk_scalarCoefficientTensor c₀.cycle f
    _ = KasparovHomotopyClass.mk (BundledKasparovCycle.of d) :=
      KasparovHomotopyClass.mk_eq_of_iso hIso
    _ = KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (unitizedRelativeProjectionCycle (Γ := PUnit)
          (matrixProjectionMap (Unitization.starMap f) p) (matrixProjectionMap (Unitization.starMap f) q)
          (coefficientImageRelativeProjection_scalar_map f p q h))) :=
      (coefficientImageRelativeProjection_class f p q h).symm
    _ = _ := by
      rw [operatorK0Map_equalScalarProjectionDifference,
        nonunitalRelativeK0KasparovMap_equalScalarProjectionDifference]

end BC4lean.KKTheory
