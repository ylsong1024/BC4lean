import BC4lean.FiniteModuleCompactMatrix
import BC4lean.NonunitalOperatorK

/-! # Genuine relative unitization projection classes in the scalar kernel

Two genuine finite projections with the same complete scalar matrix part give
an actual element of the existing scalar-kernel definition of OperatorK0(B).
This is the difference of their projection classes in K0(Unitization(B)), not
a double unitization. It supplies neither index descent nor a group inverse.
-/

noncomputable section
namespace BC4lean.KKTheory

open BC4lean.OperatorKTheory

local instance relativeProjectionSpectralOrder (A : Type*) [CStarAlgebra A] : PartialOrder A :=
  CStarAlgebra.spectralOrder A
local instance relativeProjectionSpectralOrderedRing (A : Type*) [CStarAlgebra A] : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

variable {B : Type*} {ι : Type} [NonUnitalCStarAlgebra B] [Fintype ι] [DecidableEq ι]

/-- A genuine unitization matrix projection as an existing finite projection. -/
def unitizationFiniteProjection (M : CStarMatrix ι ι (Unitization ℂ B)) (hM : IsStarProjection M) :
    FiniteProjection (Unitization ℂ B) :=
  FiniteProjection.ofProjection (⟨M, hM⟩ : MatrixProjection (Unitization ℂ B) ι)

/-- Equality of the full scalar matrices gives equality of the actual scalar
finite projections, by the entrywise scalar quotient. -/
theorem unitizationFiniteProjection_scalar_map_eq
    (M N : CStarMatrix ι ι (Unitization ℂ B)) (hM : IsStarProjection M) (hN : IsStarProjection N)
    (hScalar : unitizationScalarMatrix M = unitizationScalarMatrix N) :
    FiniteProjection.map (scalarQuotient B) (unitizationFiniteProjection M hM) =
      FiniteProjection.map (scalarQuotient B) (unitizationFiniteProjection N hN) := by
  apply congrArg (FiniteProjection.ofProjection (A := ℂ) (ι := ι))
  apply Subtype.ext
  ext i j
  exact congrArg (fun K : CStarMatrix ι ι ℂ => K i j) hScalar

/-- The genuine relative projection difference belongs to the actual scalar
kernel, derived from projection naturality of the existing K0 homomorphism. -/
theorem unitizationRelativeProjection_scalar_zero
    (M N : CStarMatrix ι ι (Unitization ℂ B)) (hM : IsStarProjection M) (hN : IsStarProjection N)
    (hScalar : unitizationScalarMatrix M = unitizationScalarMatrix N) :
    k0Map (scalarQuotient B)
      (k0Projection (unitizationFiniteProjection M hM) -
        k0Projection (unitizationFiniteProjection N hN)) = 0 := by
  rw [map_sub, k0Map_projection, k0Map_projection,
    unitizationFiniteProjection_scalar_map_eq M N hM hN hScalar, sub_self]

/-- The actual element of OperatorK0(B) represented by this genuine finite
relative unitization projection pair. This makes no index-invariance claim. -/
def unitizationRelativeProjectionK0
    (M N : CStarMatrix ι ι (Unitization ℂ B)) (hM : IsStarProjection M) (hN : IsStarProjection N)
    (hScalar : unitizationScalarMatrix M = unitizationScalarMatrix N) : OperatorK0 B :=
  ⟨k0Projection (unitizationFiniteProjection M hM) -
    k0Projection (unitizationFiniteProjection N hN),
    unitizationRelativeProjection_scalar_zero M N hM hN hScalar⟩

@[simp] theorem operatorK0Inclusion_unitizationRelativeProjectionK0
    (M N : CStarMatrix ι ι (Unitization ℂ B)) (hM : IsStarProjection M) (hN : IsStarProjection N)
    (hScalar : unitizationScalarMatrix M = unitizationScalarMatrix N) :
    operatorK0Inclusion B (unitizationRelativeProjectionK0 M N hM hN hScalar) =
      k0Projection (unitizationFiniteProjection M hM) -
        k0Projection (unitizationFiniteProjection N hN) := rfl

end BC4lean.KKTheory
