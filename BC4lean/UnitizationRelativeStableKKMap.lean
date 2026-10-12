import BC4lean.UnitizationScalarRelativeBlockSum
import BC4lean.OperatorK0

/-! # Genuine stable-projection and Grothendieck descent of scalar-relative classes

The explicit Halmos unitary turns a genuine Murray--von Neumann witness into
unitary conjugation after zero padding. Actual block additivity and zero-class
padding therefore descend the scalar-relative class to the existing stable
projection monoid. Its existing Grothendieck universal property gives an
additive map from K0 of the unitization into scalar KK over the original B.
-/

noncomputable section
universe u
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory

variable {B : Type u} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]

local instance relativeStableUnitizationOrder : PartialOrder (Unitization ℂ B) :=
  CStarAlgebra.spectralOrder _
local instance relativeStableUnitizationStarOrderedRing : StarOrderedRing (Unitization ℂ B) :=
  CStarAlgebra.spectralOrderedRing _

/-- The target is the actual full scalar homotopy group over the original coefficient algebra. -/
abbrev RelativeScalarKasparovGroup :=
  KasparovHomotopyClass.{0, 0, u, u}
    (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
    (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B)

/-- An actual same-size Murray--von Neumann witness gives equal scalar-relative classes. -/
theorem unitizationScalarRelativeClass_eq_of_equivalent
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (p q : MatrixProjection (Unitization ℂ B) ι) (h : Projection.Equivalent p q) :
    unitizationScalarRelativeClass p = unitizationScalarRelativeClass q := by
  obtain ⟨v, hvp, hvq⟩ := h
  let w := projectionHalmosUnitary p q v hvp hvq
  let p0 := projectionBlockSum p (Projection.zero : MatrixProjection (Unitization ℂ B) ι)
  let q0 := projectionBlockSum q (Projection.zero : MatrixProjection (Unitization ℂ B) ι)
  have hConjugate : unitaryProjectionConjugate w p0 = q0 := by
    apply Subtype.ext
    exact projectionHalmosMatrix_conjugate p q v hvp hvq
  have hClass := unitizationScalarRelativeClass_unitaryConjugate w p0
  rw [hConjugate] at hClass
  simpa only [p0, q0, unitizationScalarRelativeClass_blockSum,
    unitizationScalarRelativeClass_zero, add_zero] using hClass

/-- Genuine rectangular stable equivalence is handled by the actual padded
Murray--von Neumann witness, with no cancellation assumption. -/
theorem unitizationScalarRelativeClass_eq_of_rectEquivalent
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (p : MatrixProjection (Unitization ℂ B) ι) (q : MatrixProjection (Unitization ℂ B) κ)
    (h : RectEquivalent p q) :
    unitizationScalarRelativeClass p = unitizationScalarRelativeClass q := by
  have hPad := unitizationScalarRelativeClass_eq_of_equivalent
    (projectionBlockSum p (Projection.zero : MatrixProjection (Unitization ℂ B) κ))
    (projectionBlockSum (Projection.zero : MatrixProjection (Unitization ℂ B) ι) q)
    ((rectEquivalent_iff_padded p q).mp h)
  simpa only [unitizationScalarRelativeClass_blockSum, unitizationScalarRelativeClass_zero,
    add_zero, zero_add] using hPad

/-- The actual scalar-relative class of a bundled finite unitization projection. -/
def unitizationFiniteRelativeKKClass (p : FiniteProjection (Unitization ℂ B)) :
    RelativeScalarKasparovGroup (B := B) := unitizationScalarRelativeClass p.projection

/-- The actual finite witness proves the equality needed by quotient descent. -/
theorem unitizationFiniteRelativeKKClass_eq_of_equivalent
    {p q : FiniteProjection (Unitization ℂ B)} (h : FiniteProjection.Equivalent p q) :
    unitizationFiniteRelativeKKClass p = unitizationFiniteRelativeKKClass q :=
  unitizationScalarRelativeClass_eq_of_rectEquivalent p.projection q.projection h

@[simp] theorem unitizationFiniteRelativeKKClass_zero :
    unitizationFiniteRelativeKKClass (FiniteProjection.zero (A := Unitization ℂ B)) = 0 :=
  unitizationScalarRelativeClass_zero

@[simp] theorem unitizationFiniteRelativeKKClass_blockSum
    (p q : FiniteProjection (Unitization ℂ B)) :
    unitizationFiniteRelativeKKClass (FiniteProjection.blockSum p q) =
      unitizationFiniteRelativeKKClass p + unitizationFiniteRelativeKKClass q :=
  unitizationScalarRelativeClass_blockSum p.projection q.projection

/-- Genuine descent to the already defined stable projection monoid. -/
def unitizationStableRelativeKKMap : StableProjectionMonoid (Unitization ℂ B) →+
    RelativeScalarKasparovGroup (B := B) where
  toFun := Quotient.lift unitizationFiniteRelativeKKClass
    (fun _ _ h => unitizationFiniteRelativeKKClass_eq_of_equivalent h)
  map_zero' := unitizationFiniteRelativeKKClass_zero
  map_add' x y := Quotient.inductionOn₂ x y unitizationFiniteRelativeKKClass_blockSum

@[simp] theorem unitizationStableRelativeKKMap_of (p : FiniteProjection (Unitization ℂ B)) :
    unitizationStableRelativeKKMap (StableProjectionMonoid.of p) =
      unitizationFiniteRelativeKKClass p := rfl

/-- The genuine Grothendieck map, taking values over B rather than its unitization. -/
def unitizationK0RelativeKKMap : K0 (Unitization ℂ B) →+ RelativeScalarKasparovGroup (B := B) :=
  k0Universal unitizationStableRelativeKKMap

@[simp] theorem unitizationK0RelativeKKMap_projection (p : FiniteProjection (Unitization ℂ B)) :
    unitizationK0RelativeKKMap (k0Projection p) = unitizationFiniteRelativeKKClass p :=
  k0Universal_class unitizationStableRelativeKKMap (StableProjectionMonoid.of p)

end BC4lean.KKTheory
