import BC4lean.StableProjectionMonoid
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup

/-! # Unital operator K₀ as a Grothendieck group

The input is the verified stable projection monoid. No cancellation or
injectivity of its canonical map to the group completion is assumed.
-/

noncomputable section
namespace BC4lean.OperatorKTheory

universe u v
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The unital operator K₀ group, obtained by group-completing V(A). -/
abbrev K0 (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :=
  Algebra.GrothendieckAddGroup (StableProjectionMonoid A)

/-- The canonical additive map from stable projection classes to K₀. -/
def k0Class : StableProjectionMonoid A →+ K0 A := Algebra.GrothendieckAddGroup.of

/-- The K₀ class of a finite matrix projection. -/
def k0Projection (p : FiniteProjection A) : K0 A := k0Class (StableProjectionMonoid.of p)

@[simp] theorem k0Projection_zero : k0Projection (FiniteProjection.zero : FiniteProjection A) = 0 :=
  map_zero k0Class

@[simp] theorem k0Projection_blockSum (p q : FiniteProjection A) :
    k0Projection (FiniteProjection.blockSum p q) = k0Projection p + k0Projection q := by
  simp only [k0Projection, StableProjectionMonoid.of_blockSum, map_add]

theorem k0Projection_eq_of_equivalent {p q : FiniteProjection A}
    (h : FiniteProjection.Equivalent p q) : k0Projection p = k0Projection q :=
  congrArg k0Class (StableProjectionMonoid.of_eq_of_equivalent h)

/-- Every additive map from V(A) to an abelian group extends uniquely to K₀(A). -/
def k0Universal {G : Type v} [AddCommGroup G] :
    (StableProjectionMonoid A →+ G) ≃ (K0 A →+ G) := Algebra.GrothendieckAddGroup.lift

@[simp] theorem k0Universal_comp {G : Type v} [AddCommGroup G]
    (f : StableProjectionMonoid A →+ G) : (k0Universal f).comp k0Class = f :=
  k0Universal.left_inv f

@[simp] theorem k0Universal_class {G : Type v} [AddCommGroup G]
    (f : StableProjectionMonoid A →+ G) (x : StableProjectionMonoid A) :
    k0Universal f (k0Class x) = f x := DFunLike.congr_fun (k0Universal_comp f) x

theorem k0Universal_unique {G : Type v} [AddCommGroup G]
    (f : StableProjectionMonoid A →+ G) (g : K0 A →+ G)
    (h : g.comp k0Class = f) : k0Universal f = g := by
  apply k0Universal.symm.injective
  exact (k0Universal.left_inv f).trans h.symm

end BC4lean.OperatorKTheory
