import BC4lean.ScalarKasparovK0IndexUniverse
import BC4lean.FiniteRelativeProjectionK0IndexRecovery
import BC4lean.UnitizationK0KernelRepresentative

/-! # The genuine even scalar KK and nonunital operator K₀ comparison

The independently constructed Julia index recovers every finite relative
projection pair. The actual scalar-kernel normal form extends this to the
left inverse on every element of OperatorK₀. The full raw-cycle right inverse
and genuine module-universe transport give the two inverses on the full
Kasparov quotient. Additivity of the index follows from this actual bijection
with the independently constructed additive forward map.
-/

noncomputable section
universe uB uE
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory

variable {B : Type uB} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]
local notation "α₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
local notation "β₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B)

local instance standardScalarKasparovK0ComparisonAddEquivLocalInstance01 (A : Type*) [CStarAlgebra A] : PartialOrder A := CStarAlgebra.spectralOrder A
local instance standardScalarKasparovK0ComparisonAddEquivLocalInstance02 (A : Type*) [CStarAlgebra A] : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

/-- Every scalar-kernel element is recovered, using the genuine finite normal form. -/
theorem scalarKKOperatorK0Index_nonunitalRelativeK0KasparovMap_leftInverse :
    Function.LeftInverse (scalarKKOperatorK0Index (B := B)) nonunitalRelativeK0KasparovMap := by
  intro x
  obtain ⟨ι, hι, dι, P, Q, hP, hQ, hs, hx⟩ := unitizationRelativeProjectionK0_surjective x
  let := hι
  let := dι
  let p : MatrixProjection (Unitization ℂ B) ι := ⟨P, hP⟩
  let q : MatrixProjection (Unitization ℂ B) ι := ⟨Q, hQ⟩
  have h : ∀ i j, (p.val i j).fst = (q.val i j).fst := by
    intro i j
    exact congrArg (fun M : CStarMatrix ι ι ℂ => M i j) hs
  have hClass : equalScalarProjectionDifference p q h =
      unitizationRelativeProjectionK0 P Q hP hQ hs := by
    apply operatorK0Inclusion_injective B
    have hInclusion := equalScalarProjectionDifference_inclusion p q h
    have hFiniteClasses := congrArg₂ (fun a b : K0 (Unitization ℂ B) => a - b)
      (k0Projection_finiteProjectionOfMatrix p) (k0Projection_finiteProjectionOfMatrix q)
    exact hInclusion.trans (hFiniteClasses.trans
      (operatorK0Inclusion_unitizationRelativeProjectionK0 P Q hP hQ hs).symm)
  rw [← hx, nonunitalRelativeK0KasparovMap_unitizationRelativeProjectionK0,
    scalarKKOperatorK0Index_mk]
  change (unitizedRelativeProjectionCycle (Γ := PUnit) p q h).operatorK0Index =
    unitizationRelativeProjectionK0 P Q hP hQ hs
  exact (unitizedRelativeProjectionCycle_operatorK0Index p q h).trans hClass

/-- The actual left inverse is valid in every independent chosen module universe. -/
theorem nonunitalRelativeK0KasparovMapAtUniverse_leftInverse :
    Function.LeftInverse (scalarKKOperatorK0Index (B := B))
      (nonunitalRelativeK0KasparovMapAtUniverse.{uB, uE} (B := B)) := by
  intro x
  change scalarKKOperatorK0Index
    (GroupShrinkEvenBridge.addEquivalence.{0, 0, uB, uB, uE} (nonunitalRelativeK0KasparovMap x)) = x
  rw [scalarKKOperatorK0Index_universe]
  exact scalarKKOperatorK0Index_nonunitalRelativeK0KasparovMap_leftInverse x

/-- The genuine additive forward map is injective, by the independent recovered index. -/
theorem nonunitalRelativeK0KasparovMapAtUniverse_injective :
    Function.Injective (nonunitalRelativeK0KasparovMapAtUniverse.{uB, uE} (B := B)) :=
  nonunitalRelativeK0KasparovMapAtUniverse_leftInverse.injective

/-- Index additivity follows from the independently additive bijective forward map. -/
theorem scalarKKOperatorK0Index_add
    (z w : KasparovHomotopyClass.{0, 0, uB, uE} α₁ β₁) :
    scalarKKOperatorK0Index (z + w) = scalarKKOperatorK0Index z + scalarKKOperatorK0Index w := by
  apply nonunitalRelativeK0KasparovMapAtUniverse_injective
  rw [nonunitalRelativeK0KasparovMapAtUniverse_rightInverse, map_add,
    nonunitalRelativeK0KasparovMapAtUniverse_rightInverse,
    nonunitalRelativeK0KasparovMapAtUniverse_rightInverse]

/-- The actual Julia index as an additive homomorphism on the full quotient. -/
def scalarKKOperatorK0IndexHom :
    KasparovHomotopyClass.{0, 0, uB, uE} α₁ β₁ →+ OperatorK0 B :=
  AddMonoidHom.mk' scalarKKOperatorK0Index scalarKKOperatorK0Index_add

/-- The true even comparison, for every separate coefficient and carrier universe. -/
def scalarKKOperatorK0AddEquiv :
    KasparovHomotopyClass.{0, 0, uB, uE} α₁ β₁ ≃+ OperatorK0 B where
  toFun := scalarKKOperatorK0Index
  invFun := nonunitalRelativeK0KasparovMapAtUniverse
  left_inv := nonunitalRelativeK0KasparovMapAtUniverse_rightInverse
  right_inv := nonunitalRelativeK0KasparovMapAtUniverse_leftInverse
  map_add' := scalarKKOperatorK0Index_add

@[simp] theorem scalarKKOperatorK0AddEquiv_apply
    (z : KasparovHomotopyClass.{0, 0, uB, uE} α₁ β₁) :
    scalarKKOperatorK0AddEquiv z = scalarKKOperatorK0Index z := rfl

@[simp] theorem scalarKKOperatorK0AddEquiv_symm_apply (x : OperatorK0 B) :
    scalarKKOperatorK0AddEquiv.symm x = nonunitalRelativeK0KasparovMapAtUniverse.{uB, uE} x := rfl

end BC4lean.KKTheory
