import BC4lean.ScalarUnitProjection
import BC4lean.AssemblyPieceHom
import BC4lean.ScalarKKNativeNaturality
import BC4lean.CutoffRestrictionNaturality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! Cutoff and scalar homomorphism classes for the literal Unit group.
The actual compact coefficient algebra and projection normalization are
retained; nontrivial finite-group averaging is not replaced by the unit. -/

noncomputable section
namespace BC4lean.KKTheory.UnitPointCutoff
open BC4lean.ProperActions BC4lean.OperatorKTheory
open scoped ZeroAtInfty ComplexOrder KasparovDescent

section CompactCoefficients
variable (X : Type) [TopologicalSpace X] [CompactSpace X]

/-- Actual scalar constant functions, with vanishing at infinity proved by compactness. -/
def scalarToCZero : ℂ →⋆ₙₐ[ℂ] C₀(X, ℂ) where
  toFun z := ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty (ContinuousMap.const X z)
  map_zero' := by ext x; rfl
  map_add' _ _ := by ext x; rfl
  map_mul' _ _ := by ext x; rfl
  map_smul' _ _ := by ext x; rfl
  map_star' _ := by ext x; rfl

@[simp] theorem scalarToCZero_apply (z : ℂ) (x : X) : scalarToCZero X z x = z := rfl

/-- Actual evaluation on the genuine C0 algebra. -/
def cZeroEvaluation (x : X) : C₀(X, ℂ) →⋆ₙₐ[ℂ] ℂ where
  toFun f := f x
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

/-- The scalar/point algebra identification has actual constant and evaluation inverses. -/
def pointCZeroEquiv [Subsingleton X] (x : X) : ℂ ≃⋆ₐ[ℂ] C₀(X, ℂ) where
  toFun := scalarToCZero X
  invFun := cZeroEvaluation X x
  left_inv _ := rfl
  right_inv f := by
    apply ZeroAtInftyContinuousMap.ext
    intro y
    exact congrArg f (Subsingleton.elim x y)
  map_add' := map_add (scalarToCZero X)
  map_mul' := map_mul (scalarToCZero X)
  map_smul' := map_smul (scalarToCZero X)
  map_star' := map_star (scalarToCZero X)

end CompactCoefficients

variable (X : Type) [TopologicalSpace X] [MulAction Unit X]
  [ContinuousConstSMul Unit X] [CompactSpace X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [ProperSMul Unit X]

local instance cZero_separable : TopologicalSpace.SeparableSpace C₀(X, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

/-- The actual scalar map into the crossed source algebra. -/
def scalarCrossedCoefficient : ℂ →⋆ₙₐ[ℂ] ReducedCrossedProduct (CZero.action Unit (X := X)) :=
  (coefficientToReducedCrossed (CZero.action Unit)).comp (scalarToCZero X)

omit [ContinuousConstSMul Unit X] [CompactSpace X] [LocallyCompactSpace X]
  [T2Space X] [SecondCountableTopology X] [ProperSMul Unit X] in
/-- Unit normalization is exactly the coefficientwise square-one identity. -/
theorem cutoff_square_one (c : Cutoff.CutoffFunction Unit X) (x : X) : c x ^ 2 = 1 := by
  change c.toFun x ^ 2 = 1
  have hd : (default : Unit) = 1 := Subsingleton.elim _ _
  simpa only [finsum_unique, hd, inv_one, one_smul] using c.normalized x

omit [ContinuousConstSMul Unit X] [LocallyCompactSpace X]
  [T2Space X] [SecondCountableTopology X] in
/-- The actual algebraic cutoff projection has only its identity coefficient,
which is the actual constant-one function. No finite-group averaging is replaced by one. -/
theorem algebraicProjection_eq_single (c : Cutoff.CutoffFunction Unit X) :
    Cutoff.algebraicProjection c =
      AlgebraicCrossedProduct.single (CZero.action Unit) 1 (scalarToCZero X 1) := by
  apply AlgebraicCrossedProduct.ext
  intro g
  have hg : g = 1 := Subsingleton.elim _ _
  subst g
  apply ZeroAtInftyContinuousMap.ext
  intro x
  simp only [Cutoff.algebraicProjection, Cutoff.coeff_mixedAlgebraic,
    Cutoff.mixedCZeroCoefficient_apply, AlgebraicCrossedProduct.coeff_single,
    Finsupp.single_eq_same, scalarToCZero_apply, inv_one, one_smul]
  exact (congrArg Complex.ofReal (by
    simpa only [pow_two] using cutoff_square_one X c x) : _)

omit [ContinuousConstSMul Unit X] [LocallyCompactSpace X]
  [T2Space X] [SecondCountableTopology X] in
/-- The concrete completed cutoff projection is f(1) for the actual scalar map. -/
theorem reducedCutoffProjection_eq_scalarCoefficient (c : Cutoff.CutoffFunction Unit X) :
    Cutoff.reducedCutoffProjection c = scalarCrossedCoefficient X 1 := by
  unfold Cutoff.reducedCutoffProjection
  rw [algebraicProjection_eq_single X]
  apply Subtype.ext
  rw [algebraicToReducedCrossed_single]
  change reducedCrossedCoefficient (CZero.action Unit) (scalarToCZero X 1) *
      reducedCrossedRegular (1 : Unit) =
    reducedCrossedCoefficient (CZero.action Unit) (scalarToCZero X 1)
  rw [reducedCrossedRegular_one, mul_one]

omit [ContinuousConstSMul Unit X] in
/-- The actual cutoff KK class is the native standard scalar homomorphism class.
This uses the real projection normalization, genuine scalar index naturality,
and the independently proved scalar-unit calculation. -/
theorem cutoffKKClass_eq_homClass (c : Cutoff.CutoffFunction Unit X) :
    Assembly.cutoffKKClass Unit X c =
      GroupUniverseParityHomCycle.homClass.{0,0,0,0}
        (scalarCrossedCoefficient X) (fun _ _ => rfl) := by
  let α : CStarAlgebraAction Unit ℂ := CStarAlgebraAction.trivial
  let f := scalarCrossedCoefficient X
  let e := GroupUniverseParityUnits.identity.{0,0,0} α
  let δ : CStarAlgebraAction Unit
      (ReducedCrossedProduct (CZero.action Unit (X := X))) := CStarAlgebraAction.trivial
  have hproduct : GroupUniverseParityFunctoriality.coefficientPushforward.{0,0,0,0,0}
      (Γ := Unit) (A := ℂ) (B := ℂ)
      (C := ReducedCrossedProduct (CZero.action Unit (X := X)))
      («α» := α) («β» := α) (γ := δ) false f (fun _ _ => rfl) e =
      GroupUniverseParityHomCycle.homClass.{0,0,0,0}
        (Γ := Unit) (A := ℂ) (B := ReducedCrossedProduct (CZero.action Unit (X := X)))
        («α» := α) («β» := δ) f (fun _ _ => rfl) := by
    change GroupUniverseParityUnits.leftEvenProduct false e
      (GroupUniverseParityHomCycle.homClass.{0,0,0,0}
        (Γ := Unit) (A := ℂ) (B := ReducedCrossedProduct (CZero.action Unit (X := X)))
        («α» := α) («β» := δ) f (fun _ _ => rfl)) = _
    exact GroupUniverseParityUnits.left_identity false _
  have hn := Assembly.scalarKKOperatorK0_native_coefficient_natural.{0,0,0} f e
  rw [hproduct, ScalarUnitProjection.scalarKKOperatorK0AddEquiv_identity] at hn
  rw [nonunitalProjectionK0_map] at hn
  apply (scalarKKOperatorK0AddEquiv.{0,0}
    (B := ReducedCrossedProduct (CZero.action Unit (X := X)))).injective
  change scalarKKOperatorK0AddEquiv
      (scalarKKOperatorK0AddEquiv.symm (Cutoff.cutoffK0 c)) = scalarKKOperatorK0AddEquiv _
  rw [AddEquiv.apply_symm_apply, hn]
  unfold Cutoff.cutoffK0
  have hclass : ∀ (p q : ReducedCrossedProduct (CZero.action Unit (X := X)))
      (hp : IsStarProjection p) (hq : IsStarProjection q),
      p = q → nonunitalProjectionK0 p hp = nonunitalProjectionK0 q hq := by
    intro p q hp hq heq
    cases heq
    rfl
  exact hclass _ _ _ _ (reducedCutoffProjection_eq_scalarCoefficient X c)

end BC4lean.KKTheory.UnitPointCutoff
