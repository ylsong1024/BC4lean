import BC4lean.UnitScalarDescent
import BC4lean.UnitPointCutoff
import BC4lean.FiniteGroupPointCalibration
import BC4lean.BaumConnesProperty
import BC4lean.KasparovDescentSourcePullbackClass
import BC4lean.OddKTheoryIndependentCoefficientNaturality
import BC4lean.ReducedGroupCStarTrivial
import BC4lean.OperatorK0Equivalence
import BC4lean.OperatorK1Equivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! The actual canonical assembly map for the literal Unit group.
The point, cutoff, descent and scalar index comparisons identify this map
with an explicit additive equivalence in both degrees. -/

noncomputable section
namespace BC4lean.Chapter8Examples
open ProperActions KKTheory OperatorKTheory
open KKTheory.GroupUniverseParityGroup KKTheory.GroupUniverseParityFunctoriality
open KKTheory.UnitPointCutoff
open scoped ZeroAtInfty ComplexOrder KasparovDescent

abbrev unitScalarAction : CStarAlgebraAction Unit ℂ := CStarAlgebraAction.trivial
abbrev unitScalarInclusion : ℂ →⋆ₙₐ[ℂ] ReducedCrossedProduct unitScalarAction :=
  coefficientToReducedCrossed unitScalarAction
abbrev unitScalarCrossedAlgebra := ReducedCrossedProduct unitScalarAction
abbrev unitReducedAlgebra := ReducedGroupCStar Unit
local instance reducedOrder : PartialOrder unitReducedAlgebra := CStarAlgebra.spectralOrder _
local instance reducedStarOrder : StarOrderedRing unitReducedAlgebra := CStarAlgebra.spectralOrderedRing _

/-- Actual scalar comparison followed by unital agreement and the actual
trivial-group reduced-algebra equivalence, separately in each parity. -/
def unitScalarAnalyticEquiv (p : Bool) :
    KKParityGroup.{0,0,0,0} p unitScalarAction unitScalarAction ≃+ Assembly.analyticGroup Unit p := by
  cases p
  · exact (scalarKKOperatorK0AddEquiv.{0,0}).trans
      ((operatorK0UnitalEquiv ℂ).trans (@k0Equiv ℂ unitReducedAlgebra inferInstance inferInstance
        (CStarAlgebra.spectralOrder ℂ) (CStarAlgebra.spectralOrderedRing ℂ)
        reducedOrder reducedStarOrder (trivialReducedEquiv (Γ := Unit))))
  · exact (oddKKOperatorK1AllModuleUniversesAddEquiv.{0,0}).trans
      ((operatorK1UnitalEquiv ℂ).trans (@k1Equiv ℂ unitReducedAlgebra inferInstance inferInstance
        (CStarAlgebra.spectralOrder ℂ) (CStarAlgebra.spectralOrderedRing ℂ)
        reducedOrder reducedStarOrder (trivialReducedEquiv (Γ := Unit))))

/-- The genuine scalar crossed-product equivalence sends actual coefficients
by precisely the original scalar map into the reduced group algebra. -/
theorem scalarCrossedCoefficient_comp_eq :
    (reducedCrossedScalarProductEquiv (Γ := Unit)).toNonUnitalStarAlgHom.comp unitScalarInclusion =
      (trivialReducedEquiv (Γ := Unit)).toNonUnitalStarAlgHom := by
  apply DFunLike.ext
  intro z
  change reducedCrossedScalarProductEquiv (unitScalarInclusion z) = trivialReducedEquiv z
  calc
    _ = reducedCrossedScalarProductEquiv (unitScalarInclusion (z • (1 : ℂ))) := by simp
    _ = z • reducedCrossedScalarProductEquiv (unitScalarInclusion (1 : ℂ)) := by rw [map_smul, map_smul]
    _ = z • (1 : unitReducedAlgebra) := by rw [reducedCrossedScalarProductEquiv_oneCoefficient]
    _ = trivialReducedEquiv z := by
      rw [trivialReducedEquiv_apply, Algebra.algebraMap_eq_smul_one]

/-- Existing genuine index naturality computes the actual analytic comparison
of coefficient-extended even classes. -/
theorem reducedScalarKKToK0Hom_coefficient (x : KasparovHomotopyClass.{0,0,0,0} unitScalarAction unitScalarAction) :
    Assembly.reducedScalarKKToK0Hom Unit
      (GroupUniverseOrdinaryEven.coefficientPushforward unitScalarInclusion x) =
        unitScalarAnalyticEquiv false x := by
  change operatorK0UnitalEquiv unitReducedAlgebra
      (operatorK0Map (reducedCrossedScalarProductEquiv (Γ := Unit)).toNonUnitalStarAlgHom
        (scalarKKOperatorK0AddEquiv (GroupUniverseOrdinaryEven.coefficientPushforward unitScalarInclusion x))) = _
  rw [scalarKKOperatorK0AddEquiv_natural]
  rw [← AddMonoidHom.comp_apply, ← operatorK0Map_comp, scalarCrossedCoefficient_comp_eq]
  exact operatorK0UnitalEquiv_natural (trivialReducedEquiv (Γ := Unit)).toStarAlgHom
    (scalarKKOperatorK0AddEquiv x)

/-- The odd calculation uses the actual independent-universe odd coefficient
index theorem, with the same scalar coefficient composition. -/
theorem reducedScalarKKToK1Hom_coefficient (x : OddKK.{0,0,0,0} unitScalarAction unitScalarAction) :
    Assembly.reducedScalarKKToK1Hom Unit
      (GroupUniverseOrdinaryOdd.coefficientPushforward unitScalarInclusion x) =
        unitScalarAnalyticEquiv true x := by
  change operatorK1UnitalEquiv unitReducedAlgebra
      (operatorK1Map (reducedCrossedScalarProductEquiv (Γ := Unit)).toNonUnitalStarAlgHom
        (oddKKOperatorK1AllModuleUniversesAddEquiv
          (GroupUniverseOrdinaryOdd.coefficientPushforward unitScalarInclusion x))) = _
  simp only [oddKKOperatorK1AllModuleUniversesAddEquiv_apply]
  rw [oddKKOperatorK1Index_independentCoefficientPushforward]
  rw [← AddMonoidHom.comp_apply, ← operatorK1Map_comp, scalarCrossedCoefficient_comp_eq]
  change operatorK1UnitalEquiv unitReducedAlgebra
      (operatorK1Map (trivialReducedEquiv (Γ := Unit)).toNonUnitalStarAlgHom
        (oddKKOperatorK1Index x)) =
    (@k1Equiv ℂ unitReducedAlgebra inferInstance inferInstance
      (CStarAlgebra.spectralOrder ℂ) (CStarAlgebra.spectralOrderedRing ℂ)
      reducedOrder reducedStarOrder (trivialReducedEquiv (Γ := Unit)))
        (operatorK1UnitalEquiv ℂ (oddKKOperatorK1AllModuleUniversesAddEquiv x))
  rw [oddKKOperatorK1AllModuleUniversesAddEquiv_apply]
  exact operatorK1UnitalEquiv_natural (trivialReducedEquiv (Γ := Unit)).toStarAlgHom
    (oddKKOperatorK1Index x)

/-- Equality of actual source maps is respected, including their dependent
proofs of equivariance. Proof irrelevance identifies those proofs after substitution. -/
private theorem unitSourcePullback_congr
    {A B C : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
    [TopologicalSpace.SeparableSpace C]
    {α : CStarAlgebraAction Unit A} {β : CStarAlgebraAction Unit B}
    {γ : CStarAlgebraAction Unit C}
    (p : Bool) (f g : A →⋆ₙₐ[ℂ] B)
    (hf : ∀ k a, f (α.automorphism k a) = β.automorphism k (f a))
    (hg : ∀ k a, g (α.automorphism k a) = β.automorphism k (g a))
    (h : f = g) (x : KKParityGroup.{0,0,0,0} p β γ) :
    sourcePullback.{0,0,0,0,0} p f hf x = sourcePullback.{0,0,0,0,0} p g hg x := by
  cases h
  rfl

section CompactPoint
variable (X : Type) [TopologicalSpace X] [MulAction Unit X]
  [ContinuousConstSMul Unit X] [CompactSpace X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [ProperSMul Unit X]

local instance cZeroSeparable : TopologicalSpace.SeparableSpace C₀(X, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

omit [ContinuousConstSMul Unit X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] in
/-- Constant scalar functions are genuinely equivariant for the induced action. -/
theorem scalarToCZero_equivariant : ∀ (g : Unit) (z : ℂ),
    scalarToCZero X ((unitScalarAction).automorphism g z) =
      (CZero.action Unit (X := X)).automorphism g (scalarToCZero X z) := by
  intro g z
  apply ZeroAtInftyContinuousMap.ext
  intro x
  rfl

omit [ContinuousConstSMul Unit X] [CompactSpace X] [LocallyCompactSpace X]
  [T2Space X] [SecondCountableTopology X] in
/-- Evaluation is genuinely equivariant because the group itself is Unit. -/
theorem cZeroEvaluation_equivariant (x : X) : ∀ (g : Unit) (f : C₀(X, ℂ)),
    cZeroEvaluation X x ((CZero.action Unit (X := X)).automorphism g f) =
      (unitScalarAction).automorphism g (cZeroEvaluation X x f) := by
  intro g f
  have hg : g = 1 := Subsingleton.elim _ _
  subst g
  rw [CStarAlgebraAction.one_apply, CStarAlgebraAction.one_apply]

/-- The actual source pullback from the point algebra is an additive equivalence,
proved using native source functoriality and the actual inverse evaluation map. -/
def unitPointSourceEquiv [Subsingleton X] (x : X) (p : Bool) :
    TopologicalKHomology.spaceGroup p Unit X ≃+ KKParityGroup.{0,0,0,0} p unitScalarAction unitScalarAction where
  toFun := sourcePullbackHom.{0,0,0,0,0} p (scalarToCZero X) (scalarToCZero_equivariant X)
  invFun := sourcePullbackHom.{0,0,0,0,0} p (cZeroEvaluation X x)
    (cZeroEvaluation_equivariant X x)
  left_inv z := by
    change sourcePullback p (cZeroEvaluation X x) (cZeroEvaluation_equivariant X x)
      (sourcePullback p (scalarToCZero X) (scalarToCZero_equivariant X) z) = z
    rw [sourcePullback_comp]
    have h : (scalarToCZero X).comp (cZeroEvaluation X x) =
        NonUnitalStarAlgHom.id ℂ C₀(X, ℂ) := by
      ext f y
      exact congrArg f (Subsingleton.elim x y)
    exact (unitSourcePullback_congr («α» := CZero.action Unit (X := X))
      («β» := CZero.action Unit (X := X)) (γ := unitScalarAction)
      p _ _ _ (fun _ _ => rfl) h z).trans (sourcePullback_id p z)
  right_inv z := by
    change sourcePullback p (scalarToCZero X) (scalarToCZero_equivariant X)
      (sourcePullback p (cZeroEvaluation X x) (cZeroEvaluation_equivariant X x) z) = z
    rw [sourcePullback_comp]
    have h : (cZeroEvaluation X x).comp (scalarToCZero X) =
        NonUnitalStarAlgHom.id ℂ ℂ := by ext a; rfl
    exact (unitSourcePullback_congr («α» := unitScalarAction)
      («β» := unitScalarAction) (γ := unitScalarAction)
      p _ _ _ (fun _ _ => rfl) h z).trans (sourcePullback_id p z)
  map_add' := (sourcePullbackHom p (scalarToCZero X) (scalarToCZero_equivariant X)).map_add

/-- The crossed point-algebra action and its coefficient scalar map are
concrete trivial Unit actions, as required by the actual native product. -/
abbrev unitPointCrossedAction : CStarAlgebraAction Unit
    (ReducedCrossedProduct (CZero.action Unit (X := X))) := CStarAlgebraAction.trivial

abbrev unitPointCrossedMap : unitScalarCrossedAlgebra →⋆ₙₐ[ℂ]
    ReducedCrossedProduct (CZero.action Unit (X := X)) :=
  reducedCrossedMap unitScalarAction (CZero.action Unit (X := X))
    (scalarToCZero X) (scalarToCZero_equivariant X)

omit [ContinuousConstSMul Unit X] in
/-- The normalized Unit cutoff acts by the actual scalar coefficient source map. -/
private theorem unitCutoffProduct_eq_source (p : Bool) (c : Cutoff.CutoffFunction Unit X)
    (y : KKParityGroup.{0,0,0,0} p (unitPointCrossedAction X)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit unitScalarCrossedAlgebra)) :
    Assembly.cutoffProductHom Unit X p c y =
      sourcePullback.{0,0,0,0,0} (Γ := Unit) (A := ℂ)
        (B := ReducedCrossedProduct (CZero.action Unit (X := X)))
        (C := unitScalarCrossedAlgebra) («α» := unitScalarAction)
        («β» := unitPointCrossedAction X) (γ := CStarAlgebraAction.trivial)
        p (scalarCrossedCoefficient X) (fun _ _ => rfl) y := by
  cases p
  · change GroupUniverseParityUnits.leftEvenProduct.{0,0,0,0,0}
      (Γ := Unit) (A := ℂ) (B := ReducedCrossedProduct (CZero.action Unit (X := X)))
      (C := unitScalarCrossedAlgebra) («α» := unitScalarAction)
      («β» := unitPointCrossedAction X) (γ := CStarAlgebraAction.trivial)
      false (Assembly.cutoffKKClass Unit X c) y = _
    rw [cutoffKKClass_eq_homClass X c]
    rfl
  · change GroupUniverseParityUnits.leftEvenProduct.{0,0,0,0,0}
      (Γ := Unit) (A := ℂ) (B := ReducedCrossedProduct (CZero.action Unit (X := X)))
      (C := unitScalarCrossedAlgebra) («α» := unitScalarAction)
      («β» := unitPointCrossedAction X) (γ := CStarAlgebraAction.trivial)
      true (Assembly.cutoffKKClass Unit X c) y = _
    rw [cutoffKKClass_eq_homClass X c]
    rfl

omit [ContinuousConstSMul Unit X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] in
/-- Actual crossed-product functoriality identifies the scalar point coefficients. -/
private theorem unitPointCrossedMap_coefficient :
    (unitPointCrossedMap X).comp unitScalarInclusion = scalarCrossedCoefficient X := by
  apply DFunLike.ext
  intro a
  exact reducedCrossedMap_coefficient unitScalarAction (CZero.action Unit (X := X))
    (scalarToCZero X) (scalarToCZero_equivariant X) a

omit [ContinuousConstSMul Unit X] in
/-- Actual source naturality and actual coefficient composition, before applying
any parity-specific Unit descent restriction theorem. -/
private theorem unitCutoffSource_descent (p : Bool)
    (x : TopologicalKHomology.spaceGroup p Unit X) :
    sourcePullback.{0,0,0,0,0} (Γ := Unit) (A := ℂ)
      (B := ReducedCrossedProduct (CZero.action Unit (X := X)))
      (C := unitScalarCrossedAlgebra) («α» := unitScalarAction)
      («β» := unitPointCrossedAction X) (γ := CStarAlgebraAction.trivial)
      p (scalarCrossedCoefficient X) (fun _ _ => rfl)
      (KasparovDescent.classHom unitScalarAction (CZero.action Unit (X := X)) p x) =
    sourcePullback.{0,0,0,0,0} (Γ := Unit) (A := ℂ)
      (B := unitScalarCrossedAlgebra) (C := unitScalarCrossedAlgebra)
      («α» := unitScalarAction) («β» := CStarAlgebraAction.trivial)
      (γ := CStarAlgebraAction.trivial) p unitScalarInclusion (fun _ _ => rfl)
      (KasparovDescent.classHom unitScalarAction unitScalarAction p
        (sourcePullback.{0,0,0,0,0} p (scalarToCZero X) (scalarToCZero_equivariant X) x)) := by
  have hn := KasparovDescent.classHom_sourcePullback.{0,0,0,0,0}
    unitScalarAction (CZero.action Unit (X := X)) unitScalarAction p (scalarToCZero X)
      (scalarToCZero_equivariant X) x
  have hc := sourcePullback_comp.{0,0,0,0,0,0}
    (Γ := Unit) (A := ℂ) (B := unitScalarCrossedAlgebra)
    (C := ReducedCrossedProduct (CZero.action Unit (X := X)))
    (D := unitScalarCrossedAlgebra) («α» := unitScalarAction)
    («β» := CStarAlgebraAction.trivial) (γ := unitPointCrossedAction X)
    (η := CStarAlgebraAction.trivial) p unitScalarInclusion (unitPointCrossedMap X)
    (fun _ _ => rfl) (fun _ _ => rfl)
    (KasparovDescent.classHom unitScalarAction (CZero.action Unit (X := X)) p x)
  have he := unitSourcePullback_congr («α» := unitScalarAction)
    («β» := unitPointCrossedAction X)
    (γ := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit unitScalarCrossedAlgebra)) p
    ((unitPointCrossedMap X).comp unitScalarInclusion) (scalarCrossedCoefficient X)
    (fun _ _ => rfl) (fun _ _ => rfl) (unitPointCrossedMap_coefficient X)
    (KasparovDescent.classHom unitScalarAction (CZero.action Unit (X := X)) p x)
  exact (hc.trans he).symm.trans (congrArg
    (sourcePullback.{0,0,0,0,0} (Γ := Unit) (A := ℂ)
      (B := unitScalarCrossedAlgebra) (C := unitScalarCrossedAlgebra)
      («α» := unitScalarAction) («β» := CStarAlgebraAction.trivial)
      (γ := CStarAlgebraAction.trivial) p unitScalarInclusion (fun _ _ => rfl)) hn.symm)

omit [ContinuousConstSMul Unit X] in
/-- Actual source naturality moves the constant point map before actual descent;
its coefficient restriction is then the actual ordinary coefficient extension. -/
theorem cutoffProduct_descent_eq_coefficient (p : Bool) (c : Cutoff.CutoffFunction Unit X)
    (x : TopologicalKHomology.spaceGroup p Unit X) :
    Assembly.cutoffProductHom Unit X p c
      (KasparovDescent.classHom unitScalarAction (CZero.action Unit (X := X)) p x) =
    (by
      cases p
      · exact GroupUniverseOrdinaryEven.coefficientPushforward unitScalarInclusion
          (sourcePullback false (scalarToCZero X) (scalarToCZero_equivariant X) x)
      · exact GroupUniverseOrdinaryOdd.coefficientPushforward unitScalarInclusion
          (sourcePullback true (scalarToCZero X) (scalarToCZero_equivariant X) x) :
      KKParityGroup.{0,0,0,0} p unitScalarAction (CStarAlgebraAction.trivial : CStarAlgebraAction Unit unitScalarCrossedAlgebra)) := by
  have h := (unitCutoffProduct_eq_source X p c
    (KasparovDescent.classHom unitScalarAction (CZero.action Unit (X := X)) p x)).trans
      (unitCutoffSource_descent X p x)
  cases p
  · exact h.trans (UnitScalarDescent.evenClass_coefficientRestriction.{0,0} _)
  · exact h.trans (UnitScalarDescent.oddClass_coefficientRestriction.{0,0} _)

omit [ContinuousConstSMul Unit X] in
/-- The actual point formula is the composite of the actual source equivalence
and actual scalar/analytic comparison; no bijectivity hypothesis is introduced. -/
theorem spaceAssemblyHom_eq_unitPointEquiv [Subsingleton X] (x0 : X) (p : Bool)
    (c : Cutoff.CutoffFunction Unit X) (x : TopologicalKHomology.spaceGroup p Unit X) :
    Assembly.spaceAssemblyHom Unit X p c x =
      ((unitPointSourceEquiv X x0 p).trans (unitScalarAnalyticEquiv p)) x := by
  change Assembly.reducedScalarKKToAnalyticHom Unit p
    (Assembly.cutoffProductHom Unit X p c
      (KasparovDescent.classHom unitScalarAction (CZero.action Unit (X := X)) p x)) = _
  rw [cutoffProduct_descent_eq_coefficient X]
  cases p
  · exact reducedScalarKKToK0Hom_coefficient _
  · exact reducedScalarKKToK1Hom_coefficient _

end CompactPoint

/-- A concrete additive equivalence out of the actual canonical topological
colimit, using only proved finite-model and point-source equivalences. -/
def unitAssemblyAddEquiv (p : Bool) :
    TopologicalKHomology.topologicalGroup p Unit ≃+ Assembly.analyticGroup Unit p :=
  (finiteTopologicalPointSpaceEquiv Unit p).trans
    ((unitPointSourceEquiv FiniteGroupPoint.{0} default p).trans (unitScalarAnalyticEquiv p))

/-- Identification is with Chapter 7's actual canonical assembly map. -/
theorem reducedAssemblyHom_unit_eq (p : Bool)
    (x : TopologicalKHomology.topologicalGroup p Unit) :
    Assembly.reducedAssemblyHom Unit p x = unitAssemblyAddEquiv p x := by
  rw [reducedAssemblyHom_finitePoint]
  exact spaceAssemblyHom_eq_unitPointEquiv FiniteGroupPoint.{0} default p
    (finitePointCutoff Unit) (finiteTopologicalPointSpaceEquiv Unit p x)

/-- The actual coefficient-free reduced Baum–Connes property for the literal
one-element group. The general countable-discrete-group conjecture remains unproved. -/
theorem baumConnesProperty_unit : Assembly.BaumConnesProperty Unit := by
  intro p
  have h : (Assembly.reducedAssemblyHom Unit p :
      TopologicalKHomology.topologicalGroup p Unit → Assembly.analyticGroup Unit p) =
      unitAssemblyAddEquiv p := funext (reducedAssemblyHom_unit_eq p)
  rw [h]
  exact (unitAssemblyAddEquiv p).bijective

end BC4lean.Chapter8Examples
