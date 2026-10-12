import BC4lean.KasparovLocalCompactPerturbation
import BC4lean.ProjectionHilbertModule
import BC4lean.ProjectionHilbertModuleSplit
import BC4lean.KasparovDirectSumIso

/-! # Genuine support block reduction for a scalar Kasparov cycle

A possibly degenerate scalar representation has the actual support projection
p = φ(1). The original compact commutator with p makes the off-support blocks
of F compact. Removing precisely those blocks gives an admissible odd operator
and a genuine affine operator homotopy. The supported operator is constructed
on the actual closed range module of p. No scalar Fredholm normal form is
assumed by these constructions.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {β : CStarAlgebraAction Γ B}

namespace KasparovCycle

variable (c : KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) β E)

/-- The support of the actual, possibly degenerate, scalar representation. -/
def scalarSupportProjection : AdjointableMap B E E := c.representation 1

/-- Complex linearity determines the entire scalar representation from φ(1). -/
theorem representation_eq_smul_scalarSupportProjection (z : ℂ) :
    c.representation z = z • c.scalarSupportProjection := by
  simpa only [scalarSupportProjection, smul_eq_mul, mul_one] using
    map_smul c.representation z (1 : ℂ)

/-- The scalar support is an actual selfadjoint idempotent. -/
theorem scalarSupportProjection_isStarProjection : IsStarProjection c.scalarSupportProjection := by
  apply isStarProjection_iff'.mpr
  constructor
  · change c.representation 1 * c.representation 1 = c.representation 1
    rw [← map_mul]
    simp
  · change star (c.representation 1) = c.representation 1
    rw [← map_star]
    simp

/-- Remove only the two off-support blocks of the original Fredholm operator. -/
def scalarSupportBlockOperator : AdjointableMap B E E :=
  c.scalarSupportProjection * c.operator * c.scalarSupportProjection +
    (1 - c.scalarSupportProjection) * c.operator * (1 - c.scalarSupportProjection)

/-- The removed blocks are expressed entirely through the actual compact
commutator [F,p]. -/
theorem operator_sub_scalarSupportBlockOperator :
    c.operator - c.scalarSupportBlockOperator =
      (c.operator * c.scalarSupportProjection - c.scalarSupportProjection * c.operator) *
          c.scalarSupportProjection -
        c.scalarSupportProjection *
          (c.operator * c.scalarSupportProjection - c.scalarSupportProjection * c.operator) := by
  have hp := c.scalarSupportProjection_isStarProjection.isIdempotentElem.eq
  have hpF : c.scalarSupportProjection * (c.scalarSupportProjection * c.operator) =
      c.scalarSupportProjection * c.operator := by rw [← mul_assoc, hp]
  dsimp only [scalarSupportBlockOperator]
  simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc, hp, hpF]
  abel

/-- The block reduction has a globally compact difference, proved from the
original cycle commutator at the scalar unit. -/
theorem scalarSupportBlockOperator_sub_isModuleCompact :
    IsModuleCompact (c.scalarSupportBlockOperator - c.operator) := by
  have hcomm : IsModuleCompact
      (c.operator * c.scalarSupportProjection - c.scalarSupportProjection * c.operator) :=
    c.commutator_compact 1
  have hh : IsModuleCompact (c.operator - c.scalarSupportBlockOperator) := by
    rw [operator_sub_scalarSupportBlockOperator]
    exact (hcomm.comp_right c.scalarSupportProjection).sub
      (hcomm.comp_left c.scalarSupportProjection)
  simpa only [neg_sub] using hh.neg

/-- The block operator has the required odd degree because its support
projection and complementary projection are even. -/
theorem scalarSupportBlockOperator_isOdd :
    c.grading.IsOdd c.grading c.scalarSupportBlockOperator := by
  have hp : c.grading.IsEven c.grading c.scalarSupportProjection := c.representation_even 1
  have hq : c.grading.IsEven c.grading (1 - c.scalarSupportProjection) := by
    intro x
    simp only [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, map_sub]
    rw [hp x]
  have hSupport := (hp.comp_odd c.operator_odd).comp_even hp
  have hComplement := (hq.comp_odd c.operator_odd).comp_even hq
  intro x
  simp only [scalarSupportBlockOperator, AdjointableMap.coe_add_apply, map_add, neg_add]
  exact congrArg₂ (· + ·) (hSupport x) (hComplement x)

/-- All cycle conditions of the new endpoint derive from its proved compact
difference; endpoint admissibility is not an additional hypothesis. -/
theorem operatorConditions_scalarSupportBlockOperator :
    c.OperatorConditions c.scalarSupportBlockOperator := by
  have hδ := c.scalarSupportBlockOperator_sub_isModuleCompact
  have hodd : c.grading.IsOdd c.grading (c.scalarSupportBlockOperator - c.operator) := by
    intro x
    simp only [AdjointableMap.coe_sub_apply, map_sub]
    rw [c.scalarSupportBlockOperator_isOdd x, c.operator_odd x]
    abel
  have hh := c.operatorConditions_add_locallyCompact
    (c.scalarSupportBlockOperator - c.operator) hodd
    (fun z => hδ.comp_right (c.representation z))
    (fun z => hδ.adjoint.comp_right (c.representation z))
  have heq : c.operator + (c.scalarSupportBlockOperator - c.operator) =
      c.scalarSupportBlockOperator := by abel
  rwa [heq] at hh

/-- The actual scalar cycle with its support-block operator. -/
def scalarSupportBlockCycle :
    KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) β E :=
  c.withOperator c.scalarSupportBlockOperator c.operatorConditions_scalarSupportBlockOperator

/-- The verified affine path removes the compact off-support blocks. -/
def scalarSupportBlockHomotopy :
    KasparovOperatorHomotopy c c.operator c.scalarSupportBlockOperator :=
  KasparovOperatorHomotopy.compactPerturbation c c.scalarSupportBlockOperator
    c.operatorConditions_scalarSupportBlockOperator
    (fun z => c.scalarSupportBlockOperator_sub_isModuleCompact.comp_right (c.representation z))

/-- The support block obtained by right multiplication. -/
theorem scalarSupportBlockOperator_mul_support :
    c.scalarSupportBlockOperator * c.scalarSupportProjection =
      c.scalarSupportProjection * c.operator * c.scalarSupportProjection := by
  have hp := c.scalarSupportProjection_isStarProjection.isIdempotentElem.eq
  have hqp : (1 - c.scalarSupportProjection) * c.scalarSupportProjection = 0 := by
    rw [sub_mul, one_mul, hp, sub_self]
  simp only [scalarSupportBlockOperator, add_mul, mul_assoc, hp, hqp, mul_zero, add_zero]

/-- The same support block obtained by left multiplication. -/
theorem support_mul_scalarSupportBlockOperator :
    c.scalarSupportProjection * c.scalarSupportBlockOperator =
      c.scalarSupportProjection * c.operator * c.scalarSupportProjection := by
  have hp := c.scalarSupportProjection_isStarProjection.isIdempotentElem.eq
  have hpq : c.scalarSupportProjection * (1 - c.scalarSupportProjection) = 0 := by
    rw [mul_sub, mul_one, hp, sub_self]
  simp only [scalarSupportBlockOperator, mul_add, ← mul_assoc, hp, hpq, zero_mul, add_zero]

/-- The block endpoint commutes exactly with its scalar support. -/
theorem scalarSupportBlockOperator_commutes_support :
    c.scalarSupportBlockOperator * c.scalarSupportProjection =
      c.scalarSupportProjection * c.scalarSupportBlockOperator := by
  rw [scalarSupportBlockOperator_mul_support, support_mul_scalarSupportBlockOperator]

/-- The support-block operator restricts to the actual complete support range. -/
def scalarSupportCompression :
    AdjointableMap B (ProjectionModule c.scalarSupportProjection)
      (ProjectionModule c.scalarSupportProjection) :=
  ((projectionCorestrict c.scalarSupportProjection c.scalarSupportProjection_isStarProjection).comp
    c.scalarSupportBlockOperator).comp
      (projectionInclusion c.scalarSupportProjection c.scalarSupportProjection_isStarProjection)

/-- Inclusion of the constructed compression gives precisely the original
support-block action, with range preservation proved by commutation. -/
@[simp] theorem scalarSupportCompression_coe (x : ProjectionModule c.scalarSupportProjection) :
    (c.scalarSupportCompression x : E) = c.scalarSupportBlockOperator (x : E) := by
  change c.scalarSupportProjection (c.scalarSupportBlockOperator (x : E)) =
    c.scalarSupportBlockOperator (x : E)
  have hh := congrArg (fun T : AdjointableMap B E E => T (x : E))
    c.scalarSupportBlockOperator_commutes_support
  change c.scalarSupportBlockOperator (c.scalarSupportProjection (x : E)) =
    c.scalarSupportProjection (c.scalarSupportBlockOperator (x : E)) at hh
  rw [x.property] at hh
  exact hh.symm

/-- The genuinely constructed support range is countably generated. -/
theorem scalarSupportModule_isCountablyGenerated :
    IsCountablyGeneratedModule B (ProjectionModule c.scalarSupportProjection) :=
  projectionModule_isCountablyGenerated c.scalarSupportProjection
    c.scalarSupportProjection_isStarProjection c.countablyGenerated

/-- Evenness of the actual scalar support makes the original grading preserve
its genuine closed range module. -/
theorem scalarSupportProjection_grading_fixed (x : ProjectionModule c.scalarSupportProjection) :
    c.scalarSupportProjection (c.grading.grading (x : E)) = c.grading.grading (x : E) := by
  have hEven := c.representation_even 1 (x : E)
  change c.grading.grading (c.scalarSupportProjection (x : E)) =
    c.scalarSupportProjection (c.grading.grading (x : E)) at hEven
  rw [x.property] at hEven
  exact hEven.symm

/-- The actual grading restricted to the complete scalar support module. -/
def scalarSupportGrading :
    GradedHilbertModule (CStarGrading.trivial : CStarGrading B)
      (ProjectionModule c.scalarSupportProjection) where
  grading :=
    { toLinearEquiv :=
        { toFun := fun x => ⟨c.grading.grading (x : E), c.scalarSupportProjection_grading_fixed x⟩
          invFun := fun x => ⟨c.grading.grading (x : E), c.scalarSupportProjection_grading_fixed x⟩
          left_inv := fun x => Subtype.ext (c.grading.involutive (x : E))
          right_inv := fun x => Subtype.ext (c.grading.involutive (x : E))
          map_add' := fun x y => Subtype.ext (c.grading.grading.map_add (x : E) (y : E))
          map_smul' := fun z x => Subtype.ext (c.grading.grading.map_smul z (x : E)) }
      norm_map' x := c.grading.grading.norm_map (x : E) }
  involutive x := Subtype.ext (c.grading.involutive (x : E))
  inner_grading x y := c.grading.inner_grading (x : E) (y : E)

@[simp] theorem scalarSupportGrading_coe (x : ProjectionModule c.scalarSupportProjection) :
    (c.scalarSupportGrading.grading x : E) = c.grading.grading (x : E) := rfl

/-- The genuinely restricted compression has the original odd degree. -/
theorem scalarSupportCompression_isOdd :
    c.scalarSupportGrading.IsOdd c.scalarSupportGrading c.scalarSupportCompression := by
  intro x
  apply Subtype.ext
  simpa only [Submodule.coe_neg, c.scalarSupportGrading_coe, c.scalarSupportCompression_coe] using
    c.scalarSupportBlockOperator_isOdd (x : E)

/-- The adjoint of the actual support compression is the compression of the
adjoint ambient block operator. -/
theorem scalarSupportCompression_star :
    star c.scalarSupportCompression =
      ((projectionCorestrict c.scalarSupportProjection c.scalarSupportProjection_isStarProjection).comp
        (star c.scalarSupportBlockOperator)).comp
          (projectionInclusion c.scalarSupportProjection c.scalarSupportProjection_isStarProjection) := by
  ext x
  rfl

/-- The selfadjoint defect is globally compact on the actual support module.
It is extracted from the original cycle condition at the scalar unit. -/
theorem scalarSupportCompression_selfadjoint_mod_compact :
    IsModuleCompact (c.scalarSupportCompression - star c.scalarSupportCompression) := by
  have hAmbient := c.operatorConditions_scalarSupportBlockOperator.selfadjoint_mod_compact 1
  have hCompact := (hAmbient.comp_left
    (projectionCorestrict c.scalarSupportProjection c.scalarSupportProjection_isStarProjection)).comp_right
      (projectionInclusion c.scalarSupportProjection c.scalarSupportProjection_isStarProjection)
  have hEq :
      ((projectionCorestrict c.scalarSupportProjection c.scalarSupportProjection_isStarProjection).comp
        ((c.scalarSupportBlockOperator - star c.scalarSupportBlockOperator) * c.representation 1)).comp
          (projectionInclusion c.scalarSupportProjection c.scalarSupportProjection_isStarProjection) =
      c.scalarSupportCompression - star c.scalarSupportCompression := by
    rw [c.scalarSupportCompression_star]
    ext x
    change c.scalarSupportProjection
        ((c.scalarSupportBlockOperator - star c.scalarSupportBlockOperator)
          (c.scalarSupportProjection (x : E))) =
      ((c.scalarSupportCompression -
        ((projectionCorestrict c.scalarSupportProjection c.scalarSupportProjection_isStarProjection).comp
          (star c.scalarSupportBlockOperator)).comp
            (projectionInclusion c.scalarSupportProjection c.scalarSupportProjection_isStarProjection)) x : E)
    simp only [AdjointableMap.coe_sub_apply, Submodule.coe_sub]
    change c.scalarSupportProjection
        (c.scalarSupportBlockOperator (c.scalarSupportProjection (x : E)) -
          star c.scalarSupportBlockOperator (c.scalarSupportProjection (x : E))) =
      c.scalarSupportProjection (c.scalarSupportBlockOperator (x : E)) -
        c.scalarSupportProjection (star c.scalarSupportBlockOperator (x : E))
    rw [x.property, c.scalarSupportProjection.toCLM.map_sub]
  rwa [hEq] at hCompact

/-- The square defect is globally compact on the actual support module.
Range preservation was proved from the support commutator before this step. -/
theorem scalarSupportCompression_square_mod_compact :
    IsModuleCompact (c.scalarSupportCompression * c.scalarSupportCompression - 1) := by
  have hAmbient := c.operatorConditions_scalarSupportBlockOperator.square_mod_compact 1
  have hCompact := (hAmbient.comp_left
    (projectionCorestrict c.scalarSupportProjection c.scalarSupportProjection_isStarProjection)).comp_right
      (projectionInclusion c.scalarSupportProjection c.scalarSupportProjection_isStarProjection)
  have hEq :
      ((projectionCorestrict c.scalarSupportProjection c.scalarSupportProjection_isStarProjection).comp
        ((c.scalarSupportBlockOperator * c.scalarSupportBlockOperator - 1) * c.representation 1)).comp
          (projectionInclusion c.scalarSupportProjection c.scalarSupportProjection_isStarProjection) =
      c.scalarSupportCompression * c.scalarSupportCompression - 1 := by
    ext x
    have hFixed : c.scalarSupportProjection
        (c.scalarSupportBlockOperator (c.scalarSupportBlockOperator (x : E))) =
        c.scalarSupportBlockOperator (c.scalarSupportBlockOperator (x : E)) := by
      have hh := (c.scalarSupportCompression (c.scalarSupportCompression x)).property
      change c.scalarSupportProjection
          (c.scalarSupportCompression (c.scalarSupportCompression x) : E) =
        (c.scalarSupportCompression (c.scalarSupportCompression x) : E) at hh
      simpa only [c.scalarSupportCompression_coe] using hh
    have hx : c.scalarSupportProjection (x : E) = (x : E) := x.property
    change c.scalarSupportProjection
        ((c.scalarSupportBlockOperator * c.scalarSupportBlockOperator - 1)
          (c.scalarSupportProjection (x : E))) =
      ((c.scalarSupportCompression * c.scalarSupportCompression - 1) x : E)
    simp only [hx, AdjointableMap.coe_sub_apply, Submodule.coe_sub, AdjointableMap.mul_apply,
      AdjointableMap.one_apply, c.scalarSupportProjection.toCLM.map_sub,
      c.scalarSupportCompression_coe, hFixed]
  rwa [hEq] at hCompact

/-- Exact representation equivariance at the scalar unit makes the actual
support commute with every original group action. -/
theorem scalarSupportProjection_action (g : Γ) (x : E) :
    c.scalarSupportProjection (c.groupAction.action g x) =
      c.groupAction.action g (c.scalarSupportProjection x) := by
  have hh := congrArg (fun T : AdjointableMap B E E => T (c.groupAction.action g x))
    (c.representation_equivariant g 1)
  change c.groupAction.action g
      (c.scalarSupportProjection (c.groupAction.action g⁻¹ (c.groupAction.action g x))) =
    c.scalarSupportProjection (c.groupAction.action g x) at hh
  rw [c.groupAction.inv_apply_apply] at hh
  exact hh.symm

/-- Each original group action restricts to the actual scalar support range. -/
def scalarSupportAction (g : Γ) :
    ProjectionModule c.scalarSupportProjection ≃ₗᵢ[ℂ] ProjectionModule c.scalarSupportProjection where
  toLinearEquiv :=
    { toFun := fun x => ⟨c.groupAction.action g (x : E), by
        change c.scalarSupportProjection (c.groupAction.action g (x : E)) =
          c.groupAction.action g (x : E)
        rw [c.scalarSupportProjection_action, x.property]⟩
      invFun := fun x => ⟨c.groupAction.action g⁻¹ (x : E), by
        change c.scalarSupportProjection (c.groupAction.action g⁻¹ (x : E)) =
          c.groupAction.action g⁻¹ (x : E)
        rw [c.scalarSupportProjection_action, x.property]⟩
      left_inv := fun x => Subtype.ext (c.groupAction.inv_apply_apply g (x : E))
      right_inv := fun x => Subtype.ext (c.groupAction.apply_inv_apply g (x : E))
      map_add' := fun x y => Subtype.ext ((c.groupAction.action g).map_add (x : E) (y : E))
      map_smul' := fun z x => Subtype.ext ((c.groupAction.action g).map_smul z (x : E)) }
  norm_map' x := (c.groupAction.action g).norm_map (x : E)

@[simp] theorem scalarSupportAction_coe (g : Γ) (x : ProjectionModule c.scalarSupportProjection) :
    (c.scalarSupportAction g x : E) = c.groupAction.action g (x : E) := rfl

/-- The full original compatible group action restricted to the support. -/
def scalarSupportGroupAction : EquivariantHilbertModule β (ProjectionModule c.scalarSupportProjection) where
  action :=
    { toFun := c.scalarSupportAction
      map_one' := by
        ext x
        change c.groupAction.action 1 (x : E) = (x : E)
        exact c.groupAction.one_apply (x : E)
      map_mul' := fun g h => by
        ext x
        change c.groupAction.action (g * h) (x : E) =
          c.groupAction.action g (c.groupAction.action h (x : E))
        exact c.groupAction.mul_apply g h (x : E) }
  inner_action g x y := c.groupAction.inner_action g (x : E) (y : E)

@[simp] theorem scalarSupportGroupAction_coe (g : Γ)
    (x : ProjectionModule c.scalarSupportProjection) :
    (c.scalarSupportGroupAction.action g x : E) = c.groupAction.action g (x : E) := rfl

theorem scalarSupportGroupAction_preservesGrading :
    c.scalarSupportGroupAction.PreservesGrading c.scalarSupportGrading := by
  intro g x
  apply Subtype.ext
  exact c.grading_preserved g (x : E)

@[simp] theorem scalarSupportCompression_conjugate_coe (g : Γ)
    (x : ProjectionModule c.scalarSupportProjection) :
    (c.scalarSupportGroupAction.conjugateOperator g c.scalarSupportCompression x : E) =
      c.groupAction.conjugateOperator g c.scalarSupportBlockOperator (x : E) := by
  simp only [EquivariantHilbertModule.conjugateMap_apply, c.scalarSupportGroupAction_coe,
    c.scalarSupportCompression_coe]

/-- Equivariance modulo compact operators is globally inherited on the actual
support module by its adjointable inclusion and projection. -/
theorem scalarSupportCompression_equivariance_mod_compact (g : Γ) :
    IsModuleCompact (c.scalarSupportGroupAction.conjugateOperator g c.scalarSupportCompression -
      c.scalarSupportCompression) := by
  have hAmbient := c.operatorConditions_scalarSupportBlockOperator.equivariance_mod_compact g 1
  have hCompact := (hAmbient.comp_left
    (projectionCorestrict c.scalarSupportProjection c.scalarSupportProjection_isStarProjection)).comp_right
      (projectionInclusion c.scalarSupportProjection c.scalarSupportProjection_isStarProjection)
  have hEq :
      ((projectionCorestrict c.scalarSupportProjection c.scalarSupportProjection_isStarProjection).comp
        ((c.groupAction.conjugateOperator g c.scalarSupportBlockOperator - c.scalarSupportBlockOperator) *
          c.representation 1)).comp
          (projectionInclusion c.scalarSupportProjection c.scalarSupportProjection_isStarProjection) =
      c.scalarSupportGroupAction.conjugateOperator g c.scalarSupportCompression - c.scalarSupportCompression := by
    ext x
    have hFixedConjugate : c.scalarSupportProjection
        (c.groupAction.conjugateOperator g c.scalarSupportBlockOperator (x : E)) =
        c.groupAction.conjugateOperator g c.scalarSupportBlockOperator (x : E) := by
      have hh :=
        (c.scalarSupportGroupAction.conjugateOperator g c.scalarSupportCompression x).property
      change c.scalarSupportProjection
          (c.scalarSupportGroupAction.conjugateOperator g c.scalarSupportCompression x : E) =
        (c.scalarSupportGroupAction.conjugateOperator g c.scalarSupportCompression x : E) at hh
      simpa only [c.scalarSupportCompression_conjugate_coe] using hh
    have hFixedOperator : c.scalarSupportProjection (c.scalarSupportBlockOperator (x : E)) =
        c.scalarSupportBlockOperator (x : E) := by
      have hh := (c.scalarSupportCompression x).property
      change c.scalarSupportProjection (c.scalarSupportCompression x : E) =
        (c.scalarSupportCompression x : E) at hh
      simpa only [c.scalarSupportCompression_coe] using hh
    have hx : c.scalarSupportProjection (x : E) = (x : E) := x.property
    change c.scalarSupportProjection
        ((c.groupAction.conjugateOperator g c.scalarSupportBlockOperator - c.scalarSupportBlockOperator)
          (c.scalarSupportProjection (x : E))) =
      ((c.scalarSupportGroupAction.conjugateOperator g c.scalarSupportCompression -
        c.scalarSupportCompression) x : E)
    simp only [hx, AdjointableMap.coe_sub_apply, Submodule.coe_sub,
      c.scalarSupportProjection.toCLM.map_sub,
      c.scalarSupportCompression_conjugate_coe, c.scalarSupportCompression_coe,
      hFixedConjugate, hFixedOperator]
  rwa [hEq] at hCompact

/-- The unital scalar representation on the genuinely restricted support. -/
def scalarSupportRepresentation : ℂ →⋆ₙₐ[ℂ]
    AdjointableMap B (ProjectionModule c.scalarSupportProjection) (ProjectionModule c.scalarSupportProjection) :=
  (StarAlgHom.ofId ℂ (AdjointableMap B (ProjectionModule c.scalarSupportProjection)
    (ProjectionModule c.scalarSupportProjection))).toNonUnitalStarAlgHom

@[simp] theorem scalarSupportRepresentation_apply (z : ℂ) (x : ProjectionModule c.scalarSupportProjection) :
    c.scalarSupportRepresentation z x = z • x := by
  change (algebraMap ℂ (AdjointableMap B (ProjectionModule c.scalarSupportProjection)
    (ProjectionModule c.scalarSupportProjection)) z) x = z • x
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

/-- The actual scalar support cycle, with all admissibility conditions derived
from the original cycle rather than supplied as endpoint assumptions. -/
def scalarSupportCycle :
    KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) β
      (ProjectionModule c.scalarSupportProjection) where
  countablyGenerated := c.scalarSupportModule_isCountablyGenerated
  grading := c.scalarSupportGrading
  groupAction := c.scalarSupportGroupAction
  grading_preserved := c.scalarSupportGroupAction_preservesGrading
  representation := c.scalarSupportRepresentation
  representation_even z x := c.scalarSupportGrading.grading.map_smul z x
  representation_equivariant g z := by
    ext x
    simp only [EquivariantHilbertModule.conjugateMap_apply, c.scalarSupportRepresentation_apply,
      map_smul, EquivariantHilbertModule.apply_inv_apply]
    rfl
  operator := c.scalarSupportCompression
  operator_odd := c.scalarSupportCompression_isOdd
  selfadjoint_mod_compact z := c.scalarSupportCompression_selfadjoint_mod_compact.comp_right
    (c.scalarSupportRepresentation z)
  square_mod_compact z := c.scalarSupportCompression_square_mod_compact.comp_right
    (c.scalarSupportRepresentation z)
  commutator_compact z := by
    have hZero : c.scalarSupportCompression * c.scalarSupportRepresentation z -
        c.scalarSupportRepresentation z * c.scalarSupportCompression = 0 := by
      ext x
      simp only [AdjointableMap.coe_sub_apply, AdjointableMap.mul_apply,
        c.scalarSupportRepresentation_apply]
      exact sub_eq_zero.mpr (congrArg
        (fun y : ProjectionModule c.scalarSupportProjection => (y : E))
        (c.scalarSupportCompression.toCLM.map_smul z x))
    rw [hZero]
    exact IsModuleCompact.zero
  equivariance_mod_compact g z := (c.scalarSupportCompression_equivariance_mod_compact g).comp_right
    (c.scalarSupportRepresentation z)

/-- The original grading preserves the actual complementary support module. -/
theorem scalarComplementProjection_grading_fixed
    (x : ProjectionModule (1 - c.scalarSupportProjection)) :
    (1 - c.scalarSupportProjection) (c.grading.grading (x : E)) = c.grading.grading (x : E) := by
  have hEven := c.representation_even 1 (x : E)
  have hFixed := congrArg c.grading.grading x.property
  change c.grading.grading (c.scalarSupportProjection (x : E)) =
    c.scalarSupportProjection (c.grading.grading (x : E)) at hEven
  rw [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply] at hFixed ⊢
  rwa [map_sub, hEven] at hFixed

/-- The genuinely restricted complementary grading. -/
def scalarComplementGrading :
    GradedHilbertModule (CStarGrading.trivial : CStarGrading B)
      (ProjectionModule (1 - c.scalarSupportProjection)) where
  grading :=
    { toLinearEquiv :=
        { toFun := fun x => ⟨c.grading.grading (x : E), c.scalarComplementProjection_grading_fixed x⟩
          invFun := fun x => ⟨c.grading.grading (x : E), c.scalarComplementProjection_grading_fixed x⟩
          left_inv := fun x => Subtype.ext (c.grading.involutive (x : E))
          right_inv := fun x => Subtype.ext (c.grading.involutive (x : E))
          map_add' := fun x y => Subtype.ext (c.grading.grading.map_add (x : E) (y : E))
          map_smul' := fun z x => Subtype.ext (c.grading.grading.map_smul z (x : E)) }
      norm_map' x := c.grading.grading.norm_map (x : E) }
  involutive x := Subtype.ext (c.grading.involutive (x : E))
  inner_grading x y := c.grading.inner_grading (x : E) (y : E)

@[simp] theorem scalarComplementGrading_coe (x : ProjectionModule (1 - c.scalarSupportProjection)) :
    (c.scalarComplementGrading.grading x : E) = c.grading.grading (x : E) := rfl

theorem scalarComplementProjection_action_fixed (g : Γ)
    (x : ProjectionModule (1 - c.scalarSupportProjection)) :
    (1 - c.scalarSupportProjection) (c.groupAction.action g (x : E)) = c.groupAction.action g (x : E) := by
  have hFixed := congrArg (c.groupAction.action g) x.property
  rw [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply] at hFixed ⊢
  rwa [map_sub, ← c.scalarSupportProjection_action] at hFixed

def scalarComplementAction (g : Γ) :
    ProjectionModule (1 - c.scalarSupportProjection) ≃ₗᵢ[ℂ]
      ProjectionModule (1 - c.scalarSupportProjection) where
  toLinearEquiv :=
    { toFun := fun x => ⟨c.groupAction.action g (x : E), c.scalarComplementProjection_action_fixed g x⟩
      invFun := fun x => ⟨c.groupAction.action g⁻¹ (x : E), c.scalarComplementProjection_action_fixed g⁻¹ x⟩
      left_inv := fun x => Subtype.ext (c.groupAction.inv_apply_apply g (x : E))
      right_inv := fun x => Subtype.ext (c.groupAction.apply_inv_apply g (x : E))
      map_add' := fun x y => Subtype.ext ((c.groupAction.action g).map_add (x : E) (y : E))
      map_smul' := fun z x => Subtype.ext ((c.groupAction.action g).map_smul z (x : E)) }
  norm_map' x := (c.groupAction.action g).norm_map (x : E)

@[simp] theorem scalarComplementAction_coe (g : Γ)
    (x : ProjectionModule (1 - c.scalarSupportProjection)) :
    (c.scalarComplementAction g x : E) = c.groupAction.action g (x : E) := rfl

def scalarComplementGroupAction :
    EquivariantHilbertModule β (ProjectionModule (1 - c.scalarSupportProjection)) where
  action :=
    { toFun := c.scalarComplementAction
      map_one' := by
        ext x
        change c.groupAction.action 1 (x : E) = (x : E)
        exact c.groupAction.one_apply (x : E)
      map_mul' := fun g h => by
        ext x
        change c.groupAction.action (g * h) (x : E) =
          c.groupAction.action g (c.groupAction.action h (x : E))
        exact c.groupAction.mul_apply g h (x : E) }
  inner_action g x y := c.groupAction.inner_action g (x : E) (y : E)

@[simp] theorem scalarComplementGroupAction_coe (g : Γ)
    (x : ProjectionModule (1 - c.scalarSupportProjection)) :
    (c.scalarComplementGroupAction.action g x : E) = c.groupAction.action g (x : E) := rfl

theorem scalarComplementGroupAction_preservesGrading :
    c.scalarComplementGroupAction.PreservesGrading c.scalarComplementGrading := by
  intro g x
  apply Subtype.ext
  exact c.grading_preserved g (x : E)

/-- The actual complementary block, where the scalar representation vanishes. -/
def scalarComplementCompression :
    AdjointableMap B (ProjectionModule (1 - c.scalarSupportProjection))
      (ProjectionModule (1 - c.scalarSupportProjection)) :=
  ((projectionCorestrict (1 - c.scalarSupportProjection) c.scalarSupportProjection_isStarProjection.one_sub).comp
    c.scalarSupportBlockOperator).comp
      (projectionInclusion (1 - c.scalarSupportProjection) c.scalarSupportProjection_isStarProjection.one_sub)

@[simp] theorem scalarComplementCompression_coe
    (x : ProjectionModule (1 - c.scalarSupportProjection)) :
    (c.scalarComplementCompression x : E) = c.scalarSupportBlockOperator (x : E) := by
  have hCommute : c.scalarSupportBlockOperator * (1 - c.scalarSupportProjection) =
      (1 - c.scalarSupportProjection) * c.scalarSupportBlockOperator := by
    simp only [mul_sub, sub_mul, mul_one, one_mul]
    rw [c.scalarSupportBlockOperator_commutes_support]
  have hh := congrArg (fun T : AdjointableMap B E E => T (x : E)) hCommute
  change c.scalarSupportBlockOperator ((1 - c.scalarSupportProjection) (x : E)) =
    (1 - c.scalarSupportProjection) (c.scalarSupportBlockOperator (x : E)) at hh
  rw [x.property] at hh
  exact hh.symm

theorem scalarComplementCompression_isOdd :
    c.scalarComplementGrading.IsOdd c.scalarComplementGrading c.scalarComplementCompression := by
  intro x
  apply Subtype.ext
  simpa only [Submodule.coe_neg, c.scalarComplementGrading_coe, c.scalarComplementCompression_coe] using
    c.scalarSupportBlockOperator_isOdd (x : E)

/-- The zero-support cycle has the actual complementary operator, and its
zero representation makes every cycle defect exactly vanish. -/
def scalarComplementCycle :
    KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) β
      (ProjectionModule (1 - c.scalarSupportProjection)) where
  countablyGenerated := projectionModule_isCountablyGenerated (1 - c.scalarSupportProjection)
    c.scalarSupportProjection_isStarProjection.one_sub c.countablyGenerated
  grading := c.scalarComplementGrading
  groupAction := c.scalarComplementGroupAction
  grading_preserved := c.scalarComplementGroupAction_preservesGrading
  representation := 0
  representation_even := by intro z x; simp
  representation_equivariant := by intro g z; exact c.scalarComplementGroupAction.conjugateOperator_zero g
  operator := c.scalarComplementCompression
  operator_odd := c.scalarComplementCompression_isOdd
  selfadjoint_mod_compact := by intro z; simpa using IsModuleCompact.zero (B := B)
  square_mod_compact := by intro z; simpa using IsModuleCompact.zero (B := B)
  commutator_compact := by intro z; simpa using IsModuleCompact.zero (B := B)
  equivariance_mod_compact := by intro g z; simpa using IsModuleCompact.zero (B := B)

theorem scalarComplementCycle_isDegenerate : c.scalarComplementCycle.IsDegenerate := by
  constructor
  · intro z; simp [scalarComplementCycle]
  constructor
  · intro z; simp [scalarComplementCycle]
  constructor
  · intro z; simp [scalarComplementCycle]
  · intro g z; simp [scalarComplementCycle]

/-- The same genuine orthogonal decomposition intertwines all cycle data:
the unital scalar support cycle and an exactly degenerate complementary cycle
give precisely the compactly perturbed block endpoint on the original module. -/
def scalarSupportDirectSumIso :
    KasparovCycleIso (c.scalarSupportCycle.directSum c.scalarComplementCycle) c.scalarSupportBlockCycle where
  moduleEquiv := (projectionModuleSplitEquiv c.scalarSupportProjection
    c.scalarSupportProjection_isStarProjection).symm
  grading_intertwine x := by
    change (c.scalarSupportGrading.grading x.fst : E) +
        (c.scalarComplementGrading.grading x.snd : E) =
      c.grading.grading ((x.fst : E) + (x.snd : E))
    rw [c.scalarSupportGrading_coe, c.scalarComplementGrading_coe, map_add]
  action_intertwine g x := by
    change (c.scalarSupportGroupAction.action g x.fst : E) +
        (c.scalarComplementGroupAction.action g x.snd : E) =
      c.groupAction.action g ((x.fst : E) + (x.snd : E))
    rw [c.scalarSupportGroupAction_coe, c.scalarComplementGroupAction_coe, map_add]
  representation_intertwine z x := by
    change (projectionModuleSplitEquiv c.scalarSupportProjection
        c.scalarSupportProjection_isStarProjection).symm
      (sumMap (c.scalarSupportRepresentation z)
        (0 : AdjointableMap B (ProjectionModule (1 - c.scalarSupportProjection))
          (ProjectionModule (1 - c.scalarSupportProjection))) x) =
      c.representation z ((projectionModuleSplitEquiv c.scalarSupportProjection
        c.scalarSupportProjection_isStarProjection).symm x)
    rw [sumMap_apply, projectionModuleSplitEquiv_symm_apply, projectionModuleSplitEquiv_symm_apply]
    simp only [sumMk_fst, sumMk_snd, c.scalarSupportRepresentation_apply,
      AdjointableMap.coe_zero_apply, Submodule.coe_smul, Submodule.coe_zero]
    rw [c.representation_eq_smul_scalarSupportProjection, AdjointableMap.coe_smul_apply,
      c.scalarSupportProjection.toCLM.map_add, x.fst.property,
      projection_complement_fixed_eq_zero, add_zero]
    rw [add_zero]
  operator_intertwine x := by
    change (projectionModuleSplitEquiv c.scalarSupportProjection
        c.scalarSupportProjection_isStarProjection).symm
      (sumMap c.scalarSupportCompression c.scalarComplementCompression x) =
      c.scalarSupportBlockOperator ((projectionModuleSplitEquiv c.scalarSupportProjection
        c.scalarSupportProjection_isStarProjection).symm x)
    rw [sumMap_apply, projectionModuleSplitEquiv_symm_apply, projectionModuleSplitEquiv_symm_apply]
    simp only [sumMk_fst, sumMk_snd]
    rw [c.scalarSupportCompression_coe, c.scalarComplementCompression_coe,
      c.scalarSupportBlockOperator.toCLM.map_add]

end KasparovCycle
end BC4lean.KKTheory
