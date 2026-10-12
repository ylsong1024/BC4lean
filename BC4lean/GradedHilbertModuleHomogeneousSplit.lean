import BC4lean.ProjectionHilbertModuleSplit
import BC4lean.GradedHilbertModule
import BC4lean.KasparovDirectSum
import BC4lean.KasparovInverseRotation

/-! # Genuine homogeneous modules and rectangular odd operators

The two modules are the actual complete ranges of the grading projections.
The coefficient-inner-product projection decomposition supplies their actual
grading-preserving unitary. Odd operators restrict through genuine adjointable
inclusions and projections. A selfadjoint odd operator with compact global
square defect yields a rectangular operator with both genuine compact defects.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

namespace GradedHilbertModule

variable (γ : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E)

/-- The actual even grading projection. -/
def evenProjection : AdjointableMap B E E := (2 : ℂ)⁻¹ • (1 + γ.toAdjointable)

omit [StarOrderedRing B] in
@[simp] theorem evenProjection_apply (x : E) : γ.evenProjection x = γ.evenPart x := rfl

omit [StarOrderedRing B] in
theorem evenProjection_isStarProjection : IsStarProjection γ.evenProjection := by
  apply isStarProjection_iff'.mpr
  constructor
  · ext x
    change (2 : ℂ)⁻¹ • (γ.evenPart x + γ.grading (γ.evenPart x)) = γ.evenPart x
    rw [γ.grading_evenPart, ← two_smul ℂ, smul_smul,
      inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]
  · change star ((2 : ℂ)⁻¹ • (1 + γ.toAdjointable)) = (2 : ℂ)⁻¹ • (1 + γ.toAdjointable)
    simp only [star_smul, star_add, star_one, AdjointableMap.star_eq_adjoint, γ.toAdjointable_adjoint]
    congr 1
    norm_num

/-- The actual complementary odd grading projection. -/
def oddProjection : AdjointableMap B E E := 1 - γ.evenProjection

omit [StarOrderedRing B] in
theorem oddProjection_isStarProjection : IsStarProjection γ.oddProjection :=
  γ.evenProjection_isStarProjection.one_sub

omit [StarOrderedRing B] in
@[simp] theorem oddProjection_apply (x : E) : γ.oddProjection x = γ.oddPart x := by
  rw [oddProjection, AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, evenProjection_apply]
  calc
    x - γ.evenPart x = (γ.evenPart x + γ.oddPart x) - γ.evenPart x :=
      congrArg (fun z => z - γ.evenPart x) (γ.evenPart_add_oddPart x).symm
    _ = γ.oddPart x := by abel

/-- The genuine homogeneous coefficient modules, with inherited actual norms. -/
abbrev EvenModule := ProjectionModule γ.evenProjection
abbrev OddModule := ProjectionModule γ.oddProjection

omit [StarOrderedRing B] in
@[simp] theorem grading_evenModule (x : γ.EvenModule) : γ.grading (x : E) = (x : E) := by
  calc
    γ.grading (x : E) = γ.grading (γ.evenProjection (x : E)) := by rw [x.property]
    _ = γ.evenProjection (x : E) := γ.grading_evenPart (x : E)
    _ = (x : E) := x.property

omit [StarOrderedRing B] in
@[simp] theorem grading_oddModule (x : γ.OddModule) : γ.grading (x : E) = -(x : E) := by
  calc
    γ.grading (x : E) = γ.grading (γ.oddProjection (x : E)) := by rw [x.property]
    _ = -γ.oddProjection (x : E) := by rw [oddProjection_apply, γ.grading_oddPart]
    _ = -(x : E) := congrArg Neg.neg x.property

omit [StarOrderedRing B] in
theorem evenProjection_eq_self_of_grading_fixed {x : E} (hx : γ.grading x = x) :
    γ.evenProjection x = x := by
  rw [evenProjection_apply, evenPart, hx, ← two_smul ℂ, smul_smul,
    inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]

omit [StarOrderedRing B] in
theorem oddProjection_eq_self_of_grading_neg {x : E} (hx : γ.grading x = -x) :
    γ.oddProjection x = x := by
  rw [oddProjection_apply, oddPart, hx, sub_neg_eq_add, ← two_smul ℂ, smul_smul,
    inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]

omit [StarOrderedRing B] in
theorem evenModule_isCountablyGenerated (hE : IsCountablyGeneratedModule B E) :
    IsCountablyGeneratedModule B γ.EvenModule :=
  projectionModule_isCountablyGenerated γ.evenProjection γ.evenProjection_isStarProjection hE

omit [StarOrderedRing B] in
theorem oddModule_isCountablyGenerated (hE : IsCountablyGeneratedModule B E) :
    IsCountablyGeneratedModule B γ.OddModule :=
  projectionModule_isCountablyGenerated γ.oddProjection γ.oddProjection_isStarProjection hE

/-- The actual orthogonal homogeneous split of the entire Hilbert module. -/
def homogeneousSplitEquiv : HilbertModuleEquiv B E (HilbertModuleSum B γ.EvenModule γ.OddModule) :=
  projectionModuleSplitEquiv γ.evenProjection γ.evenProjection_isStarProjection

/-- The same genuine unitary is grading preserving for the canonical positive
and negative gradings on the two actual homogeneous range modules. -/
theorem homogeneousSplitEquiv_grading_intertwine (x : E) :
    γ.homogeneousSplitEquiv (γ.grading x) =
      (GradedHilbertModule.trivial.sum GradedHilbertModule.trivial.opposite).grading
        (γ.homogeneousSplitEquiv x) := by
  rw [GradedHilbertModule.sum_grading_apply, GradedHilbertModule.opposite_grading_apply]
  apply Prod.ext <;> apply Subtype.ext
  · change γ.evenPart (γ.grading x) = γ.evenPart x
    simp only [evenPart, γ.grading_sq]
    rw [add_comm]
  · change γ.oddProjection (γ.grading x) = -γ.oddProjection x
    rw [oddProjection_apply, oddProjection_apply]
    simp only [oddPart, γ.grading_sq]
    rw [← smul_neg, neg_sub]

variable (T : AdjointableMap B E E) (hOdd : γ.IsOdd γ T)

omit [StarOrderedRing B] in
include hOdd in
theorem oddOperator_even_to_odd (x : γ.EvenModule) :
    γ.oddProjection (T (x : E)) = T (x : E) := by
  apply γ.oddProjection_eq_self_of_grading_neg
  rw [hOdd, γ.grading_evenModule]

omit [StarOrderedRing B] in
include hOdd in
theorem oddOperator_odd_to_even (x : γ.OddModule) :
    γ.evenProjection (T (x : E)) = T (x : E) := by
  apply γ.evenProjection_eq_self_of_grading_fixed
  rw [hOdd, γ.grading_oddModule, T.toCLM.map_neg, neg_neg]

/-- The actual rectangular even-to-odd block of an odd operator. -/
def homogeneousOddMap : AdjointableMap B γ.EvenModule γ.OddModule :=
  ((projectionCorestrict γ.oddProjection γ.oddProjection_isStarProjection).comp T).comp
    (projectionInclusion γ.evenProjection γ.evenProjection_isStarProjection)

omit [StarOrderedRing B] in
include hOdd in
@[simp] theorem homogeneousOddMap_coe (x : γ.EvenModule) :
    (γ.homogeneousOddMap T x : E) = T (x : E) := γ.oddOperator_even_to_odd T hOdd x

omit [StarOrderedRing B] in
include hOdd in
theorem homogeneousOddMap_adjoint_coe (hSelf : IsSelfAdjoint T) (x : γ.OddModule) :
    ((γ.homogeneousOddMap T).adjoint x : E) = T (x : E) := by
  have hStar : T.adjoint = T := hSelf.star_eq
  have hAdj : (γ.homogeneousOddMap T).adjoint =
      ((projectionCorestrict γ.evenProjection γ.evenProjection_isStarProjection).comp T.adjoint).comp
        (projectionInclusion γ.oddProjection γ.oddProjection_isStarProjection) := by
    simp only [homogeneousOddMap, projectionCorestrict, AdjointableMap.adjoint_comp,
      AdjointableMap.adjoint_adjoint, AdjointableMap.comp_assoc]
  rw [hAdj]
  change γ.evenProjection (T.adjoint (x : E)) = T (x : E)
  rw [hStar]
  exact γ.oddOperator_odd_to_even T hOdd x

include hOdd in
/-- A genuine global square defect gives the source rectangular Fredholm
defect by the actual finite adjointable range inclusions and corestrictions. -/
theorem homogeneousOddMap_source_defect_isModuleCompact (hSelf : IsSelfAdjoint T)
    (hSquare : IsModuleCompact (T * T - 1)) :
    IsModuleCompact (1 - (γ.homogeneousOddMap T).adjoint.comp (γ.homogeneousOddMap T)) := by
  have hCompact := (hSquare.comp_left
    (projectionCorestrict γ.evenProjection γ.evenProjection_isStarProjection)).comp_right
      (projectionInclusion γ.evenProjection γ.evenProjection_isStarProjection)
  have hEq :
      ((projectionCorestrict γ.evenProjection γ.evenProjection_isStarProjection).comp (T * T - 1)).comp
          (projectionInclusion γ.evenProjection γ.evenProjection_isStarProjection) =
      (γ.homogeneousOddMap T).adjoint.comp (γ.homogeneousOddMap T) - 1 := by
    ext x
    have hFixed : γ.evenProjection (T (T (x : E))) = T (T (x : E)) := by
      have hy : γ.evenProjection
          (((γ.homogeneousOddMap T).adjoint.comp (γ.homogeneousOddMap T)) x : E) =
        (((γ.homogeneousOddMap T).adjoint.comp (γ.homogeneousOddMap T)) x : E) :=
          (((γ.homogeneousOddMap T).adjoint.comp (γ.homogeneousOddMap T)) x).property
      simpa only [AdjointableMap.comp_apply, γ.homogeneousOddMap_adjoint_coe T hOdd hSelf,
        γ.homogeneousOddMap_coe T hOdd] using hy
    have hx : γ.evenProjection (x : E) = (x : E) := x.property
    change γ.evenProjection ((T * T - 1) (x : E)) =
      (((γ.homogeneousOddMap T).adjoint.comp (γ.homogeneousOddMap T) - 1) x : E)
    simp only [AdjointableMap.coe_sub_apply, AdjointableMap.mul_apply, AdjointableMap.one_apply,
      γ.evenProjection.toCLM.map_sub, AdjointableMap.comp_apply, Submodule.coe_sub,
      γ.homogeneousOddMap_adjoint_coe T hOdd hSelf, γ.homogeneousOddMap_coe T hOdd,
      hFixed, hx]
  rw [hEq] at hCompact
  simpa only [neg_sub] using hCompact.neg

include hOdd in
/-- The target rectangular defect is derived from the same genuine global
square defect, again using actual adjointable range maps. -/
theorem homogeneousOddMap_target_defect_isModuleCompact (hSelf : IsSelfAdjoint T)
    (hSquare : IsModuleCompact (T * T - 1)) :
    IsModuleCompact ((γ.homogeneousOddMap T).comp (γ.homogeneousOddMap T).adjoint - 1) := by
  have hCompact := (hSquare.comp_left
    (projectionCorestrict γ.oddProjection γ.oddProjection_isStarProjection)).comp_right
      (projectionInclusion γ.oddProjection γ.oddProjection_isStarProjection)
  have hEq :
      ((projectionCorestrict γ.oddProjection γ.oddProjection_isStarProjection).comp (T * T - 1)).comp
          (projectionInclusion γ.oddProjection γ.oddProjection_isStarProjection) =
      (γ.homogeneousOddMap T).comp (γ.homogeneousOddMap T).adjoint - 1 := by
    ext x
    have hFixed : γ.oddProjection (T (T (x : E))) = T (T (x : E)) := by
      have hy : γ.oddProjection
          (((γ.homogeneousOddMap T).comp (γ.homogeneousOddMap T).adjoint) x : E) =
        (((γ.homogeneousOddMap T).comp (γ.homogeneousOddMap T).adjoint) x : E) :=
          (((γ.homogeneousOddMap T).comp (γ.homogeneousOddMap T).adjoint) x).property
      simpa only [AdjointableMap.comp_apply, γ.homogeneousOddMap_coe T hOdd,
        γ.homogeneousOddMap_adjoint_coe T hOdd hSelf] using hy
    have hx : γ.oddProjection (x : E) = (x : E) := x.property
    change γ.oddProjection ((T * T - 1) (x : E)) =
      (((γ.homogeneousOddMap T).comp (γ.homogeneousOddMap T).adjoint - 1) x : E)
    simp only [AdjointableMap.coe_sub_apply, AdjointableMap.mul_apply, AdjointableMap.one_apply,
      γ.oddProjection.toCLM.map_sub, AdjointableMap.comp_apply, Submodule.coe_sub,
      γ.homogeneousOddMap_coe T hOdd, γ.homogeneousOddMap_adjoint_coe T hOdd hSelf,
      hFixed, hx]
  rwa [hEq] at hCompact

end GradedHilbertModule
end BC4lean.KKTheory
