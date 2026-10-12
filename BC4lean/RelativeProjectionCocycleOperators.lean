import BC4lean.RelativeProjectionSum
import BC4lean.GlobalFredholmScalarCycle
import BC4lean.KasparovCompactAnticommutatorRotation

/-! # The concrete Fredholm rotation for relative projection cocycles

For three actual projections with compact consecutive differences, the
two rectangular operators from P E plus Q E to R E plus Q E are
T0(x,y)=(R y,Q x) and T1(x,y)=(R x,-y). Their Fredholm defects and both
cross anticommutators are actual compact compressions of the projection
differences. No finite-dimensional range or compact projection is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B E : Type*} [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [completeE : CompleteSpace E]

omit completeE in
theorem projectionCrossMap_source_defect_isModuleCompact [CompleteSpace E]
    (P Q : AdjointableMap B E E) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hc : IsModuleCompact (P - Q)) :
    IsModuleCompact (1 - (projectionCrossMap P Q hP hQ).adjoint.comp
      (projectionCrossMap P Q hP hQ)) := by
  have heq : 1 - (projectionCrossMap P Q hP hQ).adjoint.comp (projectionCrossMap P Q hP hQ) =
      (projectionCorestrict P hP).comp ((P - Q).comp (projectionInclusion P hP)) := by
    apply AdjointableMap.ext
    intro x
    apply Subtype.ext
    rw [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, Submodule.coe_sub]
    change (x : E) - P (Q (x : E)) = P ((P - Q) (x : E))
    have hx : P (x : E) = (x : E) := x.property
    simp only [AdjointableMap.coe_sub_apply, P.toCLM.map_sub, hx]
  rw [heq]
  exact (hc.comp_right (projectionInclusion P hP)).comp_left (projectionCorestrict P hP)

omit completeE in
theorem projectionCrossMap_target_defect_isModuleCompact [CompleteSpace E]
    (P Q : AdjointableMap B E E) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hc : IsModuleCompact (P - Q)) :
    IsModuleCompact ((projectionCrossMap P Q hP hQ).comp
      (projectionCrossMap P Q hP hQ).adjoint - 1) := by
  have heq : (projectionCrossMap P Q hP hQ).comp (projectionCrossMap P Q hP hQ).adjoint - 1 =
      (projectionCorestrict Q hQ).comp ((P - Q).comp (projectionInclusion Q hQ)) := by
    apply AdjointableMap.ext
    intro x
    apply Subtype.ext
    rw [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, Submodule.coe_sub]
    change Q (P (x : E)) - (x : E) = Q ((P - Q) (x : E))
    have hx : Q (x : E) = (x : E) := x.property
    simp only [AdjointableMap.coe_sub_apply, Q.toCLM.map_sub, hx]
  rw [heq]
  exact (hc.comp_right (projectionInclusion Q hQ)).comp_left (projectionCorestrict Q hQ)

omit [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] completeE in
theorem projectionCrossMap_same_eq_id
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
    [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
    (P : AdjointableMap B E E) (hP : IsStarProjection P) :
    projectionCrossMap P P hP hP = AdjointableMap.id := by
  apply AdjointableMap.ext
  intro x
  apply Subtype.ext
  exact x.property

variable (P Q R : AdjointableMap B E E)
  (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hR : IsStarProjection R)

def relativeProjectionCocycleT0 : AdjointableMap B
    (HilbertModuleSum B (ProjectionModule P) (ProjectionModule Q))
    (HilbertModuleSum B (ProjectionModule R) (ProjectionModule Q)) :=
  (sumInl.comp (projectionCrossMap Q R hQ hR)).comp sumSnd +
    (sumInr.comp (projectionCrossMap P Q hP hQ)).comp sumFst

def relativeProjectionCocycleT1 : AdjointableMap B
    (HilbertModuleSum B (ProjectionModule P) (ProjectionModule Q))
    (HilbertModuleSum B (ProjectionModule R) (ProjectionModule Q)) :=
  sumMap (projectionCrossMap P R hP hR) (-projectionCrossMap Q Q hQ hQ)

omit completeE P Q R hP hQ hR in
@[simp] theorem relativeProjectionCocycleT0_apply [CompleteSpace E]
    (P Q R : AdjointableMap B E E)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hR : IsStarProjection R)
    (x : HilbertModuleSum B (ProjectionModule P) (ProjectionModule Q)) :
    relativeProjectionCocycleT0 P Q R hP hQ hR x =
      sumMk (projectionCrossMap Q R hQ hR x.snd) (projectionCrossMap P Q hP hQ x.fst) := by
  change (projectionCrossMap Q R hQ hR x.snd, (0 : ProjectionModule Q)) +
    ((0 : ProjectionModule R), projectionCrossMap P Q hP hQ x.fst) = _
  apply Prod.ext
  · change projectionCrossMap Q R hQ hR x.snd + 0 = projectionCrossMap Q R hQ hR x.snd
    exact add_zero _
  · change 0 + projectionCrossMap P Q hP hQ x.fst = projectionCrossMap P Q hP hQ x.fst
    exact zero_add _

omit completeE P Q R hP hQ hR in
@[simp] theorem relativeProjectionCocycleT0_adjoint_apply [CompleteSpace E]
    (P Q R : AdjointableMap B E E)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hR : IsStarProjection R)
    (x : HilbertModuleSum B (ProjectionModule R) (ProjectionModule Q)) :
    (relativeProjectionCocycleT0 P Q R hP hQ hR).adjoint x =
      sumMk (projectionCrossMap Q P hQ hP x.snd) (projectionCrossMap R Q hR hQ x.fst) := by
  change ((0 : ProjectionModule P), projectionCrossMap R Q hR hQ x.fst) +
    (projectionCrossMap Q P hQ hP x.snd, (0 : ProjectionModule Q)) = _
  apply Prod.ext
  · change 0 + projectionCrossMap Q P hQ hP x.snd = projectionCrossMap Q P hQ hP x.snd
    exact zero_add _
  · change projectionCrossMap R Q hR hQ x.fst + 0 = projectionCrossMap R Q hR hQ x.fst
    exact add_zero _

@[simp] theorem relativeProjectionCocycleT1_apply
    (x : HilbertModuleSum B (ProjectionModule P) (ProjectionModule Q)) :
    relativeProjectionCocycleT1 P Q R hP hQ hR x =
      sumMk (projectionCrossMap P R hP hR x.fst) (-x.snd) := by
  rw [relativeProjectionCocycleT1, projectionCrossMap_same_eq_id]
  simp only [sumMap_apply, AdjointableMap.coe_neg_apply, AdjointableMap.id_apply]

@[simp] theorem relativeProjectionCocycleT1_adjoint_apply
    (x : HilbertModuleSum B (ProjectionModule R) (ProjectionModule Q)) :
    (relativeProjectionCocycleT1 P Q R hP hQ hR).adjoint x =
      sumMk (projectionCrossMap R P hR hP x.fst) (-x.snd) := by
  rw [relativeProjectionCocycleT1, sumMap_adjoint, projectionCrossMap_adjoint,
    projectionCrossMap_same_eq_id]
  have hneg : (- (AdjointableMap.id : AdjointableMap B (ProjectionModule Q)
      (ProjectionModule Q))).adjoint = -AdjointableMap.id := by
    rw [← AdjointableMap.star_eq_adjoint, star_neg, AdjointableMap.star_eq_adjoint,
      AdjointableMap.adjoint_id]
  rw [hneg]
  simp only [sumMap_apply, AdjointableMap.coe_neg_apply, AdjointableMap.id_apply]

theorem relativeProjectionCocycleT0_source_defect
    (hcPQ : IsModuleCompact (P - Q)) (hcQR : IsModuleCompact (Q - R)) :
    IsModuleCompact (1 - (relativeProjectionCocycleT0 P Q R hP hQ hR).adjoint.comp
      (relativeProjectionCocycleT0 P Q R hP hQ hR)) := by
  have heq : 1 - (relativeProjectionCocycleT0 P Q R hP hQ hR).adjoint.comp
      (relativeProjectionCocycleT0 P Q R hP hQ hR) =
      sumMap (1 - (projectionCrossMap P Q hP hQ).adjoint.comp (projectionCrossMap P Q hP hQ))
        (1 - (projectionCrossMap Q R hQ hR).adjoint.comp (projectionCrossMap Q R hQ hR)) := by
    ext x
    simp only [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, AdjointableMap.comp_apply,
      relativeProjectionCocycleT0_apply, relativeProjectionCocycleT0_adjoint_apply,
      projectionCrossMap_adjoint, sumMap_apply, sumMk_fst, sumMk_snd]
    rfl
  rw [heq]
  exact (projectionCrossMap_source_defect_isModuleCompact P Q hP hQ hcPQ).sumMap
    (projectionCrossMap_source_defect_isModuleCompact Q R hQ hR hcQR)

theorem relativeProjectionCocycleT0_target_defect
    (hcPQ : IsModuleCompact (P - Q)) (hcQR : IsModuleCompact (Q - R)) :
    IsModuleCompact ((relativeProjectionCocycleT0 P Q R hP hQ hR).comp
      (relativeProjectionCocycleT0 P Q R hP hQ hR).adjoint - 1) := by
  have heq : (relativeProjectionCocycleT0 P Q R hP hQ hR).comp
      (relativeProjectionCocycleT0 P Q R hP hQ hR).adjoint - 1 =
      sumMap ((projectionCrossMap Q R hQ hR).comp (projectionCrossMap Q R hQ hR).adjoint - 1)
        ((projectionCrossMap P Q hP hQ).comp (projectionCrossMap P Q hP hQ).adjoint - 1) := by
    ext x
    simp only [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, AdjointableMap.comp_apply,
      relativeProjectionCocycleT0_apply, relativeProjectionCocycleT0_adjoint_apply,
      projectionCrossMap_adjoint, sumMap_apply, sumMk_fst, sumMk_snd]
    rfl
  rw [heq]
  exact (projectionCrossMap_target_defect_isModuleCompact Q R hQ hR hcQR).sumMap
    (projectionCrossMap_target_defect_isModuleCompact P Q hP hQ hcPQ)

omit completeE in
theorem relativeProjectionCocycle_difference_compact [CompleteSpace E]
    (P Q R : AdjointableMap B E E)
    (hcPQ : IsModuleCompact (P - Q)) (hcQR : IsModuleCompact (Q - R)) :
    IsModuleCompact (P - R) := by
  have heq : P - R = (P - Q) + (Q - R) := by abel
  rw [heq]
  exact hcPQ.add hcQR

theorem relativeProjectionCocycleT1_source_defect
    (hcPQ : IsModuleCompact (P - Q)) (hcQR : IsModuleCompact (Q - R)) :
    IsModuleCompact (1 - (relativeProjectionCocycleT1 P Q R hP hQ hR).adjoint.comp
      (relativeProjectionCocycleT1 P Q R hP hQ hR)) := by
  have heq : 1 - (relativeProjectionCocycleT1 P Q R hP hQ hR).adjoint.comp
      (relativeProjectionCocycleT1 P Q R hP hQ hR) =
      sumMap (1 - (projectionCrossMap P R hP hR).adjoint.comp (projectionCrossMap P R hP hR)) 0 := by
    apply AdjointableMap.ext
    intro x
    apply Prod.ext <;> simp
  rw [heq]
  exact (projectionCrossMap_source_defect_isModuleCompact P R hP hR
    (relativeProjectionCocycle_difference_compact P Q R hcPQ hcQR)).sumMap IsModuleCompact.zero

theorem relativeProjectionCocycleT1_target_defect
    (hcPQ : IsModuleCompact (P - Q)) (hcQR : IsModuleCompact (Q - R)) :
    IsModuleCompact ((relativeProjectionCocycleT1 P Q R hP hQ hR).comp
      (relativeProjectionCocycleT1 P Q R hP hQ hR).adjoint - 1) := by
  have heq : (relativeProjectionCocycleT1 P Q R hP hQ hR).comp
      (relativeProjectionCocycleT1 P Q R hP hQ hR).adjoint - 1 =
      sumMap ((projectionCrossMap P R hP hR).comp (projectionCrossMap P R hP hR).adjoint - 1) 0 := by
    apply AdjointableMap.ext
    intro x
    apply Prod.ext <;> simp
  rw [heq]
  exact (projectionCrossMap_target_defect_isModuleCompact P R hP hR
    (relativeProjectionCocycle_difference_compact P Q R hcPQ hcQR)).sumMap IsModuleCompact.zero

def relativeProjectionCocycleBlock (S T H : AdjointableMap B E E)
    (hS : IsStarProjection S) (hT : IsStarProjection T) :
    AdjointableMap B (ProjectionModule T) (ProjectionModule S) :=
  (projectionCorestrict S hS).comp (H.comp (projectionInclusion T hT))

omit completeE in
theorem relativeProjectionCocycleBlock_compact [CompleteSpace E] (S T H : AdjointableMap B E E)
    (hS : IsStarProjection S) (hT : IsStarProjection T) (hc : IsModuleCompact H) :
    IsModuleCompact (relativeProjectionCocycleBlock S T H hS hT) :=
  (hc.comp_right (projectionInclusion T hT)).comp_left (projectionCorestrict S hS)

theorem relativeProjectionCocycle_source_cross_compact
    (hcPQ : IsModuleCompact (P - Q)) (hcQR : IsModuleCompact (Q - R)) :
    IsModuleCompact ((relativeProjectionCocycleT0 P Q R hP hQ hR).adjoint.comp
        (relativeProjectionCocycleT1 P Q R hP hQ hR) +
      (relativeProjectionCocycleT1 P Q R hP hQ hR).adjoint.comp
        (relativeProjectionCocycleT0 P Q R hP hQ hR)) := by
  let K₀ := relativeProjectionCocycleBlock P Q (R - Q) hP hQ
  let K₁ := relativeProjectionCocycleBlock Q P (R - P) hQ hP
  have hc₀ : IsModuleCompact K₀ := relativeProjectionCocycleBlock_compact P Q _ hP hQ
    (by simpa only [neg_sub] using hcQR.neg)
  have hc₁ : IsModuleCompact K₁ := relativeProjectionCocycleBlock_compact Q P _ hQ hP
    (by simpa only [neg_sub] using (relativeProjectionCocycle_difference_compact P Q R hcPQ hcQR).neg)
  have heq : (relativeProjectionCocycleT0 P Q R hP hQ hR).adjoint.comp
        (relativeProjectionCocycleT1 P Q R hP hQ hR) +
      (relativeProjectionCocycleT1 P Q R hP hQ hR).adjoint.comp
        (relativeProjectionCocycleT0 P Q R hP hQ hR) =
      (sumInl.comp K₀).comp sumSnd + (sumInr.comp K₁).comp sumFst := by
    apply AdjointableMap.ext
    intro x
    apply Prod.ext
    · apply Subtype.ext
      have hfixed : Q (x.snd : E) = (x.snd : E) := x.snd.property
      simp [K₀, relativeProjectionCocycleBlock, hfixed]; abel
    · apply Subtype.ext
      have hfixed : P (x.fst : E) = (x.fst : E) := x.fst.property
      simp [K₁, relativeProjectionCocycleBlock, hfixed]; abel
  rw [heq]
  exact ((hc₀.comp_left sumInl).comp_right sumSnd).add
    ((hc₁.comp_left sumInr).comp_right sumFst)

theorem relativeProjectionCocycle_target_cross_compact
    (hcPQ : IsModuleCompact (P - Q)) (hcQR : IsModuleCompact (Q - R)) :
    IsModuleCompact ((relativeProjectionCocycleT0 P Q R hP hQ hR).comp
        (relativeProjectionCocycleT1 P Q R hP hQ hR).adjoint +
      (relativeProjectionCocycleT1 P Q R hP hQ hR).comp
        (relativeProjectionCocycleT0 P Q R hP hQ hR).adjoint) := by
  let K₀ := relativeProjectionCocycleBlock R Q (P - Q) hR hQ
  let K₁ := relativeProjectionCocycleBlock Q R (P - R) hQ hR
  have hc₀ : IsModuleCompact K₀ := relativeProjectionCocycleBlock_compact R Q _ hR hQ hcPQ
  have hc₁ : IsModuleCompact K₁ := relativeProjectionCocycleBlock_compact Q R _ hQ hR
    (relativeProjectionCocycle_difference_compact P Q R hcPQ hcQR)
  have heq : (relativeProjectionCocycleT0 P Q R hP hQ hR).comp
        (relativeProjectionCocycleT1 P Q R hP hQ hR).adjoint +
      (relativeProjectionCocycleT1 P Q R hP hQ hR).comp
        (relativeProjectionCocycleT0 P Q R hP hQ hR).adjoint =
      (sumInl.comp K₀).comp sumSnd + (sumInr.comp K₁).comp sumFst := by
    apply AdjointableMap.ext
    intro x
    apply Prod.ext
    · apply Subtype.ext
      have hfixed : Q (x.snd : E) = (x.snd : E) := x.snd.property
      simp [K₀, relativeProjectionCocycleBlock, hfixed]; abel
    · apply Subtype.ext
      have hfixed : R (x.fst : E) = (x.fst : E) := x.fst.property
      simp [K₁, relativeProjectionCocycleBlock, hfixed]; abel
  rw [heq]
  exact ((hc₀.comp_left sumInl).comp_right sumSnd).add
    ((hc₁.comp_left sumInr).comp_right sumFst)

end BC4lean.KKTheory
