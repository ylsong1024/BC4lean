import BC4lean.RelativeProjectionCocycleOperators

/-! # The actual relative-projection cocycle in full homotopy classes

The concrete rotation from (Ry,Qx) to (Rx,-y) connects the sum of
the P/Q and Q/R cycles to the P/R cycle plus an exactly degenerate
Q/Q summand. Both cross terms were derived from compact projection
differences in the preceding file. The interval witness is constructed
from the actual operator path, and both endpoint identifications are
coefficient-inner-product-preserving whole-cycle unitaries.
-/

noncomputable section
universe uΓ uB uE
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {Γ : Type uΓ} {B : Type uB} {E : Type uE} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

variable (P Q R : AdjointableMap B E E)
  (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hR : IsStarProjection R)
  (hcPQ : IsModuleCompact (P - Q)) (hcQR : IsModuleCompact (Q - R))
  (hE : IsCountablyGeneratedModule B E)

def relativeProjectionCocycleStartCycle :=
  globalFredholmScalarCycle (Γ := Γ) (relativeProjectionCocycleT0 P Q R hP hQ hR)
    (relativeProjectionCocycleT0_source_defect P Q R hP hQ hR hcPQ hcQR)
    (relativeProjectionCocycleT0_target_defect P Q R hP hQ hR hcPQ hcQR)
    ((projectionModule_isCountablyGenerated P hP hE).sum
      (projectionModule_isCountablyGenerated Q hQ hE))
    ((projectionModule_isCountablyGenerated R hR hE).sum
      (projectionModule_isCountablyGenerated Q hQ hE))

def relativeProjectionCocycleEndCycle :=
  globalFredholmScalarCycle (Γ := Γ) (relativeProjectionCocycleT1 P Q R hP hQ hR)
    (relativeProjectionCocycleT1_source_defect P Q R hP hQ hR hcPQ hcQR)
    (relativeProjectionCocycleT1_target_defect P Q R hP hQ hR hcPQ hcQR)
    ((projectionModule_isCountablyGenerated P hP hE).sum
      (projectionModule_isCountablyGenerated Q hQ hE))
    ((projectionModule_isCountablyGenerated R hR hE).sum
      (projectionModule_isCountablyGenerated Q hQ hE))

omit [CompleteSpace E] Q in
/-- This square is exactly one, without compactness of the supported range. -/
theorem relativeProjectionNegativeIdentity_source_defect [CompleteSpace E]
    (Q : AdjointableMap B E E) :
    IsModuleCompact (1 - (-AdjointableMap.id (B := B) (E := ProjectionModule Q)).adjoint.comp
      (-AdjointableMap.id)) := by
  have hneg : (- (AdjointableMap.id : AdjointableMap B (ProjectionModule Q)
      (ProjectionModule Q))).adjoint = -AdjointableMap.id := by
    rw [← AdjointableMap.star_eq_adjoint, star_neg, AdjointableMap.star_eq_adjoint,
      AdjointableMap.adjoint_id]
  have heq : 1 - (-AdjointableMap.id (B := B) (E := ProjectionModule Q)).adjoint.comp
      (-AdjointableMap.id) = 0 := by
    rw [hneg]
    apply AdjointableMap.ext
    intro x
    simp only [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply,
      AdjointableMap.comp_apply, AdjointableMap.coe_neg_apply, AdjointableMap.id_apply,
      AdjointableMap.coe_zero_apply, neg_neg, sub_self]
  rw [heq]
  exact IsModuleCompact.zero

omit [CompleteSpace E] Q in
theorem relativeProjectionNegativeIdentity_target_defect [CompleteSpace E]
    (Q : AdjointableMap B E E) :
    IsModuleCompact ((-AdjointableMap.id (B := B) (E := ProjectionModule Q)).comp
      (-AdjointableMap.id).adjoint - 1) := by
  have hneg : (- (AdjointableMap.id : AdjointableMap B (ProjectionModule Q)
      (ProjectionModule Q))).adjoint = -AdjointableMap.id := by
    rw [← AdjointableMap.star_eq_adjoint, star_neg, AdjointableMap.star_eq_adjoint,
      AdjointableMap.adjoint_id]
  have heq : (-AdjointableMap.id (B := B) (E := ProjectionModule Q)).comp
      (-AdjointableMap.id).adjoint - 1 = 0 := by
    rw [hneg]
    apply AdjointableMap.ext
    intro x
    simp only [AdjointableMap.coe_sub_apply, AdjointableMap.comp_apply,
      AdjointableMap.coe_neg_apply, AdjointableMap.id_apply, AdjointableMap.one_apply,
      AdjointableMap.coe_zero_apply, neg_neg, sub_self]
  rw [heq]
  exact IsModuleCompact.zero

def relativeProjectionNegativeIdentityCycle :=
  globalFredholmScalarCycle (Γ := Γ) (-AdjointableMap.id (B := B) (E := ProjectionModule Q))
    (relativeProjectionNegativeIdentity_source_defect Q)
    (relativeProjectionNegativeIdentity_target_defect Q)
    (projectionModule_isCountablyGenerated Q hQ hE)
    (projectionModule_isCountablyGenerated Q hQ hE)

theorem relativeProjectionNegativeIdentityCycle_isDegenerate :
    (relativeProjectionNegativeIdentityCycle (Γ := Γ) Q hQ hE).IsDegenerate := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    change (offDiagonalAdjointable (-AdjointableMap.id) -
      star (offDiagonalAdjointable (-AdjointableMap.id))) * scalarModuleRepresentation a = 0
    rw [offDiagonalAdjointable_star, sub_self, zero_mul]
  · intro a
    have hs : offDiagonalAdjointable (-AdjointableMap.id (B := B) (E := ProjectionModule Q)) *
        offDiagonalAdjointable (-AdjointableMap.id) = 1 := by
      rw [offDiagonalAdjointable_square]
      have hneg : (- (AdjointableMap.id : AdjointableMap B (ProjectionModule Q)
          (ProjectionModule Q))).adjoint = -AdjointableMap.id := by
        rw [← AdjointableMap.star_eq_adjoint, star_neg, AdjointableMap.star_eq_adjoint,
          AdjointableMap.adjoint_id]
      simp only [hneg]
      have hid : (-AdjointableMap.id : AdjointableMap B (ProjectionModule Q)
          (ProjectionModule Q)).comp (-AdjointableMap.id) = 1 := by
        apply AdjointableMap.ext
        intro x
        simp only [AdjointableMap.comp_apply, AdjointableMap.coe_neg_apply,
          AdjointableMap.id_apply, neg_neg, AdjointableMap.one_apply]
      simpa only [hid] using
        (sumMap_one (B := B) (E := ProjectionModule Q) (F := ProjectionModule Q))
    change (offDiagonalAdjointable (-AdjointableMap.id) *
      offDiagonalAdjointable (-AdjointableMap.id) - 1) * scalarModuleRepresentation a = 0
    rw [hs, sub_self, zero_mul]
  · intro a
    change offDiagonalAdjointable (-AdjointableMap.id) * scalarModuleRepresentation a -
      scalarModuleRepresentation a * offDiagonalAdjointable (-AdjointableMap.id) = 0
    apply AdjointableMap.ext
    intro x
    simp only [AdjointableMap.coe_sub_apply, AdjointableMap.mul_apply,
      scalarModuleRepresentation_apply, AdjointableMap.coe_zero_apply]
    exact sub_eq_zero.mpr ((offDiagonalAdjointable (-AdjointableMap.id)).toCLM.map_smul a x)
  · intro g a
    have heq : (EquivariantHilbertModule.trivial (Γ := Γ)).conjugateOperator g
        (offDiagonalAdjointable (-AdjointableMap.id (B := B) (E := ProjectionModule Q))) =
        offDiagonalAdjointable (-AdjointableMap.id) := by ext x; rfl
    change ((EquivariantHilbertModule.trivial (Γ := Γ)).conjugateOperator g
      (offDiagonalAdjointable (-AdjointableMap.id)) - offDiagonalAdjointable (-AdjointableMap.id)) *
        scalarModuleRepresentation a = 0
    rw [heq, sub_self, zero_mul]

set_option maxHeartbeats 800000 in
/-- Actual shuffle of the two cycle summands to the concrete starting rectangle. -/
def relativeProjectionCocycleStartIso : KasparovCycleIso
    ((relativeProjectionCycle (Γ := Γ) P Q hP hQ hcPQ hE).directSum
      (relativeProjectionCycle (Γ := Γ) Q R hQ hR hcQR hE))
    (relativeProjectionCocycleStartCycle (Γ := Γ) P Q R hP hQ hR hcPQ hcQR hE) where
  moduleEquiv := relativeProjectionMiddleShuffle.trans
    (HilbertModuleEquiv.refl.sum HilbertModuleEquiv.sumSwapEquiv)
  grading_intertwine x := by
    change ((x.fst.fst, x.snd.fst), (-x.snd.snd, -x.fst.snd)) =
      ((x.fst.fst, x.snd.fst), -(x.snd.snd, x.fst.snd))
    rfl
  action_intertwine _ _ := rfl
  representation_intertwine a x := by
    change (relativeProjectionMiddleShuffle.trans
        (HilbertModuleEquiv.refl.sum HilbertModuleEquiv.sumSwapEquiv))
      (sumMap (scalarModuleRepresentation a) (scalarModuleRepresentation a) x) =
      scalarModuleRepresentation a ((relativeProjectionMiddleShuffle.trans
        (HilbertModuleEquiv.refl.sum HilbertModuleEquiv.sumSwapEquiv)) x)
    simp only [sumMap_apply, scalarModuleRepresentation_apply, ← sumMk_smul, sumMk_eta]
    exact HilbertModuleEquiv.map_smul _ a x
  operator_intertwine x := by
    change (relativeProjectionMiddleShuffle.trans
        (HilbertModuleEquiv.refl.sum HilbertModuleEquiv.sumSwapEquiv))
      (sumMap (offDiagonalAdjointable (projectionCrossMap P Q hP hQ))
        (offDiagonalAdjointable (projectionCrossMap Q R hQ hR)) x) =
      offDiagonalAdjointable (relativeProjectionCocycleT0 P Q R hP hQ hR)
        ((relativeProjectionMiddleShuffle.trans
          (HilbertModuleEquiv.refl.sum HilbertModuleEquiv.sumSwapEquiv)) x)
    simp only [HilbertModuleEquiv.trans_apply, relativeProjectionMiddleShuffle_apply,
      HilbertModuleEquiv.sum_apply, HilbertModuleEquiv.refl_apply,
      HilbertModuleEquiv.sumSwapEquiv_apply, sumMap_apply, offDiagonalAdjointable_apply,
      projectionCrossMap_adjoint, relativeProjectionCocycleT0_apply,
      relativeProjectionCocycleT0_adjoint_apply, sumMk_fst, sumMk_snd]

/-- The terminal shuffle separates the P/R cycle and the exactly degenerate tail. -/
def relativeProjectionCocycleEndIso : KasparovCycleIso
    (relativeProjectionCocycleEndCycle (Γ := Γ) P Q R hP hQ hR hcPQ hcQR hE)
    ((relativeProjectionCycle (Γ := Γ) P R hP hR
      (relativeProjectionCocycle_difference_compact P Q R hcPQ hcQR) hE).directSum
      (relativeProjectionNegativeIdentityCycle (Γ := Γ) Q hQ hE)) where
  moduleEquiv := relativeProjectionMiddleShuffle
  grading_intertwine x := rfl
  action_intertwine _ _ := rfl
  representation_intertwine a x := by
    change relativeProjectionMiddleShuffle (scalarModuleRepresentation a x) =
      sumMap (scalarModuleRepresentation a) (scalarModuleRepresentation a)
        (relativeProjectionMiddleShuffle x)
    simp only [scalarModuleRepresentation_apply, sumMap_apply, ← sumMk_smul, sumMk_eta]
    exact HilbertModuleEquiv.map_smul _ a x
  operator_intertwine x := by
    change relativeProjectionMiddleShuffle
        (offDiagonalAdjointable (relativeProjectionCocycleT1 P Q R hP hQ hR) x) =
      sumMap (offDiagonalAdjointable (projectionCrossMap P R hP hR))
        (offDiagonalAdjointable (-AdjointableMap.id)) (relativeProjectionMiddleShuffle x)
    have hneg : (- (AdjointableMap.id : AdjointableMap B (ProjectionModule Q)
        (ProjectionModule Q))).adjoint = -AdjointableMap.id := by
      rw [← AdjointableMap.star_eq_adjoint, star_neg, AdjointableMap.star_eq_adjoint,
        AdjointableMap.adjoint_id]
    simp only [relativeProjectionMiddleShuffle_apply, offDiagonalAdjointable_apply,
      relativeProjectionCocycleT1_apply,
      relativeProjectionCocycleT1_adjoint_apply, projectionCrossMap_adjoint,
      sumMap_apply, sumMk_fst, sumMk_snd, hneg, AdjointableMap.coe_neg_apply,
      AdjointableMap.id_apply]

include hcPQ hcQR in
theorem relativeProjectionCocycle_anticommutator_compact :
    IsModuleCompact
      (offDiagonalAdjointable (relativeProjectionCocycleT0 P Q R hP hQ hR) *
          offDiagonalAdjointable (relativeProjectionCocycleT1 P Q R hP hQ hR) +
        offDiagonalAdjointable (relativeProjectionCocycleT1 P Q R hP hQ hR) *
          offDiagonalAdjointable (relativeProjectionCocycleT0 P Q R hP hQ hR)) := by
  have heq : offDiagonalAdjointable (relativeProjectionCocycleT0 P Q R hP hQ hR) *
          offDiagonalAdjointable (relativeProjectionCocycleT1 P Q R hP hQ hR) +
        offDiagonalAdjointable (relativeProjectionCocycleT1 P Q R hP hQ hR) *
          offDiagonalAdjointable (relativeProjectionCocycleT0 P Q R hP hQ hR) =
      sumMap ((relativeProjectionCocycleT0 P Q R hP hQ hR).adjoint.comp
          (relativeProjectionCocycleT1 P Q R hP hQ hR) +
        (relativeProjectionCocycleT1 P Q R hP hQ hR).adjoint.comp
          (relativeProjectionCocycleT0 P Q R hP hQ hR))
        ((relativeProjectionCocycleT0 P Q R hP hQ hR).comp
          (relativeProjectionCocycleT1 P Q R hP hQ hR).adjoint +
        (relativeProjectionCocycleT1 P Q R hP hQ hR).comp
          (relativeProjectionCocycleT0 P Q R hP hQ hR).adjoint) := by
    ext x
    simp only [AdjointableMap.mul_apply, AdjointableMap.coe_add_apply,
      offDiagonalAdjointable_apply, sumMap_apply, sumMk_fst, sumMk_snd,
      AdjointableMap.comp_apply]
    rfl
  rw [heq]
  exact (relativeProjectionCocycle_source_cross_compact P Q R hP hQ hR hcPQ hcQR).sumMap
    (relativeProjectionCocycle_target_cross_compact P Q R hP hQ hR hcPQ hcQR)

/-- A genuine norm-continuous rotation with proved cycle conditions throughout. -/
def relativeProjectionCocycleOperatorHomotopy : KasparovOperatorHomotopy
    (relativeProjectionCocycleStartCycle (Γ := Γ) P Q R hP hQ hR hcPQ hcQR hE)
    (offDiagonalAdjointable (relativeProjectionCocycleT0 P Q R hP hQ hR))
    (offDiagonalAdjointable (relativeProjectionCocycleT1 P Q R hP hQ hR)) :=
  KasparovOperatorHomotopy.compactAnticommutatorRotation
    (relativeProjectionCocycleStartCycle (Γ := Γ) P Q R hP hQ hR hcPQ hcQR hE) _ _
    (relativeProjectionCocycleStartCycle (Γ := Γ) P Q R hP hQ hR hcPQ hcQR hE).operatorConditions
    { operator_odd :=
        (relativeProjectionCocycleEndCycle (Γ := Γ) P Q R hP hQ hR hcPQ hcQR hE).operator_odd
      selfadjoint_mod_compact :=
        (relativeProjectionCocycleEndCycle (Γ := Γ) P Q R hP hQ hR hcPQ hcQR hE).selfadjoint_mod_compact
      square_mod_compact :=
        (relativeProjectionCocycleEndCycle (Γ := Γ) P Q R hP hQ hR hcPQ hcQR hE).square_mod_compact
      commutator_compact :=
        (relativeProjectionCocycleEndCycle (Γ := Γ) P Q R hP hQ hR hcPQ hcQR hE).commutator_compact
      equivariance_mod_compact :=
        (relativeProjectionCocycleEndCycle (Γ := Γ) P Q R hP hQ hR hcPQ hcQR hE).equivariance_mod_compact }
    (fun a => (relativeProjectionCocycle_anticommutator_compact P Q R hP hQ hR hcPQ hcQR).comp_right
      (scalarModuleRepresentation a))

/-- The concrete rotation and endpoint unitaries produce the full class cocycle. -/
theorem relativeProjectionCocycle_class :
    KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (relativeProjectionCycle (Γ := Γ) P Q hP hQ hcPQ hE)) +
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (relativeProjectionCycle (Γ := Γ) Q R hQ hR hcQR hE)) =
    KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (relativeProjectionCycle (Γ := Γ) P R hP hR
        (relativeProjectionCocycle_difference_compact P Q R hcPQ hcQR) hE)) := by
  have hstart := KasparovHomotopyClass.mk_eq_of_iso
    (c := BundledKasparovCycle.of
      ((relativeProjectionCycle (Γ := Γ) P Q hP hQ hcPQ hE).directSum
        (relativeProjectionCycle (Γ := Γ) Q R hQ hR hcQR hE)))
    (d := BundledKasparovCycle.of
      (relativeProjectionCocycleStartCycle (Γ := Γ) P Q R hP hQ hR hcPQ hcQR hE))
    (relativeProjectionCocycleStartIso (Γ := Γ) P Q R hP hQ hR hcPQ hcQR hE)
  have hrotate := KasparovHomotopyClass.mk_eq_of_full
    (FullKasparovHomotopy.ofOperatorHomotopy
      (relativeProjectionCocycleOperatorHomotopy (Γ := Γ) P Q R hP hQ hR hcPQ hcQR hE))
  have hend := KasparovHomotopyClass.mk_eq_of_iso
    (c := BundledKasparovCycle.of
      (relativeProjectionCocycleEndCycle (Γ := Γ) P Q R hP hQ hR hcPQ hcQR hE))
    (d := BundledKasparovCycle.of
      ((relativeProjectionCycle (Γ := Γ) P R hP hR
        (relativeProjectionCocycle_difference_compact P Q R hcPQ hcQR) hE).directSum
        (relativeProjectionNegativeIdentityCycle (Γ := Γ) Q hQ hE)))
    (relativeProjectionCocycleEndIso (Γ := Γ) P Q R hP hQ hR hcPQ hcQR hE)
  have hzero := KasparovHomotopyClass.mk_eq_zero_of_degenerate
    (BundledKasparovCycle.of (relativeProjectionNegativeIdentityCycle (Γ := Γ) Q hQ hE))
    (relativeProjectionNegativeIdentityCycle_isDegenerate (Γ := Γ) Q hQ hE)
  change KasparovHomotopyClass.mk (BundledKasparovCycle.of
    ((relativeProjectionCycle (Γ := Γ) P Q hP hQ hcPQ hE).directSum
      (relativeProjectionCycle (Γ := Γ) Q R hQ hR hcQR hE))) = _
  calc
    _ = KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (relativeProjectionCocycleStartCycle (Γ := Γ) P Q R hP hQ hR hcPQ hcQR hE)) := hstart
    _ = KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (relativeProjectionCocycleEndCycle (Γ := Γ) P Q R hP hQ hR hcPQ hcQR hE)) := hrotate
    _ = _ := by
      rw [hend]
      change KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (relativeProjectionCycle (Γ := Γ) P R hP hR
          (relativeProjectionCocycle_difference_compact P Q R hcPQ hcQR) hE)) +
        KasparovHomotopyClass.mk (BundledKasparovCycle.of
          (relativeProjectionNegativeIdentityCycle (Γ := Γ) Q hQ hE)) = _
      rw [hzero, add_zero]

end BC4lean.KKTheory
