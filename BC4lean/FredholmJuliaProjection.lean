import BC4lean.HilbertModuleJuliaSqrt
import BC4lean.RelativeProjectionKasparovCycle
import BC4lean.CompactModuleOperatorCriterion

/-! # Actual Julia projection pair of a global Fredholm contraction

For T:E→F, the column Vx=(√(1−T*T)x,Tx) is an actual isometry.
P=VV* and Q=diag(0,1) are genuine projections. Global compact Fredholm
defects make P−Q compact, using the proved square compactness criterion.
Actual range unitaries identify the supported crossmap QP with T, and its
adjoint with T*. These are constructed operator identities, not an assumed
Fredholm or finite-projection normal form.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

def juliaFredholmColumn (T : AdjointableMap B E F) : AdjointableMap B E (HilbertModuleSum B E F) :=
  sumInl.comp (juliaSourceDefect T) + sumInr.comp T

omit [CompleteSpace F] in
@[simp] theorem juliaFredholmColumn_apply (T : AdjointableMap B E F) (x : E) :
    juliaFredholmColumn T x = sumMk (juliaSourceDefect T x) (T x) := by
  simp only [juliaFredholmColumn, AdjointableMap.coe_add_apply, AdjointableMap.comp_apply,
    sumInl_apply, sumInr_apply, sumMk_add, add_zero, zero_add]

omit [CompleteSpace F] in
@[simp] theorem juliaFredholmColumn_adjoint_apply (T : AdjointableMap B E F)
    (x : HilbertModuleSum B E F) :
    (juliaFredholmColumn T).adjoint x = juliaSourceDefect T x.fst + T.adjoint x.snd := by
  change (juliaSourceDefect T).adjoint x.fst + T.adjoint x.snd = _
  rw [juliaSourceDefect_adjoint]

theorem juliaFredholmColumn_adjoint_comp_self (T : AdjointableMap B E F) (hT : ‖T‖ ≤ 1) :
    (juliaFredholmColumn T).adjoint.comp (juliaFredholmColumn T) = AdjointableMap.id := by
  ext x
  simp only [AdjointableMap.comp_apply, juliaFredholmColumn_apply,
    juliaFredholmColumn_adjoint_apply, sumMk_fst, sumMk_snd, AdjointableMap.id_apply]
  exact congrArg (fun R : AdjointableMap B E E => R x) (juliaSourceDefect_square T hT)

def juliaFredholmProjection (T : AdjointableMap B E F) :
    AdjointableMap B (HilbertModuleSum B E F) (HilbertModuleSum B E F) :=
  (juliaFredholmColumn T).comp (juliaFredholmColumn T).adjoint

def juliaReferenceProjection :
    AdjointableMap B (HilbertModuleSum B E F) (HilbertModuleSum B E F) := sumInr.comp sumSnd

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem juliaReferenceProjection_apply (x : HilbertModuleSum B E F) :
    juliaReferenceProjection x = sumMk (0 : E) x.snd := rfl

theorem juliaFredholmProjection_isStarProjection (T : AdjointableMap B E F) (hT : ‖T‖ ≤ 1) :
    IsStarProjection (juliaFredholmProjection T) where
  isIdempotentElem := by
    ext x
    change juliaFredholmColumn T ((juliaFredholmColumn T).adjoint
      (juliaFredholmColumn T ((juliaFredholmColumn T).adjoint x))) =
      juliaFredholmColumn T ((juliaFredholmColumn T).adjoint x)
    have hh := congrArg (fun R : AdjointableMap B E E => R ((juliaFredholmColumn T).adjoint x))
      (juliaFredholmColumn_adjoint_comp_self T hT)
    change (juliaFredholmColumn T).adjoint
      (juliaFredholmColumn T ((juliaFredholmColumn T).adjoint x)) = (juliaFredholmColumn T).adjoint x at hh
    rw [hh]
  isSelfAdjoint := by
    change ((juliaFredholmColumn T).comp (juliaFredholmColumn T).adjoint).adjoint = _
    rw [AdjointableMap.adjoint_comp, AdjointableMap.adjoint_adjoint]
    rfl

omit [CompleteSpace E] [CompleteSpace F] in
theorem juliaReferenceProjection_isStarProjection :
    IsStarProjection (juliaReferenceProjection (B := B) (E := E) (F := F)) where
  isIdempotentElem := by
    ext x
    simp only [AdjointableMap.mul_apply, juliaReferenceProjection_apply, sumMk_snd]
  isSelfAdjoint := by
    change (sumInr.comp sumSnd).adjoint = sumInr.comp sumSnd
    rw [AdjointableMap.adjoint_comp, sumSnd_adjoint, sumInr_adjoint]

/-- The source defect root is actually compact whenever its square is compact. -/
theorem juliaSourceDefect_isModuleCompact (T : AdjointableMap B E F) (hT : ‖T‖ ≤ 1)
    (h : IsModuleCompact (1 - T.adjoint.comp T)) : IsModuleCompact (juliaSourceDefect T) := by
  apply IsModuleCompact.of_adjoint_comp_self
  rw [juliaSourceDefect_adjoint]
  change IsModuleCompact (juliaSourceDefect T * juliaSourceDefect T)
  have hs : juliaSourceDefect T * juliaSourceDefect T = 1 - T.adjoint.comp T := by
    have hh := juliaSourceDefect_square T hT
    exact eq_sub_iff_add_eq.mpr hh
  rw [hs]
  exact h

omit [CompleteSpace F] in
theorem juliaFredholmProjection_difference (T : AdjointableMap B E F) :
    juliaFredholmProjection T - juliaReferenceProjection =
      sumMap (juliaSourceDefect T * juliaSourceDefect T) (T.comp T.adjoint - 1) +
        (sumInl.comp ((juliaSourceDefect T).comp T.adjoint)).comp sumSnd +
        (sumInr.comp (T.comp (juliaSourceDefect T))).comp sumFst := by
  ext x
  simp only [juliaFredholmProjection, AdjointableMap.coe_sub_apply,
    AdjointableMap.coe_add_apply, AdjointableMap.comp_apply, AdjointableMap.mul_apply,
    AdjointableMap.one_apply, juliaFredholmColumn_apply, juliaFredholmColumn_adjoint_apply,
    juliaReferenceProjection_apply, sumMap_apply, sumInl_apply, sumInr_apply,
    sumFst_apply, sumSnd_apply]
  apply Prod.ext
  · simp only [WithCStarModule.sub_fst, WithCStarModule.add_fst, sumMk_fst]
    rw [(juliaSourceDefect T).toCLM.map_add]
    simp only [sub_zero, add_zero]
  · simp only [WithCStarModule.sub_snd, WithCStarModule.add_snd, sumMk_snd]
    rw [T.toCLM.map_add]
    abel

/-- Both global Fredholm defects give the actual compact projection difference. -/
theorem juliaFredholmProjection_difference_isModuleCompact (T : AdjointableMap B E F)
    (hT : ‖T‖ ≤ 1) (hSource : IsModuleCompact (1 - T.adjoint.comp T))
    (hTarget : IsModuleCompact (T.comp T.adjoint - 1)) :
    IsModuleCompact (juliaFredholmProjection T - juliaReferenceProjection) := by
  have hS := juliaSourceDefect_isModuleCompact T hT hSource
  rw [juliaFredholmProjection_difference]
  exact ((hS.comp_left (juliaSourceDefect T)).sumMap hTarget).add
    (((hS.comp_right T.adjoint).comp_left sumInl).comp_right sumSnd) |>.add
      (((hS.comp_left T).comp_left sumInr).comp_right sumFst)

/-- The identity-supported module is actually the original module. -/
def projectionIdentityRangeEquiv : HilbertModuleEquiv B E (ProjectionModule (AdjointableMap.id (B := B) (E := E))) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun := fun x => ⟨x, rfl⟩
          invFun := Subtype.val
          left_inv := fun _ => rfl
          right_inv := fun _ => Subtype.ext rfl
          map_add' := fun _ _ => Subtype.ext rfl
          map_smul' := fun _ _ => Subtype.ext rfl }
      norm_map' := fun _ => rfl }
  inner_map := fun _ _ => rfl

def juliaFredholmRangeEquiv (T : AdjointableMap B E F) (hT : ‖T‖ ≤ 1) :
    HilbertModuleEquiv B E (ProjectionModule (juliaFredholmProjection T)) :=
  projectionIdentityRangeEquiv.trans (projectionRangeEquiv AdjointableMap.id
    (juliaFredholmProjection T) (juliaFredholmColumn T) (juliaFredholmColumn_adjoint_comp_self T hT) rfl)

def juliaReferenceRangeEquiv : HilbertModuleEquiv B F
    (ProjectionModule (juliaReferenceProjection (B := B) (E := E) (F := F))) :=
  projectionIdentityRangeEquiv.trans (projectionRangeEquiv AdjointableMap.id
    juliaReferenceProjection sumInr sumSnd_comp_inr rfl)

@[simp] theorem juliaFredholmRangeEquiv_coe (T : AdjointableMap B E F) (hT : ‖T‖ ≤ 1) (x : E) :
    ((juliaFredholmRangeEquiv T hT x : ProjectionModule (juliaFredholmProjection T)) :
      HilbertModuleSum B E F) = juliaFredholmColumn T x := rfl

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem juliaReferenceRangeEquiv_coe (y : F) :
    ((juliaReferenceRangeEquiv (B := B) (E := E) y : ProjectionModule juliaReferenceProjection) :
      HilbertModuleSum B E F) = sumMk (0 : E) y := rfl

/-- The genuine supported QP map is exactly the original Fredholm map under
the constructed range unitaries. -/
theorem juliaProjectionCrossMap_intertwine (T : AdjointableMap B E F) (hT : ‖T‖ ≤ 1) (x : E) :
    projectionCrossMap (juliaFredholmProjection T) juliaReferenceProjection
      (juliaFredholmProjection_isStarProjection T hT) juliaReferenceProjection_isStarProjection
        (juliaFredholmRangeEquiv T hT x) = juliaReferenceRangeEquiv (T x) := by
  apply Subtype.ext
  rw [projectionCrossMap_coe, juliaFredholmRangeEquiv_coe, juliaReferenceRangeEquiv_coe,
    juliaReferenceProjection_apply, juliaFredholmColumn_apply, sumMk_snd]

/-- The supported adjoint PQ likewise becomes the actual adjoint T*. -/
theorem juliaProjectionCrossMap_adjoint_intertwine (T : AdjointableMap B E F) (hT : ‖T‖ ≤ 1) (y : F) :
    (projectionCrossMap (juliaFredholmProjection T) juliaReferenceProjection
      (juliaFredholmProjection_isStarProjection T hT) juliaReferenceProjection_isStarProjection).adjoint
        (juliaReferenceRangeEquiv y) = juliaFredholmRangeEquiv T hT (T.adjoint y) := by
  apply Subtype.ext
  rw [projectionCrossMap_adjoint, projectionCrossMap_coe, juliaReferenceRangeEquiv_coe,
    juliaFredholmRangeEquiv_coe]
  change juliaFredholmColumn T ((juliaFredholmColumn T).adjoint (sumMk (0 : E) y)) = _
  rw [juliaFredholmColumn_adjoint_apply, sumMk_fst, sumMk_snd, map_zero, zero_add]

end BC4lean.KKTheory
