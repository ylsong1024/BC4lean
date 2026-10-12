import BC4lean.RelativeProjectionKasparovCycle
import BC4lean.KasparovDirectSumIso
import BC4lean.KasparovHomotopyGroup

/-! # Actual unitary transport of relative projection cycles

An ambient Hilbert-module unitary restricts to the genuine supported ranges of
transported projections. Its sum identifies the full relative cycle, including
the compressed cross-range operator. Compactness and countable generation of
the transported cycle are derived from the given cycle and actual unitary.
-/

noncomputable section
universe uΓ uB uE uF
namespace BC4lean.KKTheory

variable {Γ : Type uΓ} {B : Type uB} {E : Type uE} {F : Type uF} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

/-- The actual ambient unitary, restricted to the genuine transported range. -/
def projectionTransportRangeEquiv (U : HilbertModuleEquiv B E F) (P : AdjointableMap B E E) :
    HilbertModuleEquiv B (ProjectionModule P) (ProjectionModule (U.transport P)) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun := fun x => ⟨U (x : E), by
            change U (P (U.symm (U (x : E)))) = U (x : E)
            rw [U.symm_apply_apply, x.property]⟩
          invFun := fun y => ⟨U.symm (y : F), by
            apply U.injective
            rw [U.apply_symm_apply]
            exact y.property⟩
          left_inv := fun x => Subtype.ext (U.symm_apply_apply (x : E))
          right_inv := fun y => Subtype.ext (U.apply_symm_apply (y : F))
          map_add' := fun x y => Subtype.ext (U.map_add (x : E) (y : E))
          map_smul' := fun c x => Subtype.ext (U.map_smul c (x : E)) }
      norm_map' x := U.norm_map (x : E) }
  inner_map x y := U.inner_map (x : E) (y : E)

omit [StarOrderedRing B] in
@[simp] theorem projectionTransportRangeEquiv_coe
    (U : HilbertModuleEquiv B E F) (P : AdjointableMap B E E) (x : ProjectionModule P) :
    ((projectionTransportRangeEquiv U P x : ProjectionModule (U.transport P)) : F) = U (x : E) := rfl

omit [StarOrderedRing B] in
/-- Countable generation transports using the proved coefficient linearity. -/
theorem HilbertModuleEquiv.isCountablyGeneratedModule (U : HilbertModuleEquiv B E F)
    (hE : IsCountablyGeneratedModule B E) : IsCountablyGeneratedModule B F :=
  hE.map_linearIsometryEquiv U.linearIsometryEquiv id U.map_op_smul

omit [StarOrderedRing B] in
/-- Actual transport is a star-algebra equivalence and preserves projections. -/
theorem HilbertModuleEquiv.transport_isStarProjection (U : HilbertModuleEquiv B E F)
    {P : AdjointableMap B E E} (hP : IsStarProjection P) : IsStarProjection (U.transport P) :=
  hP.map U.transportStarAlgEquiv

/-- The compact difference is transported by the actual composition ideal laws. -/
theorem HilbertModuleEquiv.transport_difference_isModuleCompact (U : HilbertModuleEquiv B E F)
    {P Q : AdjointableMap B E E} (hc : IsModuleCompact (P - Q)) :
    IsModuleCompact (U.transport P - U.transport Q) := by
  rw [← U.transport_sub]
  exact U.transportMap_isModuleCompact U hc

variable [CompleteSpace E] [CompleteSpace F]

/-- The sum of the actual supported-range unitaries intertwines the whole cycle. -/
def relativeProjectionTransportCycleIso (U : HilbertModuleEquiv B E F)
    (P Q : AdjointableMap B E E) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hc : IsModuleCompact (P - Q)) (hE : IsCountablyGeneratedModule B E) :
    KasparovCycleIso (relativeProjectionCycle (Γ := Γ) P Q hP hQ hc hE)
      (relativeProjectionCycle (Γ := Γ) (U.transport P) (U.transport Q)
        (U.transport_isStarProjection hP) (U.transport_isStarProjection hQ)
        (U.transport_difference_isModuleCompact hc) (U.isCountablyGeneratedModule hE)) where
  moduleEquiv := (projectionTransportRangeEquiv U P).sum (projectionTransportRangeEquiv U Q)
  grading_intertwine x := by
    change sumMk (projectionTransportRangeEquiv U P x.fst)
      (projectionTransportRangeEquiv U Q (-x.snd)) =
      sumMk (projectionTransportRangeEquiv U P x.fst)
        (-(projectionTransportRangeEquiv U Q x.snd))
    rw [HilbertModuleEquiv.map_neg]
  action_intertwine _ _ := rfl
  representation_intertwine a x := by
    change ((projectionTransportRangeEquiv U P).sum (projectionTransportRangeEquiv U Q))
      (a • x) = a • (((projectionTransportRangeEquiv U P).sum
        (projectionTransportRangeEquiv U Q)) x)
    exact HilbertModuleEquiv.map_smul _ a x
  operator_intertwine x := by
    change ((projectionTransportRangeEquiv U P).sum (projectionTransportRangeEquiv U Q))
      (offDiagonalAdjointable (projectionCrossMap P Q hP hQ) x) =
      offDiagonalAdjointable (projectionCrossMap (U.transport P) (U.transport Q)
        (U.transport_isStarProjection hP) (U.transport_isStarProjection hQ))
        (((projectionTransportRangeEquiv U P).sum (projectionTransportRangeEquiv U Q)) x)
    simp only [HilbertModuleEquiv.sum_apply, offDiagonalAdjointable_apply, sumMk_fst, sumMk_snd,
      projectionCrossMap_adjoint]
    apply Prod.ext <;> apply Subtype.ext
    · change U (P (x.snd : E)) = U (P (U.symm (U (x.snd : E))))
      rw [U.symm_apply_apply]
    · change U (Q (x.fst : E)) = U (Q (U.symm (U (x.fst : E))))
      rw [U.symm_apply_apply]

variable {G : Type uE} [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G]
  [CStarModule Bᵐᵒᵖ G] [CompleteSpace G]

/-- The actual unitary transport preserves the full class. -/
theorem relativeProjectionTransport_class (U : HilbertModuleEquiv B E G)
    (P Q : AdjointableMap B E E) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hc : IsModuleCompact (P - Q)) (hE : IsCountablyGeneratedModule B E) :
    KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (relativeProjectionCycle (Γ := Γ) P Q hP hQ hc hE)) =
    KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (relativeProjectionCycle (Γ := Γ) (U.transport P) (U.transport Q)
        (U.transport_isStarProjection hP) (U.transport_isStarProjection hQ)
        (U.transport_difference_isModuleCompact hc) (U.isCountablyGeneratedModule hE))) :=
  KasparovHomotopyClass.mk_eq_of_iso (relativeProjectionTransportCycleIso U P Q hP hQ hc hE)

end BC4lean.KKTheory
