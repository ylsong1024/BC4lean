import BC4lean.RelativeProjectionTransport

/-! # Actual block sums of relative projection cycles

The range of a block projection is the true Hilbert-module sum of its ranges.
The middle-coordinate shuffle preserves the coefficient inner product and
identifies the relative cycle of a block pair with the direct sum of the two
relative cycles. This supplies additivity with the actual supported carriers.
-/

noncomputable section
universe uΓ uB uE
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {Γ : Type uΓ} {B : Type uB} {E F G H : Type uE} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H]

/-- The actual range of the actual block-diagonal projection. -/
def relativeProjectionSumRangeEquiv (P : AdjointableMap B E E) (R : AdjointableMap B F F) :
    HilbertModuleEquiv B (ProjectionModule (sumMap P R))
      (HilbertModuleSum B (ProjectionModule P) (ProjectionModule R)) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun := fun x => sumMk
            ⟨(x : HilbertModuleSum B E F).fst, by
              apply (mem_projectionFixedSubmodule P _).mpr
              have hx := (mem_projectionFixedSubmodule (sumMap P R) _).mp x.property
              simpa only [sumMap_apply, sumMk_fst] using congrArg Prod.fst hx⟩
            ⟨(x : HilbertModuleSum B E F).snd, by
              apply (mem_projectionFixedSubmodule R _).mpr
              have hx := (mem_projectionFixedSubmodule (sumMap P R) _).mp x.property
              simpa only [sumMap_apply, sumMk_snd] using congrArg Prod.snd hx⟩
          invFun := fun x => ⟨sumMk (x.fst : E) (x.snd : F), by
            apply (mem_projectionFixedSubmodule (sumMap P R) _).mpr
            rw [sumMap_apply, sumMk_fst, sumMk_snd,
              (mem_projectionFixedSubmodule P _).mp x.fst.property,
              (mem_projectionFixedSubmodule R _).mp x.snd.property]⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      norm_map' x := by
        change Real.sqrt ‖⟪(x : HilbertModuleSum B E F).fst,
            (x : HilbertModuleSum B E F).fst⟫_(Bᵐᵒᵖ) +
          ⟪(x : HilbertModuleSum B E F).snd,
            (x : HilbertModuleSum B E F).snd⟫_(Bᵐᵒᵖ)‖ = ‖x‖
        exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm }
  inner_map _ _ := rfl

/-- The first range coordinate is the actual ambient first coordinate. -/
theorem relativeProjectionSumRangeEquiv_fst (P : AdjointableMap B E E)
    (R : AdjointableMap B F F) (x : ProjectionModule (sumMap P R)) :
    (((relativeProjectionSumRangeEquiv P R) x).fst : E) =
      (x : HilbertModuleSum B E F).fst := rfl

/-- The second range coordinate is the actual ambient second coordinate. -/
theorem relativeProjectionSumRangeEquiv_snd (P : AdjointableMap B E E)
    (R : AdjointableMap B F F) (x : ProjectionModule (sumMap P R)) :
    (((relativeProjectionSumRangeEquiv P R) x).snd : F) =
      (x : HilbertModuleSum B E F).snd := rfl

/-- Exchanging the actual middle coordinates preserves the full coefficient form. -/
def relativeProjectionMiddleShuffle :
    HilbertModuleEquiv B (HilbertModuleSum B (HilbertModuleSum B E F) (HilbertModuleSum B G H))
      (HilbertModuleSum B (HilbertModuleSum B E G) (HilbertModuleSum B F H)) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun := fun x => sumMk (sumMk x.fst.fst x.snd.fst) (sumMk x.fst.snd x.snd.snd)
          invFun := fun x => sumMk (sumMk x.fst.fst x.snd.fst) (sumMk x.fst.snd x.snd.snd)
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      norm_map' x := by
        change Real.sqrt ‖(⟪x.fst.fst, x.fst.fst⟫_(Bᵐᵒᵖ) +
            ⟪x.snd.fst, x.snd.fst⟫_(Bᵐᵒᵖ)) +
          (⟪x.fst.snd, x.fst.snd⟫_(Bᵐᵒᵖ) +
            ⟪x.snd.snd, x.snd.snd⟫_(Bᵐᵒᵖ))‖ =
          Real.sqrt ‖(⟪x.fst.fst, x.fst.fst⟫_(Bᵐᵒᵖ) +
            ⟪x.fst.snd, x.fst.snd⟫_(Bᵐᵒᵖ)) +
          (⟪x.snd.fst, x.snd.fst⟫_(Bᵐᵒᵖ) +
            ⟪x.snd.snd, x.snd.snd⟫_(Bᵐᵒᵖ))‖
        congr 2
        abel }
  inner_map x y := by
    change (⟪x.fst.fst, y.fst.fst⟫_(Bᵐᵒᵖ) + ⟪x.snd.fst, y.snd.fst⟫_(Bᵐᵒᵖ)) +
      (⟪x.fst.snd, y.fst.snd⟫_(Bᵐᵒᵖ) + ⟪x.snd.snd, y.snd.snd⟫_(Bᵐᵒᵖ)) =
      (⟪x.fst.fst, y.fst.fst⟫_(Bᵐᵒᵖ) + ⟪x.fst.snd, y.fst.snd⟫_(Bᵐᵒᵖ)) +
      (⟪x.snd.fst, y.snd.fst⟫_(Bᵐᵒᵖ) + ⟪x.snd.snd, y.snd.snd⟫_(Bᵐᵒᵖ))
    abel

/-- The actual middle-coordinate shuffle on arbitrary vectors. -/
theorem relativeProjectionMiddleShuffle_apply
    (x : HilbertModuleSum B (HilbertModuleSum B E F) (HilbertModuleSum B G H)) :
    (relativeProjectionMiddleShuffle (B := B)) x =
      sumMk (sumMk x.fst.fst x.snd.fst) (sumMk x.fst.snd x.snd.snd) := rfl

/-- The genuine block projection laws follow from the actual block operator algebra. -/
theorem sumMap_isStarProjection {P : AdjointableMap B E E} {R : AdjointableMap B F F}
    (hP : IsStarProjection P) (hR : IsStarProjection R) : IsStarProjection (sumMap P R) := by
  apply isStarProjection_iff'.mpr
  constructor
  · rw [← sumMap_mul, hP.isIdempotentElem.eq, hR.isIdempotentElem.eq]
  · rw [← sumMap_star, hP.isSelfAdjoint.star_eq, hR.isSelfAdjoint.star_eq]

variable [CompleteSpace E] [CompleteSpace F]

/-- The supported block pair is identified with the actual direct-sum cycle. -/
def relativeProjectionSumCycleIso (P Q : AdjointableMap B E E) (R S : AdjointableMap B F F)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hR : IsStarProjection R) (hS : IsStarProjection S)
    (hc : IsModuleCompact (P - Q)) (hd : IsModuleCompact (R - S))
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F) :
    KasparovCycleIso
      (relativeProjectionCycle (Γ := Γ) (sumMap P R) (sumMap Q S)
        (sumMap_isStarProjection hP hR) (sumMap_isStarProjection hQ hS)
        (by rw [← sumMap_sub]; exact hc.sumMap hd) (hE.sum hF))
      ((relativeProjectionCycle (Γ := Γ) P Q hP hQ hc hE).directSum
        (relativeProjectionCycle (Γ := Γ) R S hR hS hd hF)) where
  moduleEquiv := ((relativeProjectionSumRangeEquiv P R).sum (relativeProjectionSumRangeEquiv Q S)).trans
    relativeProjectionMiddleShuffle
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine a x := by
    change ((((relativeProjectionSumRangeEquiv P R).sum
      (relativeProjectionSumRangeEquiv Q S)).trans relativeProjectionMiddleShuffle)
        (scalarModuleRepresentation a x)) =
      sumMap (scalarModuleRepresentation a) (scalarModuleRepresentation a)
        ((((relativeProjectionSumRangeEquiv P R).sum
          (relativeProjectionSumRangeEquiv Q S)).trans relativeProjectionMiddleShuffle) x)
    simp only [scalarModuleRepresentation_apply, sumMap_apply, ← sumMk_smul, sumMk_eta]
    exact HilbertModuleEquiv.map_smul _ a x
  operator_intertwine x := by
    change (((relativeProjectionSumRangeEquiv P R).sum (relativeProjectionSumRangeEquiv Q S)).trans
      relativeProjectionMiddleShuffle)
        (offDiagonalAdjointable (projectionCrossMap (sumMap P R) (sumMap Q S)
          (sumMap_isStarProjection hP hR) (sumMap_isStarProjection hQ hS)) x) =
      sumMap (offDiagonalAdjointable (projectionCrossMap P Q hP hQ))
        (offDiagonalAdjointable (projectionCrossMap R S hR hS))
        ((((relativeProjectionSumRangeEquiv P R).sum (relativeProjectionSumRangeEquiv Q S)).trans
          relativeProjectionMiddleShuffle) x)
    simp only [offDiagonalAdjointable_apply, projectionCrossMap_adjoint,
      HilbertModuleEquiv.trans_apply, HilbertModuleEquiv.sum_apply,
      relativeProjectionMiddleShuffle_apply, sumMk_fst, sumMk_snd, sumMap_apply]
    apply Prod.ext <;> apply Prod.ext <;> apply Subtype.ext
    all_goals simp only [sumMk_fst, sumMk_snd, relativeProjectionSumRangeEquiv_fst,
      relativeProjectionSumRangeEquiv_snd, projectionCrossMap_coe, sumMap_apply]

/-- Actual block sums add in the full homotopy group. -/
theorem relativeProjectionSum_class (P Q : AdjointableMap B E E) (R S : AdjointableMap B F F)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hR : IsStarProjection R) (hS : IsStarProjection S)
    (hc : IsModuleCompact (P - Q)) (hd : IsModuleCompact (R - S))
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F) :
    KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (relativeProjectionCycle (Γ := Γ) (sumMap P R) (sumMap Q S)
        (sumMap_isStarProjection hP hR) (sumMap_isStarProjection hQ hS)
        (by rw [← sumMap_sub]; exact hc.sumMap hd) (hE.sum hF))) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of (relativeProjectionCycle (Γ := Γ) P Q hP hQ hc hE)) +
        KasparovHomotopyClass.mk (BundledKasparovCycle.of (relativeProjectionCycle (Γ := Γ) R S hR hS hd hF)) :=
  (KasparovHomotopyClass.mk_eq_of_iso (relativeProjectionSumCycleIso P Q R S hP hQ hR hS hc hd hE hF)).trans
    (KasparovHomotopyClass.mk_directSum _ _)

end BC4lean.KKTheory
