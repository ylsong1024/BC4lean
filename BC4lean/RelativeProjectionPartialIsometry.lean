import BC4lean.RelativeProjectionTransport
import BC4lean.AdjointableUnitaryHilbertModuleEquiv
import BC4lean.KasparovCompactPerturbation

/-! # A genuine compact-relative partial isometry gives the zero relative class

An actual rectangular partial isometry restricts to a coefficient-inner-product
unitary between the supported ranges. If it differs compactly from the cross
operator QP, the relative cycle has a genuine compact affine homotopy to the
exactly degenerate unitary cycle. Compactness and all endpoint conditions are
derived, not supplied as additional admissibility hypotheses.
-/

noncomputable section
universe uΓ uB uE
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {Γ : Type uΓ} {B : Type uB} {E : Type uE} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

omit [StarOrderedRing B] [CompleteSpace E] in
/-- Actual unitary equivalences have both inverse adjoint compositions. -/
theorem HilbertModuleEquiv.adjoint_comp_self_identity
    {F : Type uE} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] (U : HilbertModuleEquiv B E F) :
    U.toAdjointable.adjoint.comp U.toAdjointable = AdjointableMap.id := by
  ext x
  exact U.symm_apply_apply x

omit [StarOrderedRing B] [CompleteSpace E] in
/-- The actual unitary has the other inverse adjoint composition as well. -/
theorem HilbertModuleEquiv.comp_adjoint_identity
    {F : Type uE} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] (U : HilbertModuleEquiv B E F) :
    U.toAdjointable.comp U.toAdjointable.adjoint = AdjointableMap.id := by
  ext x
  exact U.apply_symm_apply x

omit [CompleteSpace E] in
/-- The restricted range unitary differs compactly from the actual crossmap. -/
theorem projectionRangeEquiv_cross_difference_isModuleCompact
    (P Q V : AdjointableMap B E E) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hVP : V.adjoint.comp V = P) (hVQ : V.comp V.adjoint = Q)
    (hc : IsModuleCompact (V - Q * P)) :
    IsModuleCompact ((projectionRangeEquiv P Q V hVP hVQ).toAdjointable -
      projectionCrossMap P Q hP hQ) := by
  let U := projectionRangeEquiv P Q V hVP hVQ
  have hEq : U.toAdjointable - projectionCrossMap P Q hP hQ =
      (projectionCorestrict Q hQ).comp ((V - Q * P).comp (projectionInclusion P hP)) := by
    apply AdjointableMap.ext
    intro x
    apply Subtype.ext
    dsimp only [U]
    simp only [AdjointableMap.coe_sub_apply, Submodule.coe_sub,
      HilbertModuleEquiv.toAdjointable_apply, projectionRangeEquiv_apply,
      projectionCrossMap_coe, AdjointableMap.comp_apply, projectionCorestrict_coe,
      projectionInclusion_apply, AdjointableMap.mul_apply]
    have hx : P (x : E) = (x : E) :=
      (mem_projectionFixedSubmodule P _).mp x.property
    have hQV : Q (V (x : E)) = V (x : E) := by
      have h := (mem_projectionFixedSubmodule Q _).mp (U x).property
      simpa only [U, projectionRangeEquiv_apply] using h
    have hQQ : Q (Q (x : E)) = Q (x : E) :=
      congrArg (fun T : AdjointableMap B E E => T (x : E)) hQ.isIdempotentElem.eq
    rw [Q.toCLM.map_sub, hx, hQV, hQQ]
  rw [hEq]
  exact (hc.comp_right (projectionInclusion P hP)).comp_left (projectionCorestrict Q hQ)

/-- Compact rectangular differences give compact differences of the actual
selfadjoint off-diagonal operators. -/
theorem relativeOffDiagonal_compact_difference
    {F G : Type uE} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]
    (S T : AdjointableMap B F G) (hc : IsModuleCompact (S - T)) :
    IsModuleCompact (offDiagonalAdjointable S - offDiagonalAdjointable T) := by
  have hAdj : (S - T).adjoint = S.adjoint - T.adjoint := by
    apply AdjointableMap.toCLM_injective
    rw [AdjointableMap.toCLM_sub]
    exact AdjointableMap.adjointCLM_sub S T
  have hEq : offDiagonalAdjointable S - offDiagonalAdjointable T =
      ((sumInl (B := B) (E := F) (F := G)).comp (S - T).adjoint).comp sumSnd +
        ((sumInr (B := B) (E := F) (F := G)).comp (S - T)).comp sumFst := by
    ext x
    apply Prod.ext <;>
      simp [offDiagonalAdjointable_apply, hAdj, AdjointableMap.comp_apply]
  rw [hEq]
  exact ((hc.adjoint.comp_left sumInl).comp_right sumSnd).add
    ((hc.comp_left sumInr).comp_right sumFst)

/-- The unitary off-diagonal endpoint has every raw operator condition,
proved from the actual unitary and scalar cycle data. -/
theorem relativeProjectionRangeUnitaryConditions
    (P Q : AdjointableMap B E E) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hc : IsModuleCompact (P - Q)) (hE : IsCountablyGeneratedModule B E)
    (U : HilbertModuleEquiv B (ProjectionModule P) (ProjectionModule Q)) :
    (relativeProjectionCycle (Γ := Γ) P Q hP hQ hc hE).OperatorConditions
      (offDiagonalAdjointable U.toAdjointable) where
  operator_odd := offDiagonalAdjointable_odd U.toAdjointable
  selfadjoint_mod_compact a := by
    rw [offDiagonalAdjointable_star, sub_self, zero_mul]
    exact IsModuleCompact.zero
  square_mod_compact a := by
    rw [offDiagonalAdjointable_square, U.adjoint_comp_self_identity, U.comp_adjoint_identity]
    change IsModuleCompact ((sumMap (1 : AdjointableMap B (ProjectionModule P)
      (ProjectionModule P)) (1 : AdjointableMap B (ProjectionModule Q) (ProjectionModule Q)) - 1) * _)
    rw [sumMap_one, sub_self, zero_mul]
    exact IsModuleCompact.zero
  commutator_compact a := by
    have hZero : offDiagonalAdjointable U.toAdjointable * scalarModuleRepresentation a -
        scalarModuleRepresentation a * offDiagonalAdjointable U.toAdjointable = 0 := by
      ext x
      simp only [AdjointableMap.coe_sub_apply, AdjointableMap.mul_apply,
        scalarModuleRepresentation_apply, AdjointableMap.coe_zero_apply]
      exact sub_eq_zero.mpr ((offDiagonalAdjointable U.toAdjointable).toCLM.map_smul a x)
    change IsModuleCompact (offDiagonalAdjointable U.toAdjointable * scalarModuleRepresentation a -
      scalarModuleRepresentation a * offDiagonalAdjointable U.toAdjointable)
    rw [hZero]
    exact IsModuleCompact.zero
  equivariance_mod_compact g a := by
    have hZero : (EquivariantHilbertModule.trivial (Γ := Γ)).conjugateOperator g
        (offDiagonalAdjointable U.toAdjointable) = offDiagonalAdjointable U.toAdjointable := by
      ext x
      rfl
    change IsModuleCompact (((EquivariantHilbertModule.trivial (Γ := Γ)).conjugateOperator g
      (offDiagonalAdjointable U.toAdjointable) - offDiagonalAdjointable U.toAdjointable) * _)
    rw [hZero, sub_self, zero_mul]
    exact IsModuleCompact.zero

/-- The actual unitary endpoint is exactly degenerate. -/
theorem relativeProjectionRangeUnitaryCycle_isDegenerate
    (P Q : AdjointableMap B E E) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hc : IsModuleCompact (P - Q)) (hE : IsCountablyGeneratedModule B E)
    (U : HilbertModuleEquiv B (ProjectionModule P) (ProjectionModule Q)) :
    ((relativeProjectionCycle (Γ := Γ) P Q hP hQ hc hE).withOperator
      (offDiagonalAdjointable U.toAdjointable)
      (relativeProjectionRangeUnitaryConditions P Q hP hQ hc hE U)).IsDegenerate := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    change (offDiagonalAdjointable U.toAdjointable - star (offDiagonalAdjointable U.toAdjointable)) * _ = 0
    rw [offDiagonalAdjointable_star, sub_self, zero_mul]
  · intro a
    change (offDiagonalAdjointable U.toAdjointable * offDiagonalAdjointable U.toAdjointable - 1) * _ = 0
    rw [offDiagonalAdjointable_square, U.adjoint_comp_self_identity, U.comp_adjoint_identity]
    change (sumMap (1 : AdjointableMap B (ProjectionModule P) (ProjectionModule P))
      (1 : AdjointableMap B (ProjectionModule Q) (ProjectionModule Q)) - 1) * _ = 0
    rw [sumMap_one, sub_self, zero_mul]
  · intro a
    change offDiagonalAdjointable U.toAdjointable * scalarModuleRepresentation a -
      scalarModuleRepresentation a * offDiagonalAdjointable U.toAdjointable = 0
    ext x
    simp only [AdjointableMap.coe_sub_apply, AdjointableMap.mul_apply,
      scalarModuleRepresentation_apply, AdjointableMap.coe_zero_apply]
    exact sub_eq_zero.mpr ((offDiagonalAdjointable U.toAdjointable).toCLM.map_smul a x)
  · intro g a
    have hZero : (EquivariantHilbertModule.trivial (Γ := Γ)).conjugateOperator g
        (offDiagonalAdjointable U.toAdjointable) = offDiagonalAdjointable U.toAdjointable := by
      ext x
      rfl
    change ((EquivariantHilbertModule.trivial (Γ := Γ)).conjugateOperator g
      (offDiagonalAdjointable U.toAdjointable) - offDiagonalAdjointable U.toAdjointable) * _ = 0
    rw [hZero, sub_self, zero_mul]

/-- A proved compact-relative partial isometry yields a genuine affine full
homotopy to the derived degenerate endpoint, hence zero full relative class. -/
theorem relativeProjection_class_zero_of_partialIsometry
    (P Q V : AdjointableMap B E E) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hcPQ : IsModuleCompact (P - Q)) (hE : IsCountablyGeneratedModule B E)
    (hVP : V.adjoint.comp V = P) (hVQ : V.comp V.adjoint = Q)
    (hcV : IsModuleCompact (V - Q * P)) :
    KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (relativeProjectionCycle (Γ := Γ) P Q hP hQ hcPQ hE)) = 0 := by
  let U := projectionRangeEquiv P Q V hVP hVQ
  let c := relativeProjectionCycle (Γ := Γ) P Q hP hQ hcPQ hE
  have hDiff := relativeOffDiagonal_compact_difference U.toAdjointable
    (projectionCrossMap P Q hP hQ)
    (projectionRangeEquiv_cross_difference_isModuleCompact P Q V hP hQ hVP hVQ hcV)
  let h := KasparovOperatorHomotopy.compactPerturbation c
    (offDiagonalAdjointable U.toAdjointable)
    (relativeProjectionRangeUnitaryConditions P Q hP hQ hcPQ hE U)
    (fun a => hDiff.comp_right (c.representation a))
  have hClass := KasparovHomotopyClass.mk_eq_of_full (FullKasparovHomotopy.ofOperatorHomotopy h)
  simpa only [KasparovCycle.withOperator_self] using hClass.trans
    (KasparovHomotopyClass.mk_eq_zero_of_degenerate _
      (relativeProjectionRangeUnitaryCycle_isDegenerate P Q hP hQ hcPQ hE U))

end BC4lean.KKTheory
