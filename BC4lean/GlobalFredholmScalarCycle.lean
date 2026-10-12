import BC4lean.FredholmJuliaProjection
import BC4lean.KasparovDirectSumIso

/-! # The actual scalar Fredholm cycle and its Julia relative-projection cycle

An actual rectangular map with both global compact Fredholm defects supplies
the scalar off-diagonal Kasparov cycle. If it is a contraction, the constructed
Julia projection pair gives an actual isomorphism of this cycle with its
supported relative-projection cycle. Arbitrary scalar-cycle support reduction,
contraction normalization, finite approximation and index invariance are not
assumed by this construction.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ B E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

/-- The genuine scalar cycle of a global rectangular Fredholm operator. -/
def globalFredholmScalarCycle (T : AdjointableMap B E F)
    (hSource : IsModuleCompact (1 - T.adjoint.comp T))
    (hTarget : IsModuleCompact (T.comp T.adjoint - 1))
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F) :
    KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B) (HilbertModuleSum B E F) where
  countablyGenerated := hE.sum hF
  grading := GradedHilbertModule.trivial.sum GradedHilbertModule.trivial.opposite
  groupAction := EquivariantHilbertModule.trivial
  grading_preserved := by intro g x; rfl
  representation := scalarModuleRepresentation
  representation_even := by
    intro c x
    exact (GradedHilbertModule.trivial.sum GradedHilbertModule.trivial.opposite).grading.map_smul c x
  representation_equivariant := by intro g c; ext x; rfl
  operator := offDiagonalAdjointable T
  operator_odd := offDiagonalAdjointable_odd T
  selfadjoint_mod_compact := by
    intro c
    rw [offDiagonalAdjointable_star, sub_self, zero_mul]
    exact IsModuleCompact.zero
  square_mod_compact := by
    intro c
    have hs : IsModuleCompact (T.adjoint.comp T - 1) := by
      simpa only [neg_sub] using hSource.neg
    have hh : IsModuleCompact (offDiagonalAdjointable T * offDiagonalAdjointable T - 1) := by
      rw [offDiagonalAdjointable_square, ← sumMap_one, ← sumMap_sub]
      exact hs.sumMap hTarget
    exact hh.comp_right (scalarModuleRepresentation c)
  commutator_compact := by
    intro c
    have hh : offDiagonalAdjointable T * scalarModuleRepresentation c -
        scalarModuleRepresentation c * offDiagonalAdjointable T = 0 := by
      ext x
      simp only [AdjointableMap.coe_sub_apply, AdjointableMap.mul_apply, scalarModuleRepresentation_apply]
      exact sub_eq_zero.mpr ((offDiagonalAdjointable T).toCLM.map_smul c x)
    rw [hh]
    exact IsModuleCompact.zero
  equivariance_mod_compact := by
    intro g c
    have hh : (EquivariantHilbertModule.trivial (Γ := Γ)).conjugateOperator g
        (offDiagonalAdjointable T) = offDiagonalAdjointable T := by ext x; rfl
    rw [hh, sub_self, zero_mul]
    exact IsModuleCompact.zero

/-- The two actual range unitaries identify all scalar-cycle data, including
the crossmaps QP=T and PQ=T* proved in the preceding operator construction. -/
def globalFredholmJuliaCycleIso (T : AdjointableMap B E F) (hT : ‖T‖ ≤ 1)
    (hSource : IsModuleCompact (1 - T.adjoint.comp T))
    (hTarget : IsModuleCompact (T.comp T.adjoint - 1))
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F) :
    KasparovCycleIso (globalFredholmScalarCycle (Γ := Γ) T hSource hTarget hE hF)
      (relativeProjectionCycle (Γ := Γ) (juliaFredholmProjection T) juliaReferenceProjection
        (juliaFredholmProjection_isStarProjection T hT) juliaReferenceProjection_isStarProjection
        (juliaFredholmProjection_difference_isModuleCompact T hT hSource hTarget) (hE.sum hF)) where
  moduleEquiv := (juliaFredholmRangeEquiv T hT).sum juliaReferenceRangeEquiv
  grading_intertwine x := by
    change sumMk (juliaFredholmRangeEquiv T hT x.fst) (juliaReferenceRangeEquiv (-x.snd)) =
      sumMk (juliaFredholmRangeEquiv T hT x.fst) (-(juliaReferenceRangeEquiv x.snd))
    rw [HilbertModuleEquiv.map_neg]
  action_intertwine _ _ := rfl
  representation_intertwine c x := by
    change ((juliaFredholmRangeEquiv T hT).sum juliaReferenceRangeEquiv)
      (scalarModuleRepresentation c x) = scalarModuleRepresentation c
        (((juliaFredholmRangeEquiv T hT).sum juliaReferenceRangeEquiv) x)
    simp only [scalarModuleRepresentation_apply, HilbertModuleEquiv.map_smul]
  operator_intertwine x := by
    change ((juliaFredholmRangeEquiv T hT).sum juliaReferenceRangeEquiv) (offDiagonalAdjointable T x) =
      offDiagonalAdjointable (projectionCrossMap (juliaFredholmProjection T) juliaReferenceProjection
        (juliaFredholmProjection_isStarProjection T hT) juliaReferenceProjection_isStarProjection)
        (((juliaFredholmRangeEquiv T hT).sum juliaReferenceRangeEquiv) x)
    simp only [HilbertModuleEquiv.sum_apply, offDiagonalAdjointable_apply, sumMk_fst, sumMk_snd]
    exact congrArg₂ (sumMk (B := B))
      (juliaProjectionCrossMap_adjoint_intertwine T hT x.snd).symm
      (juliaProjectionCrossMap_intertwine T hT x.fst).symm

end BC4lean.KKTheory
