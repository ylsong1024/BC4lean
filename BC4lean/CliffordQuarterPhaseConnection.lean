import BC4lean.CliffordQuarterPhase
import BC4lean.RectangularInteriorModuleTensorOperator
import Mathlib.Tactic.Module

/-! # Actual rectangular creator errors under the quarter-phase unitary

The full column creator is used for arbitrary two-component vectors. The
exact error formula contains the two original ordinary creator errors,
conjugated by genuine unitary phases. Consequently it proves compactness
without restricting the creator vector or assuming a product law.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordQuarterPhase
open CliffordExternalEvenBalancedTensor CliffordExternalEvenRepresentation

variable {C M F : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Cᵐᵒᵖ M] [CStarModule Cᵐᵒᵖ M]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace M] [CompleteSpace F]
  (K : GradedHilbertModule (CStarGrading.trivial : CStarGrading C) M)
  (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading C) F)

def column (T S : AdjointableMap C F M) : AdjointableMap C F (HilbertModuleSum C M M) :=
  sumInl.comp T + sumInr.comp S

omit [CompleteSpace M] [CompleteSpace F] in
@[simp] theorem column_apply [CompleteSpace M] [CompleteSpace F]
    (T S : AdjointableMap C F M) (y : F) :
    column T S y = sumMk (T y) (S y) := by
  simp only [column, AdjointableMap.coe_add_apply, AdjointableMap.comp_apply,
    sumInl_apply, sumInr_apply, sumMk_add, add_zero, zero_add]

omit [CompleteSpace M] [CompleteSpace F] in
theorem column_isModuleCompact [CompleteSpace M] [CompleteSpace F]
    {T S : AdjointableMap C F M}
    (hT : IsModuleCompact T) (hS : IsModuleCompact S) : IsModuleCompact (column T S) :=
  (hT.comp_left sumInl).add (hS.comp_left sumInr)

theorem upper_comp (T : AdjointableMap C F M)
    (hT : K.toAdjointable.comp T = T.comp J.toAdjointable) :
    (upper K).comp T = T.comp (upper J) := by
  ext y
  have h := congrArg (fun S : AdjointableMap C F M => S y) hT
  change K.grading (T y) = T (J.grading y) at h
  simp only [upper, plus, minus, CliffordOne.plusProjection, CliffordOne.minusProjection,
    AdjointableMap.comp_apply, AdjointableMap.coe_add_apply, AdjointableMap.coe_sub_apply,
    AdjointableMap.coe_smul_apply, AdjointableMap.one_apply,
    GradedHilbertModule.toAdjointable_apply, map_add, map_sub, map_smul, h]

theorem lower_comp (T : AdjointableMap C F M)
    (hT : K.toAdjointable.comp T = T.comp J.toAdjointable) :
    (lower K).comp T = T.comp (lower J) := by
  ext y
  have h := congrArg (fun S : AdjointableMap C F M => S y) hT
  change K.grading (T y) = T (J.grading y) at h
  simp only [lower, plus, minus, CliffordOne.plusProjection, CliffordOne.minusProjection,
    AdjointableMap.comp_apply, AdjointableMap.coe_add_apply, AdjointableMap.coe_sub_apply,
    AdjointableMap.coe_smul_apply, AdjointableMap.one_apply,
    GradedHilbertModule.toAdjointable_apply, map_add, map_sub, map_smul, h]

def phasedOperator (G : AdjointableMap C M M) :
    AdjointableMap C (HilbertModuleSum C M M) (HilbertModuleSum C M M) :=
  (sumEquiv K).transport (CliffordOddSourceCycle.operator G)

@[simp] theorem phasedOperator_apply (G : AdjointableMap C M M) (x : HilbertModuleSum C M M) :
    phasedOperator K G x = sumMk
      ((-Complex.I) • upper K (G (upper K x.snd)))
      (Complex.I • lower K (G (lower K x.fst))) := by
  simp only [phasedOperator, HilbertModuleEquiv.transport_apply, sumEquiv_apply,
    sumEquiv_symm_apply, CliffordOddSourceCycle.operator_apply,
    sumMk_fst, sumMk_snd, map_smul]

@[simp] theorem phasedOperator_star (G : AdjointableMap C M M) :
    star (phasedOperator K G) = phasedOperator K (star G) := by
  rw [phasedOperator, ← HilbertModuleEquiv.transport_star,
    CliffordOddSourceCycle.operator_star]
  rfl

theorem connection_formula (G : AdjointableMap C M M) (D : AdjointableMap C F F)
    (hD : J.IsOdd J D) (T S : AdjointableMap C F M)
    (hT : K.toAdjointable.comp T = T.comp J.toAdjointable)
    (hS : K.toAdjointable.comp S = S.comp J.toAdjointable) :
    (phasedOperator K G).comp (column T S) - (column S T).comp D =
      column (((-Complex.I) • upper K).comp ((G.comp S - S.comp D).comp (upper J)))
        ((Complex.I • lower K).comp ((G.comp T - T.comp D).comp (lower J))) := by
  have hUS := upper_comp K J S hS
  have hLT := lower_comp K J T hT
  have hcU : (upper K).comp (S.comp (D.comp (upper J))) = Complex.I • (S.comp D) := by
    rw [← AdjointableMap.comp_assoc, hUS, AdjointableMap.comp_assoc]
    change S.comp (upper J * D * upper J) = _
    rw [upper_odd J D hD]
    ext y
    simp only [AdjointableMap.comp_apply, AdjointableMap.coe_smul_apply, map_smul]
  have hcL : (lower K).comp (T.comp (D.comp (lower J))) = (-Complex.I) • (T.comp D) := by
    rw [← AdjointableMap.comp_assoc, hLT, AdjointableMap.comp_assoc]
    change T.comp (lower J * D * lower J) = _
    rw [lower_odd J D hD]
    ext y
    simp only [AdjointableMap.comp_apply, AdjointableMap.coe_smul_apply, map_smul]
  ext y
  have hUSy := congrArg (fun Q : AdjointableMap C F M => Q y) hUS
  have hLTy := congrArg (fun Q : AdjointableMap C F M => Q y) hLT
  have hcUy := congrArg (fun Q : AdjointableMap C F M => Q y) hcU
  have hcLy := congrArg (fun Q : AdjointableMap C F M => Q y) hcL
  simp only [AdjointableMap.comp_apply, AdjointableMap.coe_smul_apply] at hUSy hLTy hcUy hcLy
  apply Prod.ext
  · simp only [AdjointableMap.coe_sub_apply, AdjointableMap.comp_apply,
      phasedOperator_apply, column_apply, sumMk_fst, sumMk_snd,
      WithCStarModule.sub_fst, AdjointableMap.coe_smul_apply, map_sub]
    rw [hUSy]
    simp only [hcUy, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
  · simp only [AdjointableMap.coe_sub_apply, AdjointableMap.comp_apply,
      phasedOperator_apply, column_apply, sumMk_fst, sumMk_snd,
      WithCStarModule.sub_snd, AdjointableMap.coe_smul_apply, map_sub]
    rw [hLTy]
    simp only [hcLy, smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]

theorem connection_compact (G : AdjointableMap C M M) (D : AdjointableMap C F F)
    (hD : J.IsOdd J D) (T S : AdjointableMap C F M)
    (hT : K.toAdjointable.comp T = T.comp J.toAdjointable)
    (hS : K.toAdjointable.comp S = S.comp J.toAdjointable)
    (hcT : IsModuleCompact (G.comp T - T.comp D))
    (hcS : IsModuleCompact (G.comp S - S.comp D)) :
    IsModuleCompact ((phasedOperator K G).comp (column T S) - (column S T).comp D) := by
  rw [connection_formula K J G D hD T S hT hS]
  exact column_isModuleCompact
    ((hcS.comp_right (upper J)).comp_left ((-Complex.I) • upper K))
    ((hcT.comp_right (lower J)).comp_left (Complex.I • lower K))

end BC4lean.KKTheory.CliffordQuarterPhase
