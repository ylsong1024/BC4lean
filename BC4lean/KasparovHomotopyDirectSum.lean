import BC4lean.KasparovDirectSum
import BC4lean.KasparovOperatorHomotopy

/-! # Direct sums of fixed-module operator homotopies

Diagonal sum is continuous in the actual adjointable operator norms. Two
norm-continuous paths on fixed Kasparov modules therefore give a path on their
genuine Hilbert-module direct sum. Every path parameter satisfies all raw cycle
conditions; the endpoint operators are the specified diagonal endpoint sums.
-/

noncomputable section
namespace BC4lean.KKTheory
open unitInterval

variable {Γ A B E F G H : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H]

/-- Diagonal block sum as a bounded complex-linear map of operator parameters.
The product norm occurs only on the parameter space of operators. -/
def sumMapContinuousLinearMap :
    (AdjointableMap B E G × AdjointableMap B F H) →L[ℂ]
      AdjointableMap B (HilbertModuleSum B E F) (HilbertModuleSum B G H) :=
  ((AdjointableMap.compRightContinuousLinearMap (sumFst (B := B) (E := E) (F := F))).comp
      (AdjointableMap.compLeftContinuousLinearMap (sumInl (B := B) (E := G) (F := H)))).comp
    (ContinuousLinearMap.fst ℂ (AdjointableMap B E G) (AdjointableMap B F H)) +
    ((AdjointableMap.compRightContinuousLinearMap (sumSnd (B := B) (E := E) (F := F))).comp
      (AdjointableMap.compLeftContinuousLinearMap (sumInr (B := B) (E := G) (F := H)))).comp
      (ContinuousLinearMap.snd ℂ (AdjointableMap B E G) (AdjointableMap B F H))

@[simp] theorem sumMapContinuousLinearMap_apply
    (p : AdjointableMap B E G × AdjointableMap B F H) :
    sumMapContinuousLinearMap p = sumMap p.1 p.2 := rfl

theorem continuous_sumMap :
    Continuous (fun p : AdjointableMap B E G × AdjointableMap B F H => sumMap p.1 p.2) :=
  sumMapContinuousLinearMap.continuous

/-- Two actual operator paths have the indicated diagonal endpoint sums. -/
def sumMapPath {S₀ S₁ : AdjointableMap B E G} {T₀ T₁ : AdjointableMap B F H}
    (p : Path S₀ S₁) (q : Path T₀ T₁) : Path (sumMap S₀ T₀) (sumMap S₁ T₁) :=
  (p.prod q).map (continuous_sumMap (B := B) (E := E) (F := F) (G := G) (H := H))

@[simp] theorem sumMapPath_apply {S₀ S₁ : AdjointableMap B E G} {T₀ T₁ : AdjointableMap B F H}
    (p : Path S₀ S₁) (q : Path T₀ T₁) (t : I) : sumMapPath p q t = sumMap (p t) (q t) := rfl

variable [Group Γ] [NonUnitalCStarAlgebra A] [CompleteSpace E] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace KasparovCycle

/-- The operator conditions combine on the fixed genuine direct-sum module. -/
theorem OperatorConditions.directSum {c : KasparovCycle α β E} {d : KasparovCycle α β F}
    {S : AdjointableMap B E E} {T : AdjointableMap B F F}
    (hS : c.OperatorConditions S) (hT : d.OperatorConditions T) :
    (c.directSum d).OperatorConditions (sumMap S T) where
  operator_odd := hS.operator_odd.sumMap hT.operator_odd
  selfadjoint_mod_compact a := by
    change IsModuleCompact ((sumMap S T - star (sumMap S T)) *
      sumMap (c.representation a) (d.representation a))
    rw [← sumMap_star, ← sumMap_sub, ← sumMap_mul]
    exact (hS.selfadjoint_mod_compact a).sumMap (hT.selfadjoint_mod_compact a)
  square_mod_compact a := by
    change IsModuleCompact ((sumMap S T * sumMap S T - 1) *
      sumMap (c.representation a) (d.representation a))
    rw [← sumMap_mul, ← (sumMap_one (B := B) (E := E) (F := F)), ← sumMap_sub, ← sumMap_mul]
    exact (hS.square_mod_compact a).sumMap (hT.square_mod_compact a)
  commutator_compact a := by
    change IsModuleCompact (sumMap S T * sumMap (c.representation a) (d.representation a) -
      sumMap (c.representation a) (d.representation a) * sumMap S T)
    rw [← sumMap_mul, ← sumMap_mul, ← sumMap_sub]
    exact (hS.commutator_compact a).sumMap (hT.commutator_compact a)
  equivariance_mod_compact g a := by
    change IsModuleCompact (((c.groupAction.sum d.groupAction).conjugateOperator g (sumMap S T) -
      sumMap S T) * sumMap (c.representation a) (d.representation a))
    rw [EquivariantHilbertModule.sum_conjugateOperator, ← sumMap_sub, ← sumMap_mul]
    exact (hS.equivariance_mod_compact g a).sumMap (hT.equivariance_mod_compact g a)

end KasparovCycle

namespace KasparovOperatorHomotopy

/-- The pointwise diagonal sum of two actual fixed-module operator homotopies. -/
def directSum {c : KasparovCycle α β E} {d : KasparovCycle α β F}
    {S₀ S₁ : AdjointableMap B E E} {T₀ T₁ : AdjointableMap B F F}
    (h : KasparovOperatorHomotopy c S₀ S₁) (k : KasparovOperatorHomotopy d T₀ T₁) :
    KasparovOperatorHomotopy (c.directSum d) (sumMap S₀ T₀) (sumMap S₁ T₁) where
  path := sumMapPath h.path k.path
  conditions t := (h.conditions t).directSum (k.conditions t)

@[simp] theorem directSum_path_apply {c : KasparovCycle α β E} {d : KasparovCycle α β F}
    {S₀ S₁ : AdjointableMap B E E} {T₀ T₁ : AdjointableMap B F F}
    (h : KasparovOperatorHomotopy c S₀ S₁) (k : KasparovOperatorHomotopy d T₀ T₁) (t : I) :
    (h.directSum k).path t = sumMap (h.path t) (k.path t) := rfl

end KasparovOperatorHomotopy
end BC4lean.KKTheory
