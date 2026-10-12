import BC4lean.KasparovDirectSumIso
import BC4lean.OddKasparovCycleIso

/-! # Actual odd cycle direct-sum unitaries -/
noncomputable section
namespace BC4lean.KKTheory
variable {Γ A B E F G H : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G] [CompleteSpace G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H] [CompleteSpace H]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace OddKasparovCycleIso

/-- Direct sums of isomorphic cycles are isomorphic, including on different carrier types. -/
def directSum {c : OddKasparovCycle α β E} {d : OddKasparovCycle α β F}
    {k : OddKasparovCycle α β G} {l : OddKasparovCycle α β H}
    (u : OddKasparovCycleIso c k) (v : OddKasparovCycleIso d l) :
    OddKasparovCycleIso (c.directSum d) (k.directSum l) where
  moduleEquiv := u.moduleEquiv.sum v.moduleEquiv
  action_intertwine g x := by
    change (u.moduleEquiv.sum v.moduleEquiv) ((c.groupAction.sum d.groupAction).action g x) =
      (k.groupAction.sum l.groupAction).action g ((u.moduleEquiv.sum v.moduleEquiv) x)
    simp only [HilbertModuleEquiv.sum_apply, EquivariantHilbertModule.sum_action_apply,
      sumMk_fst, sumMk_snd]
    exact Prod.ext (u.action_intertwine g x.fst) (v.action_intertwine g x.snd)
  representation_intertwine a x := by
    change (u.moduleEquiv.sum v.moduleEquiv) (sumMap (c.representation a) (d.representation a) x) =
      sumMap (k.representation a) (l.representation a) ((u.moduleEquiv.sum v.moduleEquiv) x)
    simp only [HilbertModuleEquiv.sum_apply, sumMap_apply, sumMk_fst, sumMk_snd]
    exact Prod.ext (u.representation_intertwine a x.fst) (v.representation_intertwine a x.snd)
  operator_intertwine x := by
    change (u.moduleEquiv.sum v.moduleEquiv) (sumMap c.operator d.operator x) =
      sumMap k.operator l.operator ((u.moduleEquiv.sum v.moduleEquiv) x)
    simp only [HilbertModuleEquiv.sum_apply, sumMap_apply, sumMk_fst, sumMk_snd]
    exact Prod.ext (u.operator_intertwine x.fst) (v.operator_intertwine x.snd)

/-- Exchanging summands gives an actual equivariant graded cycle isomorphism. -/
def sumComm (c : OddKasparovCycle α β E) (d : OddKasparovCycle α β F) :
    OddKasparovCycleIso (c.directSum d) (d.directSum c) where
  moduleEquiv := HilbertModuleEquiv.sumSwapEquiv
  action_intertwine g x := by
    change HilbertModuleEquiv.sumSwapEquiv ((c.groupAction.sum d.groupAction).action g x) =
      (d.groupAction.sum c.groupAction).action g (HilbertModuleEquiv.sumSwapEquiv x)
    simp only [HilbertModuleEquiv.sumSwapEquiv_apply, EquivariantHilbertModule.sum_action_apply,
      sumMk_fst, sumMk_snd]
  representation_intertwine a x := by
    change HilbertModuleEquiv.sumSwapEquiv (sumMap (c.representation a) (d.representation a) x) =
      sumMap (d.representation a) (c.representation a) (HilbertModuleEquiv.sumSwapEquiv x)
    simp only [HilbertModuleEquiv.sumSwapEquiv_apply, sumMap_apply, sumMk_fst, sumMk_snd]
  operator_intertwine x := by
    change HilbertModuleEquiv.sumSwapEquiv (sumMap c.operator d.operator x) =
      sumMap d.operator c.operator (HilbertModuleEquiv.sumSwapEquiv x)
    simp only [HilbertModuleEquiv.sumSwapEquiv_apply, sumMap_apply, sumMk_fst, sumMk_snd]

/-- The two associations of three direct summands are genuinely isomorphic cycles. -/
def sumAssoc (c : OddKasparovCycle α β E) (d : OddKasparovCycle α β F) (k : OddKasparovCycle α β G) :
    OddKasparovCycleIso ((c.directSum d).directSum k) (c.directSum (d.directSum k)) where
  moduleEquiv := HilbertModuleEquiv.sumAssocEquiv
  action_intertwine g x := by
    change HilbertModuleEquiv.sumAssocEquiv
      (((c.groupAction.sum d.groupAction).sum k.groupAction).action g x) =
      (c.groupAction.sum (d.groupAction.sum k.groupAction)).action g
        (HilbertModuleEquiv.sumAssocEquiv x)
    simp only [HilbertModuleEquiv.sumAssocEquiv_apply, EquivariantHilbertModule.sum_action_apply,
      sumMk_fst, sumMk_snd]
  representation_intertwine a x := by
    change HilbertModuleEquiv.sumAssocEquiv
      (sumMap (sumMap (c.representation a) (d.representation a)) (k.representation a) x) =
      sumMap (c.representation a) (sumMap (d.representation a) (k.representation a))
        (HilbertModuleEquiv.sumAssocEquiv x)
    simp only [HilbertModuleEquiv.sumAssocEquiv_apply, sumMap_apply, sumMk_fst, sumMk_snd]
  operator_intertwine x := by
    change HilbertModuleEquiv.sumAssocEquiv (sumMap (sumMap c.operator d.operator) k.operator x) =
      sumMap c.operator (sumMap d.operator k.operator) (HilbertModuleEquiv.sumAssocEquiv x)
    simp only [HilbertModuleEquiv.sumAssocEquiv_apply, sumMap_apply, sumMk_fst, sumMk_snd]

end OddKasparovCycleIso
end BC4lean.KKTheory
