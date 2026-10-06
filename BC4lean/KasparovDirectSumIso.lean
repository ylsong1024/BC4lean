import BC4lean.KasparovDirectSum
import BC4lean.KasparovCycleIso

/-! # Isomorphisms for Kasparov-cycle direct sums

The diagonal sum of module unitaries intertwines all cycle data. Exchanging
summands and reassociating three summands preserve the genuine coefficient-valued
Hilbert norm, and yield actual cycle isomorphisms on different carrier types.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {Γ A B E F G H : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H]

namespace HilbertModuleEquiv

/-- The diagonal sum of genuine Hilbert-module unitaries. -/
def sum (u : HilbertModuleEquiv B E G) (v : HilbertModuleEquiv B F H) :
    HilbertModuleEquiv B (HilbertModuleSum B E F) (HilbertModuleSum B G H) where
  linearIsometryEquiv := sumLinearIsometryEquiv u.linearIsometryEquiv v.linearIsometryEquiv
    (StarAlgEquiv.refl ℂ Bᵐᵒᵖ) u.inner_map v.inner_map
  inner_map x y := by
    change ⟪u x.fst, u y.fst⟫_(Bᵐᵒᵖ) + ⟪v x.snd, v y.snd⟫_(Bᵐᵒᵖ) =
      ⟪x.fst, y.fst⟫_(Bᵐᵒᵖ) + ⟪x.snd, y.snd⟫_(Bᵐᵒᵖ)
    rw [u.inner_map, v.inner_map]

@[simp] theorem sum_apply (u : HilbertModuleEquiv B E G) (v : HilbertModuleEquiv B F H)
    (x : HilbertModuleSum B E F) : u.sum v x = sumMk (u x.fst) (v x.snd) := rfl

/-- The summand exchange as a coefficient-inner-product-preserving module unitary. -/
def sumSwapEquiv : HilbertModuleEquiv B (HilbertModuleSum B E F) (HilbertModuleSum B F E) where
  linearIsometryEquiv := sumSwap
  inner_map := sumSwap_inner

@[simp] theorem sumSwapEquiv_apply (x : HilbertModuleSum B E F) :
    sumSwapEquiv x = sumMk x.snd x.fst := rfl

/-- Reassociation as a genuine Hilbert-module unitary. -/
def sumAssocEquiv : HilbertModuleEquiv B (HilbertModuleSum B (HilbertModuleSum B E F) G)
    (HilbertModuleSum B E (HilbertModuleSum B F G)) where
  linearIsometryEquiv := sumAssoc
  inner_map := sumAssoc_inner

@[simp] theorem sumAssocEquiv_apply (x : HilbertModuleSum B (HilbertModuleSum B E F) G) :
    sumAssocEquiv x = sumMk x.fst.fst (sumMk x.fst.snd x.snd) := rfl

end HilbertModuleEquiv

variable [Group Γ] [NonUnitalCStarAlgebra A]
  [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] [CompleteSpace H]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace KasparovCycleIso

/-- Direct sums of isomorphic cycles are isomorphic, including on different carrier types. -/
def directSum {c : KasparovCycle α β E} {d : KasparovCycle α β F}
    {k : KasparovCycle α β G} {l : KasparovCycle α β H}
    (u : KasparovCycleIso c k) (v : KasparovCycleIso d l) :
    KasparovCycleIso (c.directSum d) (k.directSum l) where
  moduleEquiv := u.moduleEquiv.sum v.moduleEquiv
  grading_intertwine x := by
    change (u.moduleEquiv.sum v.moduleEquiv) ((c.grading.sum d.grading).grading x) =
      (k.grading.sum l.grading).grading ((u.moduleEquiv.sum v.moduleEquiv) x)
    simp only [HilbertModuleEquiv.sum_apply, GradedHilbertModule.sum_grading_apply,
      sumMk_fst, sumMk_snd]
    exact Prod.ext (u.grading_intertwine x.fst) (v.grading_intertwine x.snd)
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
def sumComm (c : KasparovCycle α β E) (d : KasparovCycle α β F) :
    KasparovCycleIso (c.directSum d) (d.directSum c) where
  moduleEquiv := HilbertModuleEquiv.sumSwapEquiv
  grading_intertwine x := by
    change HilbertModuleEquiv.sumSwapEquiv ((c.grading.sum d.grading).grading x) =
      (d.grading.sum c.grading).grading (HilbertModuleEquiv.sumSwapEquiv x)
    simp only [HilbertModuleEquiv.sumSwapEquiv_apply, GradedHilbertModule.sum_grading_apply,
      sumMk_fst, sumMk_snd]
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
def sumAssoc (c : KasparovCycle α β E) (d : KasparovCycle α β F) (k : KasparovCycle α β G) :
    KasparovCycleIso ((c.directSum d).directSum k) (c.directSum (d.directSum k)) where
  moduleEquiv := HilbertModuleEquiv.sumAssocEquiv
  grading_intertwine x := by
    change HilbertModuleEquiv.sumAssocEquiv (((c.grading.sum d.grading).sum k.grading).grading x) =
      (c.grading.sum (d.grading.sum k.grading)).grading (HilbertModuleEquiv.sumAssocEquiv x)
    simp only [HilbertModuleEquiv.sumAssocEquiv_apply, GradedHilbertModule.sum_grading_apply,
      sumMk_fst, sumMk_snd]
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

end KasparovCycleIso
end BC4lean.KKTheory
