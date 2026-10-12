import BC4lean.GradedKasparovCycleIso
import BC4lean.KasparovDirectSumIso
import BC4lean.BundledGradedKasparovCycle

/-! # Direct sums of genuine cycles with both algebra gradings

The true coefficient-valued Hilbert sum carries the diagonal semilinear
grading and action. The compact commutator uses the source grading in both
summands. Actual whole-cycle unitaries sum over different carriers.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory
variable {Γ A B E F G H : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G] [CompleteSpace G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H] [CompleteSpace H]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

def GradedKasparovCycle.directSum (c : GradedKasparovCycle α β δA δB E)
    (d : GradedKasparovCycle α β δA δB F) :
    GradedKasparovCycle α β δA δB (HilbertModuleSum B E F) where
  sourceAction_preservesGrading := c.sourceAction_preservesGrading
  coefficientAction_preservesGrading := c.coefficientAction_preservesGrading
  countablyGenerated := c.countablyGenerated.sum d.countablyGenerated
  grading := c.grading.sum d.grading
  groupAction := c.groupAction.sum d.groupAction
  grading_preserved := c.grading_preserved.sum d.grading_preserved
  representation := sumRepresentation c.representation d.representation
  representation_graded a x := by
    change (c.grading.sum d.grading).grading
      (sumMap (c.representation a) (d.representation a) x) =
      sumMap (c.representation (δA.automorphism a)) (d.representation (δA.automorphism a))
        ((c.grading.sum d.grading).grading x)
    simp only [GradedHilbertModule.sum_grading_apply, sumMap_apply, sumMk_fst, sumMk_snd]
    exact Prod.ext (c.representation_graded a x.fst) (d.representation_graded a x.snd)
  representation_equivariant g a := by
    change (c.groupAction.sum d.groupAction).conjugateOperator g
      (sumMap (c.representation a) (d.representation a)) =
      sumMap (c.representation (α.automorphism g a)) (d.representation (α.automorphism g a))
    rw [EquivariantHilbertModule.sum_conjugateOperator,
      c.representation_equivariant, d.representation_equivariant]
  operator := sumMap c.operator d.operator
  operator_odd := c.operator_odd.sumMap d.operator_odd
  selfadjoint_mod_compact a := by
    change IsModuleCompact ((sumMap c.operator d.operator - star (sumMap c.operator d.operator)) *
      sumMap (c.representation a) (d.representation a))
    rw [← sumMap_star, ← sumMap_sub, ← sumMap_mul]
    exact (c.selfadjoint_mod_compact a).sumMap (d.selfadjoint_mod_compact a)
  square_mod_compact a := by
    change IsModuleCompact ((sumMap c.operator d.operator * sumMap c.operator d.operator - 1) *
      sumMap (c.representation a) (d.representation a))
    rw [← sumMap_mul, ← (sumMap_one (B := B) (E := E) (F := F)), ← sumMap_sub, ← sumMap_mul]
    exact (c.square_mod_compact a).sumMap (d.square_mod_compact a)
  commutator_compact a := by
    change IsModuleCompact (sumMap c.operator d.operator * sumMap (c.representation a) (d.representation a) -
      sumMap (c.representation (δA.automorphism a)) (d.representation (δA.automorphism a)) *
        sumMap c.operator d.operator)
    rw [← sumMap_mul, ← sumMap_mul, ← sumMap_sub]
    exact (c.commutator_compact a).sumMap (d.commutator_compact a)
  equivariance_mod_compact g a := by
    change IsModuleCompact (((c.groupAction.sum d.groupAction).conjugateOperator g
      (sumMap c.operator d.operator) - sumMap c.operator d.operator) *
        sumMap (c.representation a) (d.representation a))
    rw [EquivariantHilbertModule.sum_conjugateOperator, ← sumMap_sub, ← sumMap_mul]
    exact (c.equivariance_mod_compact g a).sumMap (d.equivariance_mod_compact g a)

def GradedKasparovCycleIso.directSum
    {c : GradedKasparovCycle α β δA δB E} {d : GradedKasparovCycle α β δA δB F}
    {k : GradedKasparovCycle α β δA δB G} {l : GradedKasparovCycle α β δA δB H}
    (u : GradedKasparovCycleIso c k) (v : GradedKasparovCycleIso d l) :
    GradedKasparovCycleIso (c.directSum d) (k.directSum l) where
  moduleEquiv := u.moduleEquiv.sum v.moduleEquiv
  grading_intertwine x := by
    change (u.moduleEquiv.sum v.moduleEquiv) ((c.grading.sum d.grading).grading x) =
      (k.grading.sum l.grading).grading ((u.moduleEquiv.sum v.moduleEquiv) x)
    simp only [HilbertModuleEquiv.sum_apply, GradedHilbertModule.sum_grading_apply, sumMk_fst, sumMk_snd]
    exact Prod.ext (u.grading_intertwine x.fst) (v.grading_intertwine x.snd)
  action_intertwine g x := by
    change (u.moduleEquiv.sum v.moduleEquiv) ((c.groupAction.sum d.groupAction).action g x) =
      (k.groupAction.sum l.groupAction).action g ((u.moduleEquiv.sum v.moduleEquiv) x)
    simp only [HilbertModuleEquiv.sum_apply, EquivariantHilbertModule.sum_action_apply, sumMk_fst, sumMk_snd]
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

def BundledGradedKasparovCycle.directSum
    {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
    {δA : CStarGrading A} {δB : CStarGrading B}
    (c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB) :
    BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB :=
  BundledGradedKasparovCycle.of (c.cycle.directSum d.cycle)

end BC4lean.KKTheory
