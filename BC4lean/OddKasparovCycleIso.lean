import BC4lean.KasparovCycle
import BC4lean.HilbertModuleEquiv

/-! # Genuine isomorphisms of odd equivariant Kasparov cycles -/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ A B E F G : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
  [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G]
  [CStarModule Bᵐᵒᵖ G] [CompleteSpace G]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

/-- One actual module unitary intertwines the entire odd cycle. -/
structure OddKasparovCycleIso (c : OddKasparovCycle α β E) (d : OddKasparovCycle α β F) where
  moduleEquiv : HilbertModuleEquiv B E F
  action_intertwine : ∀ g x,
    moduleEquiv (c.groupAction.action g x) = d.groupAction.action g (moduleEquiv x)
  representation_intertwine : ∀ a x,
    moduleEquiv (c.representation a x) = d.representation a (moduleEquiv x)
  operator_intertwine : ∀ x, moduleEquiv (c.operator x) = d.operator (moduleEquiv x)

namespace OddKasparovCycleIso
variable {c : OddKasparovCycle α β E} {d : OddKasparovCycle α β F}
  {k : OddKasparovCycle α β G}

instance instCoeFun : CoeFun (OddKasparovCycleIso c d) (fun _ => E → F) :=
  ⟨fun e => e.moduleEquiv⟩

def refl (c : OddKasparovCycle α β E) : OddKasparovCycleIso c c where
  moduleEquiv := HilbertModuleEquiv.refl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

def symm (e : OddKasparovCycleIso c d) : OddKasparovCycleIso d c where
  moduleEquiv := e.moduleEquiv.symm
  action_intertwine g y := by
    apply e.moduleEquiv.injective
    simpa only [HilbertModuleEquiv.apply_symm_apply] using
      (e.action_intertwine g (e.moduleEquiv.symm y)).symm
  representation_intertwine a y := by
    apply e.moduleEquiv.injective
    simpa only [HilbertModuleEquiv.apply_symm_apply] using
      (e.representation_intertwine a (e.moduleEquiv.symm y)).symm
  operator_intertwine y := by
    apply e.moduleEquiv.injective
    simpa only [HilbertModuleEquiv.apply_symm_apply] using
      (e.operator_intertwine (e.moduleEquiv.symm y)).symm

def trans (e : OddKasparovCycleIso c d) (f : OddKasparovCycleIso d k) :
    OddKasparovCycleIso c k where
  moduleEquiv := e.moduleEquiv.trans f.moduleEquiv
  action_intertwine g x := by
    simp only [HilbertModuleEquiv.trans_apply]
    rw [e.action_intertwine, f.action_intertwine]
  representation_intertwine a x := by
    simp only [HilbertModuleEquiv.trans_apply]
    rw [e.representation_intertwine, f.representation_intertwine]
  operator_intertwine x := by
    simp only [HilbertModuleEquiv.trans_apply]
    rw [e.operator_intertwine, f.operator_intertwine]

end OddKasparovCycleIso
end BC4lean.KKTheory
