import BC4lean.GradedKasparovCycleIso

/-! # Genuinely graded cycles with their underlying Hilbert module bundled

The module universe `uE` is fixed explicitly, while the module type may vary.
Every object stores the actual normed, complex-linear, coefficient-module and
completeness structures, together with the full raw cycle on that module.
Isomorphism is witnessed by a genuine `GradedKasparovCycleIso`; this file constructs
its equivalence relation but does not construct a homotopy quotient or a group.
-/

noncomputable section

universe uΓ uA uB uE

namespace BC4lean.KKTheory

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]

/-- A raw cycle on an actual complete Hilbert module whose carrier lies in
the specified module universe `uE`. -/
structure BundledGradedKasparovCycle (α : CStarAlgebraAction Γ A)
    (β : CStarAlgebraAction Γ B) (δA : CStarGrading A) (δB : CStarGrading B) where
  carrier : Type uE
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [normedSpace : NormedSpace ℂ carrier]
  [opSMul : SMul Bᵐᵒᵖ carrier]
  [cstarModule : CStarModule Bᵐᵒᵖ carrier]
  [completeSpace : CompleteSpace carrier]
  cycle : GradedKasparovCycle α β δA δB carrier

attribute [instance] BundledGradedKasparovCycle.normedAddCommGroup
  BundledGradedKasparovCycle.normedSpace BundledGradedKasparovCycle.opSMul
  BundledGradedKasparovCycle.cstarModule BundledGradedKasparovCycle.completeSpace

namespace BundledGradedKasparovCycle

variable {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

instance instCoeSort : CoeSort (BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB) (Type uE) :=
  ⟨carrier⟩

/-- Bundle a raw cycle without replacing any of its module structures. -/
def of {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
    (c : GradedKasparovCycle α β δA δB E) : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB where
  carrier := E
  cycle := c

@[simp] theorem of_carrier {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
    (c : GradedKasparovCycle α β δA δB E) : (of c).carrier = E := rfl

@[simp] theorem of_cycle {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
    (c : GradedKasparovCycle α β δA δB E) : (of c).cycle = c := rfl

/-- Rebundling the stored cycle preserves its carrier and all stored structures. -/
@[simp] theorem of_storedCycle (c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB) :
    of c.cycle = c := by
  cases c
  rfl

/-- An actual varying-module isomorphism of two bundled raw cycles. -/
abbrev Iso (c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB) :=
  GradedKasparovCycleIso c.cycle d.cycle

/-- The identity bundled-cycle isomorphism uses the identity module equivalence. -/
def isoRefl (c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB) : Iso c c :=
  GradedKasparovCycleIso.refl c.cycle

/-- Invert the same genuine module equivalence and all its intertwining laws. -/
def isoSymm {c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB} (e : Iso c d) : Iso d c :=
  e.symm

/-- Compose actual cycle isomorphisms through the intermediate module. -/
def isoTrans {c d k : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB}
    (e : Iso c d) (f : Iso d k) : Iso c k := e.trans f

/-- Isomorphism means that a unitary equivalence intertwining all cycle data exists. -/
def Isomorphic (c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB) : Prop :=
  Nonempty (Iso c d)

@[refl] theorem isomorphic_refl (c : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB) :
    c.Isomorphic c := ⟨isoRefl c⟩

@[symm] theorem isomorphic_symm {c d : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB}
    (h : c.Isomorphic d) : d.Isomorphic c := by
  obtain ⟨e⟩ := h
  exact ⟨isoSymm e⟩

@[trans] theorem isomorphic_trans {c d k : BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB}
    (h : c.Isomorphic d) (h' : d.Isomorphic k) : c.Isomorphic k := by
  obtain ⟨e⟩ := h
  obtain ⟨f⟩ := h'
  exact ⟨isoTrans e f⟩

/-- The proved equivalence relation of genuine cycle isomorphism. -/
def isomorphismSetoid : Setoid (BundledGradedKasparovCycle.{uΓ, uA, uB, uE} α β δA δB) where
  r := Isomorphic
  iseqv := ⟨isomorphic_refl, isomorphic_symm, isomorphic_trans⟩

end BundledGradedKasparovCycle
end BC4lean.KKTheory
