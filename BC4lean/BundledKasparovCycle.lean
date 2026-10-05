import BC4lean.KasparovCycleTransport

/-! # Raw Kasparov cycles with their underlying Hilbert module bundled

The module universe `uE` is fixed explicitly, while the module type may vary.
Every object stores the actual normed, complex-linear, coefficient-module and
completeness structures, together with the full raw cycle on that module.
Isomorphism is witnessed by a genuine `KasparovCycleIso`; this file constructs
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
structure BundledKasparovCycle (α : CStarAlgebraAction Γ A)
    (β : CStarAlgebraAction Γ B) where
  carrier : Type uE
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [normedSpace : NormedSpace ℂ carrier]
  [opSMul : SMul Bᵐᵒᵖ carrier]
  [cstarModule : CStarModule Bᵐᵒᵖ carrier]
  [completeSpace : CompleteSpace carrier]
  cycle : KasparovCycle α β carrier

attribute [instance] BundledKasparovCycle.normedAddCommGroup
  BundledKasparovCycle.normedSpace BundledKasparovCycle.opSMul
  BundledKasparovCycle.cstarModule BundledKasparovCycle.completeSpace

namespace BundledKasparovCycle

variable {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

instance instCoeSort : CoeSort (BundledKasparovCycle.{uΓ, uA, uB, uE} α β) (Type uE) :=
  ⟨carrier⟩

/-- Bundle a raw cycle without replacing any of its module structures. -/
def of {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
    (c : KasparovCycle α β E) : BundledKasparovCycle.{uΓ, uA, uB, uE} α β where
  carrier := E
  cycle := c

@[simp] theorem of_carrier {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
    (c : KasparovCycle α β E) : (of c).carrier = E := rfl

@[simp] theorem of_cycle {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
    (c : KasparovCycle α β E) : (of c).cycle = c := rfl

/-- Rebundling the stored cycle preserves its carrier and all stored structures. -/
@[simp] theorem of_storedCycle (c : BundledKasparovCycle.{uΓ, uA, uB, uE} α β) :
    of c.cycle = c := by
  cases c
  rfl

/-- An actual varying-module isomorphism of two bundled raw cycles. -/
abbrev Iso (c d : BundledKasparovCycle.{uΓ, uA, uB, uE} α β) :=
  KasparovCycleIso c.cycle d.cycle

/-- The identity bundled-cycle isomorphism uses the identity module equivalence. -/
def isoRefl (c : BundledKasparovCycle.{uΓ, uA, uB, uE} α β) : Iso c c :=
  KasparovCycleIso.refl c.cycle

/-- Invert the same genuine module equivalence and all its intertwining laws. -/
def isoSymm {c d : BundledKasparovCycle.{uΓ, uA, uB, uE} α β} (e : Iso c d) : Iso d c :=
  e.symm

/-- Compose actual cycle isomorphisms through the intermediate module. -/
def isoTrans {c d k : BundledKasparovCycle.{uΓ, uA, uB, uE} α β}
    (e : Iso c d) (f : Iso d k) : Iso c k := e.trans f

/-- Isomorphism means that a unitary equivalence intertwining all cycle data exists. -/
def Isomorphic (c d : BundledKasparovCycle.{uΓ, uA, uB, uE} α β) : Prop :=
  Nonempty (Iso c d)

@[refl] theorem isomorphic_refl (c : BundledKasparovCycle.{uΓ, uA, uB, uE} α β) :
    c.Isomorphic c := ⟨isoRefl c⟩

@[symm] theorem isomorphic_symm {c d : BundledKasparovCycle.{uΓ, uA, uB, uE} α β}
    (h : c.Isomorphic d) : d.Isomorphic c := by
  obtain ⟨e⟩ := h
  exact ⟨isoSymm e⟩

@[trans] theorem isomorphic_trans {c d k : BundledKasparovCycle.{uΓ, uA, uB, uE} α β}
    (h : c.Isomorphic d) (h' : d.Isomorphic k) : c.Isomorphic k := by
  obtain ⟨e⟩ := h
  obtain ⟨f⟩ := h'
  exact ⟨isoTrans e f⟩

/-- The proved equivalence relation of genuine cycle isomorphism. -/
def isomorphismSetoid : Setoid (BundledKasparovCycle.{uΓ, uA, uB, uE} α β) where
  r := Isomorphic
  iseqv := ⟨isomorphic_refl, isomorphic_symm, isomorphic_trans⟩

/-- Bundle unitary transport to a different carrier in the same module universe. -/
def transport (c : BundledKasparovCycle.{uΓ, uA, uB, uE} α β)
    {F : Type uE} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]
    (u : HilbertModuleEquiv B c F) : BundledKasparovCycle.{uΓ, uA, uB, uE} α β :=
  of (c.cycle.transport u)

/-- The bundled source and its transported cycle have the actual transport isomorphism. -/
def transportIso (c : BundledKasparovCycle.{uΓ, uA, uB, uE} α β)
    {F : Type uE} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]
    (u : HilbertModuleEquiv B c F) : Iso c (c.transport u) :=
  c.cycle.transportIso u

theorem isomorphic_transport (c : BundledKasparovCycle.{uΓ, uA, uB, uE} α β)
    {F : Type uE} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]
    (u : HilbertModuleEquiv B c F) : c.Isomorphic (c.transport u) :=
  ⟨c.transportIso u⟩

end BundledKasparovCycle
end BC4lean.KKTheory
