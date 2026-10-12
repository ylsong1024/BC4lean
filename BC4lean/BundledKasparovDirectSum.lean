import BC4lean.BundledKasparovCycle
import BC4lean.KasparovDirectSumIso
import BC4lean.KasparovInverseRotation
import Mathlib.Algebra.Module.PUnit

/-! # Direct sums, opposites and the genuine zero bundled cycle

Every operation uses the actual stored module structures. The zero carrier is
the one-vector Hilbert module, and dropping that summand is an actual unitary
cycle isomorphism. Sum congruence, commutativity and associativity here concern
genuine cycle isomorphisms. No homotopy quotient or group is asserted.
-/

noncomputable section

universe uΓ uA uB uE

namespace BC4lean.KKTheory

open scoped InnerProductSpace

/-- The actual zero module, in the chosen module universe. -/
abbrev ZeroHilbertModule : Type uE := PUnit.{uE + 1}

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The zero module has the zero coefficient-valued inner product. -/
instance zeroHilbertModuleCStarModule : CStarModule Bᵐᵒᵖ ZeroHilbertModule.{uE} where
  inner _ _ := 0
  inner_add_right := by simp
  inner_self_nonneg := le_rfl
  inner_self := ⟨fun _ => Subsingleton.elim _ _, fun _ => rfl⟩
  inner_op_smul_right := by simp
  inner_smul_right_complex := by simp
  star_inner _ _ := star_zero _
  norm_eq_sqrt_norm_inner_self _ := by simp

/-- Every coefficient grading acts on the zero module by its unique isometry. -/
def zeroHilbertModuleGrading (δ : CStarGrading B) :
    GradedHilbertModule δ ZeroHilbertModule.{uE} where
  grading := LinearIsometryEquiv.refl ℂ ZeroHilbertModule
  involutive _ := rfl
  inner_grading _ _ := (map_zero _).symm

variable [Group Γ] [NonUnitalCStarAlgebra A]

/-- Every coefficient action is compatible with the unique zero-module action. -/
def zeroHilbertModuleAction (β : CStarAlgebraAction Γ B) :
    EquivariantHilbertModule β ZeroHilbertModule.{uE} where
  action := 1
  inner_action _ _ _ := (map_zero _).symm

/-- The actual zero cycle on a complete, countably generated zero Hilbert module. -/
def zeroKasparovCycle (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B) :
    KasparovCycle α β ZeroHilbertModule.{uE} :=
  KasparovCycle.zeroRepresentation isCountablyGeneratedModule_of_subsingleton
    (zeroHilbertModuleGrading CStarGrading.trivial) (zeroHilbertModuleAction β)
    (by intro g x; exact Subsingleton.elim _ _)

theorem zeroKasparovCycle_isDegenerate
    (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B) :
    (zeroKasparovCycle.{uΓ, uA, uB, uE} α β).IsDegenerate :=
  KasparovCycle.zeroRepresentation_isDegenerate _ _ _ _

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

namespace HilbertModuleEquiv

/-- Dropping the zero summand preserves the actual coefficient-valued Hilbert norm. -/
def sumZeroRight : HilbertModuleEquiv B (HilbertModuleSum B E ZeroHilbertModule.{uE}) E where
  linearIsometryEquiv :=
    { toFun := fun x => x.fst
      invFun := fun x => sumMk x 0
      left_inv := fun x => by
        apply Prod.ext
        · rfl
        · exact Subsingleton.elim _ _
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      norm_map' := fun x => by
        rw [norm_sum]
        change ‖x.fst‖ = Real.sqrt ‖⟪x.fst, x.fst⟫_(Bᵐᵒᵖ) + 0‖
        rw [add_zero]
        exact CStarModule.norm_eq_sqrt_norm_inner_self x.fst }
  inner_map x y := by
    change ⟪x.fst, y.fst⟫_(Bᵐᵒᵖ) = ⟪x.fst, y.fst⟫_(Bᵐᵒᵖ) + 0
    rw [add_zero]

@[simp] theorem sumZeroRight_apply (x : HilbertModuleSum B E ZeroHilbertModule.{uE}) :
    sumZeroRight x = x.fst := rfl

/-- Dropping a zero first summand is the composite of the genuine summand exchange and projection. -/
def sumZeroLeft : HilbertModuleEquiv B (HilbertModuleSum B ZeroHilbertModule.{uE} E) E :=
  (sumSwapEquiv (B := B) (E := ZeroHilbertModule) (F := E)).trans sumZeroRight

@[simp] theorem sumZeroLeft_apply (x : HilbertModuleSum B ZeroHilbertModule.{uE} E) :
    sumZeroLeft x = x.snd := rfl

end HilbertModuleEquiv

variable [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace KasparovCycleIso

/-- An actual cycle isomorphism after dropping the zero summand. -/
def sumZeroRight (c : KasparovCycle α β E) :
    KasparovCycleIso (c.directSum (zeroKasparovCycle α β)) c where
  moduleEquiv := HilbertModuleEquiv.sumZeroRight
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine a x := by
    change HilbertModuleEquiv.sumZeroRight
      (sumMap (c.representation a) ((zeroKasparovCycle α β).representation a) x) =
      c.representation a x.fst
    simp only [sumMap_apply, HilbertModuleEquiv.sumZeroRight_apply, sumMk_fst]
  operator_intertwine x := by
    change HilbertModuleEquiv.sumZeroRight
      (sumMap c.operator (zeroKasparovCycle α β).operator x) = c.operator x.fst
    simp only [sumMap_apply, HilbertModuleEquiv.sumZeroRight_apply, sumMk_fst]

/-- The zero first summand is removed by two genuine cycle isomorphisms. -/
def sumZeroLeft (c : KasparovCycle α β E) :
    KasparovCycleIso ((zeroKasparovCycle α β).directSum c) c :=
  (sumComm (zeroKasparovCycle α β) c).trans (sumZeroRight c)

/-- Taking opposites preserves all exact cycle intertwining laws. -/
def opposite {F : Type uE} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]
    {c : KasparovCycle α β E} {d : KasparovCycle α β F}
    (u : KasparovCycleIso c d) : KasparovCycleIso c.opposite d.opposite where
  moduleEquiv := u.moduleEquiv
  grading_intertwine x := by
    change u.moduleEquiv (-c.grading.grading x) = -d.grading.grading (u.moduleEquiv x)
    rw [HilbertModuleEquiv.map_neg, u.grading_intertwine]
  action_intertwine := u.action_intertwine
  representation_intertwine := u.representation_intertwine
  operator_intertwine x := by
    simp only [KasparovCycle.opposite_operator, AdjointableMap.coe_neg_apply,
      HilbertModuleEquiv.map_neg, u.operator_intertwine]

end KasparovCycleIso

namespace BundledKasparovCycle

/-- Direct sum with its actual coefficient-valued module norm and complete cycle data. -/
def directSum (c d : BundledKasparovCycle.{uΓ, uA, uB, uE} α β) :
    BundledKasparovCycle.{uΓ, uA, uB, uE} α β := of (c.cycle.directSum d.cycle)

/-- Opposite grading and Fredholm operator on the same stored module. -/
def opposite (c : BundledKasparovCycle.{uΓ, uA, uB, uE} α β) :
    BundledKasparovCycle.{uΓ, uA, uB, uE} α β := of c.cycle.opposite

/-- The bundled zero cycle has a genuine zero carrier and zero representation. -/
def zero (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B) :
    BundledKasparovCycle.{uΓ, uA, uB, uE} α β := of (zeroKasparovCycle α β)

/-- Isomorphisms act diagonally on direct sums of stored cycles. -/
def directSumIso {c d k l : BundledKasparovCycle.{uΓ, uA, uB, uE} α β}
    (u : c.Iso k) (v : d.Iso l) : (c.directSum d).Iso (k.directSum l) :=
  u.directSum v

/-- Commutativity is witnessed by the genuine summand-swap unitary. -/
def directSumCommIso (c d : BundledKasparovCycle.{uΓ, uA, uB, uE} α β) :
    (c.directSum d).Iso (d.directSum c) := KasparovCycleIso.sumComm c.cycle d.cycle

/-- Associativity is witnessed by the norm-preserving reassociation unitary. -/
def directSumAssocIso (c d k : BundledKasparovCycle.{uΓ, uA, uB, uE} α β) :
    ((c.directSum d).directSum k).Iso (c.directSum (d.directSum k)) :=
  KasparovCycleIso.sumAssoc c.cycle d.cycle k.cycle

/-- Adding the actual zero cycle preserves the cycle up to a genuine unitary isomorphism. -/
def directSumZeroRightIso (c : BundledKasparovCycle.{uΓ, uA, uB, uE} α β) :
    (c.directSum (zero α β)).Iso c := KasparovCycleIso.sumZeroRight c.cycle

/-- The zero first summand is also removed by an actual cycle isomorphism. -/
def directSumZeroLeftIso (c : BundledKasparovCycle.{uΓ, uA, uB, uE} α β) :
    ((zero α β).directSum c).Iso c := KasparovCycleIso.sumZeroLeft c.cycle

/-- Isomorphic cycles have isomorphic opposite cycles. -/
def oppositeIso {c d : BundledKasparovCycle.{uΓ, uA, uB, uE} α β}
    (u : c.Iso d) : c.opposite.Iso d.opposite := u.opposite

theorem directSum_isomorphic {c d k l : BundledKasparovCycle.{uΓ, uA, uB, uE} α β}
    (h : c.Isomorphic k) (h' : d.Isomorphic l) :
    (c.directSum d).Isomorphic (k.directSum l) := by
  obtain ⟨u⟩ := h
  obtain ⟨v⟩ := h'
  exact ⟨directSumIso u v⟩

theorem opposite_isomorphic {c d : BundledKasparovCycle.{uΓ, uA, uB, uE} α β}
    (h : c.Isomorphic d) : c.opposite.Isomorphic d.opposite := by
  obtain ⟨u⟩ := h
  exact ⟨oppositeIso u⟩

end BundledKasparovCycle
end BC4lean.KKTheory
