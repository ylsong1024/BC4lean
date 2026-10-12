import BC4lean.IntervalMatchedCompactPairs
import BC4lean.IntervalKasparovReversal

/-! # Joining genuine arbitrary-module Kasparov interval cycles

The joining module is the actual closed space of endpoint-matched pairs. Its
grading, group action, representation and Fredholm operator are the genuine
diagonal restrictions. Every compact defect is compact by the actual matched
compact-pair theorem. The source's separable-coefficient assumption proves
countable generation of the matching module. The completed fibres on both
halves are identified with the original cycles, with all data intertwined.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace

variable {Γ A B M N : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(unitInterval, B)ᵐᵒᵖ M] [CStarModule C(unitInterval, B)ᵐᵒᵖ M]
  [NormedAddCommGroup N] [NormedSpace ℂ N]
  [SMul C(unitInterval, B)ᵐᵒᵖ N] [CStarModule C(unitInterval, B)ᵐᵒᵖ N]
  [CompleteSpace M] [CompleteSpace N]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace KasparovCycle

variable (c : KasparovCycle α (β.continuousSections (X := unitInterval)) M)
  (d : KasparovCycle α (β.continuousSections (X := unitInterval)) N)
  (e : KasparovCycleIso (c.fibre 1) (d.fibre 0))

theorem intervalJoinOperatorCompatible :
    IntervalMatchedOperatorCompatible e.moduleEquiv c.operator d.operator :=
  e.operator_intertwine

theorem intervalJoinRepresentationCompatible (a : A) :
    IntervalMatchedOperatorCompatible e.moduleEquiv (c.representation a) (d.representation a) :=
  e.representation_intertwine a

theorem intervalJoinGradingCompatible :
    IntervalMatchedOperatorCompatible e.moduleEquiv
      c.grading.toAdjointable d.grading.toAdjointable :=
  e.grading_intertwine

/-- The actual diagonal selfadjoint grading operator on the matching module. -/
def intervalJoinGradingOperator :
    AdjointableMap C(unitInterval, B)
      (IntervalMatchedModule e.moduleEquiv) (IntervalMatchedModule e.moduleEquiv) :=
  intervalMatchedOperator e.moduleEquiv c.grading.toAdjointable d.grading.toAdjointable
    (c.intervalJoinGradingCompatible d e)

theorem intervalJoinGradingOperator_selfadjoint :
    (c.intervalJoinGradingOperator d e).adjoint = c.intervalJoinGradingOperator d e := by
  apply AdjointableMap.ext
  intro z
  apply intervalMatchedModule_ext <;> rfl

theorem intervalJoinGradingOperator_sq :
    (c.intervalJoinGradingOperator d e).comp (c.intervalJoinGradingOperator d e) =
      AdjointableMap.id := by
  apply AdjointableMap.ext
  intro z
  apply intervalMatchedModule_ext
  · exact c.grading.grading_sq z.val.1
  · exact d.grading.grading_sq z.val.2

/-- The actual grading on the joined continuous-coefficient Hilbert module. -/
def intervalJoinGrading :
    GradedHilbertModule (CStarGrading.trivial : CStarGrading C(unitInterval, B))
      (IntervalMatchedModule e.moduleEquiv) :=
  GradedHilbertModule.ofSelfadjointInvolution (c.intervalJoinGradingOperator d e)
    (c.intervalJoinGradingOperator_selfadjoint d e) (c.intervalJoinGradingOperator_sq d e)

@[simp] theorem intervalJoinGrading_fst (z : IntervalMatchedModule e.moduleEquiv) :
    ((c.intervalJoinGrading d e).grading z).val.1 = c.grading.grading z.val.1 := rfl

@[simp] theorem intervalJoinGrading_snd (z : IntervalMatchedModule e.moduleEquiv) :
    ((c.intervalJoinGrading d e).grading z).val.2 = d.grading.grading z.val.2 := rfl

/-- The exact endpoint action intertwining preserves the matching condition. -/
theorem intervalJoinAction_matches (g : Γ) :
    ∀ z ∈ intervalMatchedSubmodule e.moduleEquiv,
      (c.groupAction.action g z.1, d.groupAction.action g z.2) ∈
        intervalMatchedSubmodule e.moduleEquiv := by
  intro z hz
  apply (mem_intervalMatchedSubmodule e.moduleEquiv _).mpr
  rw [← KasparovCycle.fibre_action_mk, e.action_intertwine,
    (mem_intervalMatchedSubmodule e.moduleEquiv z).mp hz, KasparovCycle.fibre_action_mk]

/-- The actual diagonal group isometry on the matching space. -/
def intervalJoinAction (g : Γ) :
    IntervalMatchedModule e.moduleEquiv ≃ₗᵢ[ℂ] IntervalMatchedModule e.moduleEquiv :=
  intervalMatchedLinearIsometryEquiv e.moduleEquiv
    (c.groupAction.action g) (d.groupAction.action g)
    (c.intervalJoinAction_matches d e g)
    (by
      simpa only [map_inv, LinearIsometryEquiv.inv_def] using
        c.intervalJoinAction_matches d e g⁻¹)

@[simp] theorem intervalJoinAction_fst (g : Γ) (z : IntervalMatchedModule e.moduleEquiv) :
    (c.intervalJoinAction d e g z).val.1 = c.groupAction.action g z.val.1 := rfl

@[simp] theorem intervalJoinAction_snd (g : Γ) (z : IntervalMatchedModule e.moduleEquiv) :
    (c.intervalJoinAction d e g z).val.2 = d.groupAction.action g z.val.2 := rfl

/-- The actual compatible diagonal group action, including its multiplication
laws and its pointwise coefficient-inner-product compatibility. -/
def intervalJoinGroupAction :
    EquivariantHilbertModule (β.continuousSections (X := unitInterval))
      (IntervalMatchedModule e.moduleEquiv) where
  action :=
    { toFun := c.intervalJoinAction d e
      map_one' := by
        apply LinearIsometryEquiv.ext
        intro z
        apply intervalMatchedModule_ext
        · exact c.groupAction.one_apply z.val.1
        · exact d.groupAction.one_apply z.val.2
      map_mul' g h := by
        apply LinearIsometryEquiv.ext
        intro z
        apply intervalMatchedModule_ext
        · exact c.groupAction.mul_apply g h z.val.1
        · exact d.groupAction.mul_apply g h z.val.2 }
  inner_action g x y := by
    apply MulOpposite.unop_injective
    apply continuousIntervalHalves_ext
    · intro t
      rw [intervalMatchedModule_inner_leftHalf]
      change MulOpposite.unop
        ⟪c.groupAction.action g x.val.1, c.groupAction.action g y.val.1⟫_
          (C(unitInterval, B)ᵐᵒᵖ) t =
        β.automorphism g (MulOpposite.unop ⟪x, y⟫_
          (C(unitInterval, B)ᵐᵒᵖ) (intervalLeftHalf t))
      rw [c.groupAction.inner_action, intervalMatchedModule_inner_leftHalf]
      rfl
    · intro t
      rw [intervalMatchedModule_inner_rightHalf]
      change MulOpposite.unop
        ⟪d.groupAction.action g x.val.2, d.groupAction.action g y.val.2⟫_
          (C(unitInterval, B)ᵐᵒᵖ) t =
        β.automorphism g (MulOpposite.unop ⟪x, y⟫_
          (C(unitInterval, B)ᵐᵒᵖ) (intervalRightHalf t))
      rw [d.groupAction.inner_action, intervalMatchedModule_inner_rightHalf]
      rfl

/-- The genuine diagonal representation on the actual matching module. -/
def intervalJoinRepresentation : A →⋆ₙₐ[ℂ]
    AdjointableMap C(unitInterval, B)
      (IntervalMatchedModule e.moduleEquiv) (IntervalMatchedModule e.moduleEquiv) where
  toFun a := intervalMatchedOperator e.moduleEquiv (c.representation a) (d.representation a)
    (c.intervalJoinRepresentationCompatible d e a)
  map_zero' := by
    apply AdjointableMap.ext
    intro z
    apply intervalMatchedModule_ext <;> simp [map_zero]
  map_add' a b := by
    apply AdjointableMap.ext
    intro z
    apply intervalMatchedModule_ext <;> simp [map_add]
  map_mul' a b := by
    apply AdjointableMap.ext
    intro z
    apply intervalMatchedModule_ext <;> simp [map_mul]
  map_smul' a b := by
    apply AdjointableMap.ext
    intro z
    apply intervalMatchedModule_ext <;> simp [map_smul]
  map_star' a := by
    apply AdjointableMap.ext
    intro z
    apply intervalMatchedModule_ext
    · exact congrArg (fun T => T z.val.1) (map_star c.representation a)
    · exact congrArg (fun T => T z.val.2) (map_star d.representation a)

@[simp] theorem intervalJoinRepresentation_fst (a : A)
    (z : IntervalMatchedModule e.moduleEquiv) :
    (c.intervalJoinRepresentation d e a z).val.1 = c.representation a z.val.1 := rfl

@[simp] theorem intervalJoinRepresentation_snd (a : A)
    (z : IntervalMatchedModule e.moduleEquiv) :
    (c.intervalJoinRepresentation d e a z).val.2 = d.representation a z.val.2 := rfl

/-- Exact boundary compatibility for the conjugated original Fredholm operators. -/
theorem intervalJoinConjugateOperatorCompatible (g : Γ) :
    IntervalMatchedOperatorCompatible e.moduleEquiv
      (c.groupAction.conjugateOperator g c.operator)
      (d.groupAction.conjugateOperator g d.operator) := by
  intro z
  rw [← c.groupAction.fibre_conjugateOperator,
    ← d.groupAction.fibre_conjugateOperator]
  change e.moduleEquiv
    ((c.fibre 1).groupAction.conjugateOperator g (c.fibre 1).operator z) =
    (d.fibre 0).groupAction.conjugateOperator g (d.fibre 0).operator (e.moduleEquiv z)
  simp only [EquivariantHilbertModule.conjugateMap_apply, e.action_intertwine,
    e.operator_intertwine]

variable [TopologicalSpace.SeparableSpace B]

/-- Join two genuine arbitrary-module interval cycles whose common endpoint
cycles are identified by an actual whole-cycle unitary. -/
def intervalJoined : KasparovCycle α (β.continuousSections (X := unitInterval))
    (IntervalMatchedModule e.moduleEquiv) where
  countablyGenerated := intervalMatchedModule_countablyGenerated e.moduleEquiv
    c.countablyGenerated d.countablyGenerated
  grading := c.intervalJoinGrading d e
  groupAction := c.intervalJoinGroupAction d e
  grading_preserved g z := by
    apply intervalMatchedModule_ext
    · exact c.grading_preserved g z.val.1
    · exact d.grading_preserved g z.val.2
  representation := c.intervalJoinRepresentation d e
  representation_even a z := by
    apply intervalMatchedModule_ext
    · exact c.representation_even a z.val.1
    · exact d.representation_even a z.val.2
  representation_equivariant g a := by
    apply AdjointableMap.ext
    intro z
    apply intervalMatchedModule_ext
    · exact congrArg (fun T => T z.val.1) (c.representation_equivariant g a)
    · exact congrArg (fun T => T z.val.2) (d.representation_equivariant g a)
  operator := intervalMatchedOperator e.moduleEquiv c.operator d.operator
    (c.intervalJoinOperatorCompatible d e)
  operator_odd z := by
    apply intervalMatchedModule_ext
    · exact c.operator_odd z.val.1
    · exact d.operator_odd z.val.2
  selfadjoint_mod_compact a := by
    have h := ((c.intervalJoinOperatorCompatible d e).sub
      (c.intervalJoinOperatorCompatible d e).adjoint).mul
        (c.intervalJoinRepresentationCompatible d e a)
    have hc := intervalMatchedOperator_isModuleCompact e.moduleEquiv
      ((c.operator - star c.operator) * c.representation a)
      ((d.operator - star d.operator) * d.representation a) h
      (c.selfadjoint_mod_compact a) (d.selfadjoint_mod_compact a)
    convert hc using 1
    apply AdjointableMap.ext
    intro z
    apply intervalMatchedModule_ext <;> rfl
  square_mod_compact a := by
    have h := (((c.intervalJoinOperatorCompatible d e).mul
      (c.intervalJoinOperatorCompatible d e)).sub
        (IntervalMatchedOperatorCompatible.one e.moduleEquiv)).mul
          (c.intervalJoinRepresentationCompatible d e a)
    have hc := intervalMatchedOperator_isModuleCompact e.moduleEquiv
      ((c.operator * c.operator - 1) * c.representation a)
      ((d.operator * d.operator - 1) * d.representation a) h
      (c.square_mod_compact a) (d.square_mod_compact a)
    convert hc using 1
    apply AdjointableMap.ext
    intro z
    apply intervalMatchedModule_ext <;> rfl
  commutator_compact a := by
    have h := ((c.intervalJoinOperatorCompatible d e).mul
      (c.intervalJoinRepresentationCompatible d e a)).sub
        ((c.intervalJoinRepresentationCompatible d e a).mul
          (c.intervalJoinOperatorCompatible d e))
    have hc := intervalMatchedOperator_isModuleCompact e.moduleEquiv
      (c.operator * c.representation a - c.representation a * c.operator)
      (d.operator * d.representation a - d.representation a * d.operator) h
      (c.commutator_compact a) (d.commutator_compact a)
    convert hc using 1
    apply AdjointableMap.ext
    intro z
    apply intervalMatchedModule_ext <;> rfl
  equivariance_mod_compact g a := by
    have h := ((c.intervalJoinConjugateOperatorCompatible d e g).sub
      (c.intervalJoinOperatorCompatible d e)).mul
        (c.intervalJoinRepresentationCompatible d e a)
    have hc := intervalMatchedOperator_isModuleCompact e.moduleEquiv
      ((c.groupAction.conjugateOperator g c.operator - c.operator) * c.representation a)
      ((d.groupAction.conjugateOperator g d.operator - d.operator) * d.representation a) h
      (c.equivariance_mod_compact g a) (d.equivariance_mod_compact g a)
    convert hc using 1
    apply AdjointableMap.ext
    intro z
    apply intervalMatchedModule_ext <;> rfl

end KasparovCycle

namespace KasparovCycleIso

variable [TopologicalSpace.SeparableSpace B]
  (c : KasparovCycle α (β.continuousSections (X := unitInterval)) M)
  (d : KasparovCycle α (β.continuousSections (X := unitInterval)) N)
  (e : KasparovCycleIso (c.fibre 1) (d.fibre 0))

set_option maxHeartbeats 4000000 in
/-- Every first-half fibre of the actual joined cycle is the corresponding
whole cycle fibre of the first original interval cycle. -/
def intervalJoinedLeftFibre (t : unitInterval) :
    KasparovCycleIso ((c.intervalJoined d e).fibre (intervalLeftHalf t)) (c.fibre t) where
  moduleEquiv := intervalMatchedLeftFibreEquiv e.moduleEquiv t
  grading_intertwine z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective
      (B := B) (M := IntervalMatchedModule e.moduleEquiv) (intervalLeftHalf t) z
    change intervalMatchedLeftFibreEquiv e.moduleEquiv t
      (((c.intervalJoinGrading d e).fibre (intervalLeftHalf t)).grading
        (hilbertModuleFibreMk (B := B) (intervalLeftHalf t) x)) =
      (c.grading.fibre t).grading
        (intervalMatchedLeftFibreEquiv e.moduleEquiv t
          (hilbertModuleFibreMk (B := B) (intervalLeftHalf t) x))
    rw [GradedHilbertModule.fibre_grading_mk (c.intervalJoinGrading d e) (intervalLeftHalf t) x,
      intervalMatchedLeftFibreEquiv_mk e.moduleEquiv t,
      intervalMatchedLeftFibreEquiv_mk e.moduleEquiv t,
      GradedHilbertModule.fibre_grading_mk c.grading t x.val.1]
    rfl
  action_intertwine g z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective
      (B := B) (M := IntervalMatchedModule e.moduleEquiv) (intervalLeftHalf t) z
    change intervalMatchedLeftFibreEquiv e.moduleEquiv t
      (((c.intervalJoinGroupAction d e).fibre (intervalLeftHalf t)).action g
        (hilbertModuleFibreMk (B := B) (intervalLeftHalf t) x)) =
      (c.groupAction.fibre t).action g
        (intervalMatchedLeftFibreEquiv e.moduleEquiv t
          (hilbertModuleFibreMk (B := B) (intervalLeftHalf t) x))
    rw [EquivariantHilbertModule.fibre_action_mk (c.intervalJoinGroupAction d e) (intervalLeftHalf t) g x,
      intervalMatchedLeftFibreEquiv_mk e.moduleEquiv t,
      intervalMatchedLeftFibreEquiv_mk e.moduleEquiv t,
      EquivariantHilbertModule.fibre_action_mk c.groupAction t g x.val.1]
    rfl
  representation_intertwine a z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective
      (B := B) (M := IntervalMatchedModule e.moduleEquiv) (intervalLeftHalf t) z
    rw [KasparovCycle.fibre_representation_mk (c.intervalJoined d e) (intervalLeftHalf t) a x,
      intervalMatchedLeftFibreEquiv_mk e.moduleEquiv t,
      intervalMatchedLeftFibreEquiv_mk e.moduleEquiv t,
      KasparovCycle.fibre_representation_mk c t a x.val.1]
    rfl
  operator_intertwine z :=
    intervalMatchedLeftFibreEquiv_operator e.moduleEquiv t c.operator d.operator
      (c.intervalJoinOperatorCompatible d e) z

set_option maxHeartbeats 4000000 in
/-- Every second-half fibre of the actual joined cycle is the corresponding
whole cycle fibre of the second original interval cycle. -/
def intervalJoinedRightFibre (t : unitInterval) :
    KasparovCycleIso ((c.intervalJoined d e).fibre (intervalRightHalf t)) (d.fibre t) where
  moduleEquiv := intervalMatchedRightFibreEquiv e.moduleEquiv t
  grading_intertwine z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective
      (B := B) (M := IntervalMatchedModule e.moduleEquiv) (intervalRightHalf t) z
    change intervalMatchedRightFibreEquiv e.moduleEquiv t
      (((c.intervalJoinGrading d e).fibre (intervalRightHalf t)).grading
        (hilbertModuleFibreMk (B := B) (intervalRightHalf t) x)) =
      (d.grading.fibre t).grading
        (intervalMatchedRightFibreEquiv e.moduleEquiv t
          (hilbertModuleFibreMk (B := B) (intervalRightHalf t) x))
    rw [GradedHilbertModule.fibre_grading_mk (c.intervalJoinGrading d e) (intervalRightHalf t) x,
      intervalMatchedRightFibreEquiv_mk e.moduleEquiv t,
      intervalMatchedRightFibreEquiv_mk e.moduleEquiv t,
      GradedHilbertModule.fibre_grading_mk d.grading t x.val.2]
    rfl
  action_intertwine g z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective
      (B := B) (M := IntervalMatchedModule e.moduleEquiv) (intervalRightHalf t) z
    change intervalMatchedRightFibreEquiv e.moduleEquiv t
      (((c.intervalJoinGroupAction d e).fibre (intervalRightHalf t)).action g
        (hilbertModuleFibreMk (B := B) (intervalRightHalf t) x)) =
      (d.groupAction.fibre t).action g
        (intervalMatchedRightFibreEquiv e.moduleEquiv t
          (hilbertModuleFibreMk (B := B) (intervalRightHalf t) x))
    rw [EquivariantHilbertModule.fibre_action_mk (c.intervalJoinGroupAction d e) (intervalRightHalf t) g x,
      intervalMatchedRightFibreEquiv_mk e.moduleEquiv t,
      intervalMatchedRightFibreEquiv_mk e.moduleEquiv t,
      EquivariantHilbertModule.fibre_action_mk d.groupAction t g x.val.2]
    rfl
  representation_intertwine a z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective
      (B := B) (M := IntervalMatchedModule e.moduleEquiv) (intervalRightHalf t) z
    rw [KasparovCycle.fibre_representation_mk (c.intervalJoined d e) (intervalRightHalf t) a x,
      intervalMatchedRightFibreEquiv_mk e.moduleEquiv t,
      intervalMatchedRightFibreEquiv_mk e.moduleEquiv t,
      KasparovCycle.fibre_representation_mk d t a x.val.2]
    rfl
  operator_intertwine z :=
    intervalMatchedRightFibreEquiv_operator e.moduleEquiv t c.operator d.operator
      (c.intervalJoinOperatorCompatible d e) z

end KasparovCycleIso

universe uΓ uA uB uE

namespace FullKasparovHomotopy

set_option maxHeartbeats 8000000 in
/-- Concatenation is a single genuine interval witness on the actual matched
Hilbert module. The boundary unitary is obtained by composing the two given
whole-cycle endpoint identifications through the common cycle. -/
def trans {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
    {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
    {c d k : BundledKasparovCycle.{uΓ, uA, uB, uE} α β}
    (h : FullKasparovHomotopy c d) (h' : FullKasparovHomotopy d k) :
    FullKasparovHomotopy c k where
  intervalCycle := BundledKasparovCycle.of
    (h.intervalCycle.cycle.intervalJoined h'.intervalCycle.cycle
      (h.targetIso.trans h'.sourceIso.symm))
  sourceIso := by
    have u := KasparovCycleIso.intervalJoinedLeftFibre h.intervalCycle.cycle
      h'.intervalCycle.cycle (h.targetIso.trans h'.sourceIso.symm) (0 : unitInterval)
    rw [intervalLeftHalf_zero] at u
    exact u.trans h.sourceIso
  targetIso := by
    have u := KasparovCycleIso.intervalJoinedRightFibre h.intervalCycle.cycle
      h'.intervalCycle.cycle (h.targetIso.trans h'.sourceIso.symm) (1 : unitInterval)
    rw [intervalRightHalf_one] at u
    exact u.trans h'.targetIso

end FullKasparovHomotopy

namespace BundledKasparovCycle

/-- For the source's separable coefficient algebras, the generated relation
is exactly the existence of one full arbitrary-module interval witness, as in
Definition 3.4. The proof uses actual reversal and actual matched-pair gluing. -/
theorem homotopic_iff_full {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
    {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
    {c d : BundledKasparovCycle.{uΓ, uA, uB, uE} α β} :
    c.Homotopic d ↔ Nonempty (FullKasparovHomotopy c d) := by
  constructor
  · intro h
    induction h with
    | rel c d h => exact homotopyStep_iff_full.mp h
    | refl c => exact ⟨FullKasparovHomotopy.refl c⟩
    | symm c d _ ih =>
        obtain ⟨h⟩ := ih
        exact ⟨h.symm⟩
    | trans c d k _ _ hcd hdk =>
        obtain ⟨h⟩ := hcd
        obtain ⟨h'⟩ := hdk
        exact ⟨h.trans h'⟩
  · rintro ⟨h⟩
    exact homotopic_of_full h

end BundledKasparovCycle

end BC4lean.KKTheory
