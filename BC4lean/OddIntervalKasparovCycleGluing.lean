import BC4lean.IntervalMatchedCompactPairs
import BC4lean.IntervalKasparovReversal
import BC4lean.FullCliffordParityHomotopy

/-! # Joining genuine arbitrary-module odd interval cycles

The joining module is the actual closed space of endpoint-matched pairs.
The group action, representation and Fredholm operator are the genuine
restrictions, and all compact defects use the proved matched compact-pair
theorem. Separable coefficients prove countable generation. Concatenation
constructs one actual full interval witness, with whole-cycle fibre unitaries.
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

namespace OddKasparovCycle

variable (c : OddKasparovCycle α (β.continuousSections (X := unitInterval)) M)
  (d : OddKasparovCycle α (β.continuousSections (X := unitInterval)) N)
  (e : OddKasparovCycleIso (c.fibre 1) (d.fibre 0))

theorem intervalJoinOperatorCompatible :
    IntervalMatchedOperatorCompatible e.moduleEquiv c.operator d.operator :=
  e.operator_intertwine

theorem intervalJoinRepresentationCompatible (a : A) :
    IntervalMatchedOperatorCompatible e.moduleEquiv (c.representation a) (d.representation a) :=
  e.representation_intertwine a

/-- The exact endpoint action intertwining preserves the matching condition. -/
theorem intervalJoinAction_matches (g : Γ) :
    ∀ z ∈ intervalMatchedSubmodule e.moduleEquiv,
      (c.groupAction.action g z.1, d.groupAction.action g z.2) ∈
        intervalMatchedSubmodule e.moduleEquiv := by
  intro z hz
  apply (mem_intervalMatchedSubmodule e.moduleEquiv _).mpr
  rw [← OddKasparovCycle.fibre_action_mk, e.action_intertwine,
    (mem_intervalMatchedSubmodule e.moduleEquiv z).mp hz, OddKasparovCycle.fibre_action_mk]

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
    change intervalMatchedOperator e.moduleEquiv
      (c.representation (star a)) (d.representation (star a)) _ =
        (intervalMatchedOperator e.moduleEquiv (c.representation a) (d.representation a) _).adjoint
    rw [intervalMatchedOperator_adjoint]
    apply AdjointableMap.ext
    intro z
    apply intervalMatchedModule_ext
    · change c.representation (star a) z.val.1 = (c.representation a).adjoint z.val.1
      exact congrArg (fun T => T z.val.1) (map_star c.representation a)
    · change d.representation (star a) z.val.2 = (d.representation a).adjoint z.val.2
      exact congrArg (fun T => T z.val.2) (map_star d.representation a)

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
def intervalJoined : OddKasparovCycle α (β.continuousSections (X := unitInterval))
    (IntervalMatchedModule e.moduleEquiv) where
  countablyGenerated := intervalMatchedModule_countablyGenerated e.moduleEquiv
    c.countablyGenerated d.countablyGenerated
  groupAction := c.intervalJoinGroupAction d e
  representation := c.intervalJoinRepresentation d e
  representation_equivariant g a := by
    apply AdjointableMap.ext
    intro z
    apply intervalMatchedModule_ext
    · exact congrArg (fun T => T z.val.1) (c.representation_equivariant g a)
    · exact congrArg (fun T => T z.val.2) (d.representation_equivariant g a)
  operator := intervalMatchedOperator e.moduleEquiv c.operator d.operator
    (c.intervalJoinOperatorCompatible d e)
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

end OddKasparovCycle

namespace OddKasparovCycleIso

variable [TopologicalSpace.SeparableSpace B]
  (c : OddKasparovCycle α (β.continuousSections (X := unitInterval)) M)
  (d : OddKasparovCycle α (β.continuousSections (X := unitInterval)) N)
  (e : OddKasparovCycleIso (c.fibre 1) (d.fibre 0))

set_option maxHeartbeats 800000 in
/-- Every first-half fibre of the actual joined cycle is the corresponding
whole cycle fibre of the first original interval cycle. -/
def intervalJoinedLeftFibre (t : unitInterval) :
    OddKasparovCycleIso ((c.intervalJoined d e).fibre (intervalLeftHalf t)) (c.fibre t) where
  moduleEquiv := intervalMatchedLeftFibreEquiv e.moduleEquiv t
  action_intertwine g z := by
    have hNative (w : HilbertModuleFibre B (IntervalMatchedModule e.moduleEquiv)
        (intervalLeftHalf t)) :
        intervalMatchedLeftFibreEquiv e.moduleEquiv t
          (((c.intervalJoinGroupAction d e).fibre (intervalLeftHalf t)).action g w) =
        (c.groupAction.fibre t).action g (intervalMatchedLeftFibreEquiv e.moduleEquiv t w) := by
      obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective
        (B := B) (M := IntervalMatchedModule e.moduleEquiv) (intervalLeftHalf t) w
      calc
        intervalMatchedLeftFibreEquiv e.moduleEquiv t
            (((c.intervalJoinGroupAction d e).fibre (intervalLeftHalf t)).action g
              (hilbertModuleFibreMk (B := B) (intervalLeftHalf t) x)) =
            intervalMatchedLeftFibreEquiv e.moduleEquiv t
              (hilbertModuleFibreMk (B := B) (intervalLeftHalf t)
                ((c.intervalJoinGroupAction d e).action g x)) :=
          congrArg (intervalMatchedLeftFibreEquiv e.moduleEquiv t)
            (EquivariantHilbertModule.fibre_action_mk (c.intervalJoinGroupAction d e)
              (intervalLeftHalf t) g x)
        _ = hilbertModuleFibreMk (B := B) t (c.groupAction.action g x.val.1) :=
          intervalMatchedLeftFibreEquiv_mk e.moduleEquiv t
            ((c.intervalJoinGroupAction d e).action g x)
        _ = (c.groupAction.fibre t).action g
            (hilbertModuleFibreMk (B := B) t x.val.1) :=
          (EquivariantHilbertModule.fibre_action_mk c.groupAction t g x.val.1).symm
        _ = (c.groupAction.fibre t).action g
            (intervalMatchedLeftFibreEquiv e.moduleEquiv t
              (hilbertModuleFibreMk (B := B) (intervalLeftHalf t) x)) :=
          congrArg ((c.groupAction.fibre t).action g)
            (intervalMatchedLeftFibreEquiv_mk e.moduleEquiv t x).symm
    exact hNative z
  representation_intertwine a z :=
    intervalMatchedLeftFibreEquiv_operator e.moduleEquiv t
      (c.representation a) (d.representation a)
      (c.intervalJoinRepresentationCompatible d e a) z
  operator_intertwine z :=
    intervalMatchedLeftFibreEquiv_operator e.moduleEquiv t c.operator d.operator
      (c.intervalJoinOperatorCompatible d e) z

set_option maxHeartbeats 800000 in
/-- Every second-half fibre of the actual joined cycle is the corresponding
whole cycle fibre of the second original interval cycle. -/
def intervalJoinedRightFibre (t : unitInterval) :
    OddKasparovCycleIso ((c.intervalJoined d e).fibre (intervalRightHalf t)) (d.fibre t) where
  moduleEquiv := intervalMatchedRightFibreEquiv e.moduleEquiv t
  action_intertwine g z := by
    have hNative (w : HilbertModuleFibre B (IntervalMatchedModule e.moduleEquiv)
        (intervalRightHalf t)) :
        intervalMatchedRightFibreEquiv e.moduleEquiv t
          (((c.intervalJoinGroupAction d e).fibre (intervalRightHalf t)).action g w) =
        (d.groupAction.fibre t).action g (intervalMatchedRightFibreEquiv e.moduleEquiv t w) := by
      obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective
        (B := B) (M := IntervalMatchedModule e.moduleEquiv) (intervalRightHalf t) w
      calc
        intervalMatchedRightFibreEquiv e.moduleEquiv t
            (((c.intervalJoinGroupAction d e).fibre (intervalRightHalf t)).action g
              (hilbertModuleFibreMk (B := B) (intervalRightHalf t) x)) =
            intervalMatchedRightFibreEquiv e.moduleEquiv t
              (hilbertModuleFibreMk (B := B) (intervalRightHalf t)
                ((c.intervalJoinGroupAction d e).action g x)) :=
          congrArg (intervalMatchedRightFibreEquiv e.moduleEquiv t)
            (EquivariantHilbertModule.fibre_action_mk (c.intervalJoinGroupAction d e)
              (intervalRightHalf t) g x)
        _ = hilbertModuleFibreMk (B := B) t (d.groupAction.action g x.val.2) :=
          intervalMatchedRightFibreEquiv_mk e.moduleEquiv t
            ((c.intervalJoinGroupAction d e).action g x)
        _ = (d.groupAction.fibre t).action g
            (hilbertModuleFibreMk (B := B) t x.val.2) :=
          (EquivariantHilbertModule.fibre_action_mk d.groupAction t g x.val.2).symm
        _ = (d.groupAction.fibre t).action g
            (intervalMatchedRightFibreEquiv e.moduleEquiv t
              (hilbertModuleFibreMk (B := B) (intervalRightHalf t) x)) :=
          congrArg ((d.groupAction.fibre t).action g)
            (intervalMatchedRightFibreEquiv_mk e.moduleEquiv t x).symm
    exact hNative z
  representation_intertwine a z :=
    intervalMatchedRightFibreEquiv_operator e.moduleEquiv t
      (c.representation a) (d.representation a)
      (c.intervalJoinRepresentationCompatible d e a) z
  operator_intertwine z :=
    intervalMatchedRightFibreEquiv_operator e.moduleEquiv t c.operator d.operator
      (c.intervalJoinOperatorCompatible d e) z

end OddKasparovCycleIso

universe uΓ uA uB uE

namespace FullOddKasparovHomotopy

/-- Concatenation is a single genuine interval witness on the actual matched
Hilbert module. The boundary unitary is obtained by composing the two given
whole-cycle endpoint identifications through the common cycle. -/
def trans {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
    {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
    {c d k : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β}
    (h : FullOddKasparovHomotopy c d) (h' : FullOddKasparovHomotopy d k) :
    FullOddKasparovHomotopy c k where
  intervalCycle := BundledOddKasparovCycle.of
    (h.intervalCycle.cycle.intervalJoined h'.intervalCycle.cycle
      (h.targetIso.trans h'.sourceIso.symm))
  sourceIso := by
    let j := h.intervalCycle.cycle.intervalJoined h'.intervalCycle.cycle
      (h.targetIso.trans h'.sourceIso.symm)
    change OddKasparovCycleIso (j.fibre (0 : unitInterval)) c.cycle
    have u := OddKasparovCycleIso.intervalJoinedLeftFibre h.intervalCycle.cycle
      h'.intervalCycle.cycle (h.targetIso.trans h'.sourceIso.symm) (0 : unitInterval)
    have v : OddKasparovCycleIso (j.fibre (0 : unitInterval))
        (h.intervalCycle.cycle.fibre (0 : unitInterval)) :=
      Eq.mp (congrArg (fun t : unitInterval =>
        OddKasparovCycleIso (j.fibre t)
          (h.intervalCycle.cycle.fibre (0 : unitInterval))) intervalLeftHalf_zero) u
    exact v.trans h.sourceIso
  targetIso := by
    let j := h.intervalCycle.cycle.intervalJoined h'.intervalCycle.cycle
      (h.targetIso.trans h'.sourceIso.symm)
    change OddKasparovCycleIso (j.fibre (1 : unitInterval)) k.cycle
    have u := OddKasparovCycleIso.intervalJoinedRightFibre h.intervalCycle.cycle
      h'.intervalCycle.cycle (h.targetIso.trans h'.sourceIso.symm) (1 : unitInterval)
    have v : OddKasparovCycleIso (j.fibre (1 : unitInterval))
        (h'.intervalCycle.cycle.fibre (1 : unitInterval)) :=
      Eq.mp (congrArg (fun t : unitInterval =>
        OddKasparovCycleIso (j.fibre t)
          (h'.intervalCycle.cycle.fibre (1 : unitInterval))) intervalRightHalf_one) u
    exact v.trans h'.targetIso

end FullOddKasparovHomotopy

end BC4lean.KKTheory
