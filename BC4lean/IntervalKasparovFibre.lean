import BC4lean.IntervalModuleFibre
import BC4lean.IntervalKasparovHomotopy

/-! # Kasparov cycles on fibres of arbitrary interval modules

The underlying module is allowed to vary: it is an arbitrary complete right
Hilbert `C(X,B)`-module, not necessarily a module of continuous sections of
a fixed module. Evaluation uses its genuine radical-quotient completion.
Grading, group action, representation and Fredholm operator descend, and all
four compact defects remain compact by the proved rank-one/closure theorem.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace

variable {Γ A B X M : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

namespace GradedHilbertModule

/-- A genuine grading descends through evaluated null vectors and completion. -/
def fibre (γ : GradedHilbertModule (CStarGrading.trivial : CStarGrading C(X, B)) M)
    (t : X) : GradedHilbertModule (CStarGrading.trivial : CStarGrading B)
      (HilbertModuleFibre B M t) :=
  GradedHilbertModule.ofSelfadjointInvolution
    (hilbertModuleFibreOperator t γ.toAdjointable)
    (by
      change star (hilbertModuleFibreOperator t γ.toAdjointable) = _
      rw [← hilbertModuleFibreOperator_star]
      rfl)
    (by
      change hilbertModuleFibreOperator t γ.toAdjointable *
        hilbertModuleFibreOperator t γ.toAdjointable = 1
      rw [← hilbertModuleFibreOperator_mul, ← hilbertModuleFibreOperator_one]
      exact congrArg (hilbertModuleFibreOperator (B := B) t) γ.toAdjointable_sq)

@[simp] theorem fibre_grading_mk
    (γ : GradedHilbertModule (CStarGrading.trivial : CStarGrading C(X, B)) M)
    (t : X) (x : M) :
    (γ.fibre t).grading (hilbertModuleFibreMk (B := B) t x) =
      hilbertModuleFibreMk (B := B) t (γ.grading x) :=
  hilbertModuleFibreOperator_mk t γ.toAdjointable x

/-- Even degree persists on the completed fibre, by actual dense descent. -/
theorem isEven_fibre
    (γ : GradedHilbertModule (CStarGrading.trivial : CStarGrading C(X, B)) M)
    (t : X) {T : AdjointableMap C(X, B) M M} (hT : γ.IsEven γ T) :
    (γ.fibre t).IsEven (γ.fibre t) (hilbertModuleFibreOperator t T) := by
  intro z
  refine (hilbertModuleFibreMk_denseRange (B := B) (M := M) t).induction_on z ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro x
    simp only [hilbertModuleFibreOperator_mk, fibre_grading_mk]
    exact congrArg (hilbertModuleFibreMk (B := B) t) (hT x)

/-- Odd degree persists on the completed fibre, including its minus sign. -/
theorem isOdd_fibre
    (γ : GradedHilbertModule (CStarGrading.trivial : CStarGrading C(X, B)) M)
    (t : X) {T : AdjointableMap C(X, B) M M} (hT : γ.IsOdd γ T) :
    (γ.fibre t).IsOdd (γ.fibre t) (hilbertModuleFibreOperator t T) := by
  intro z
  refine (hilbertModuleFibreMk_denseRange (B := B) (M := M) t).induction_on z ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro x
    simp only [hilbertModuleFibreOperator_mk, fibre_grading_mk]
    simpa only [map_neg] using congrArg (hilbertModuleFibreMk (B := B) t) (hT x)

end GradedHilbertModule

namespace EquivariantHilbertModule

variable {β : CStarAlgebraAction Γ B}

omit [CompleteSpace M] in
/-- A parameter-fixed compatible action preserves the evaluated length,
because the actual coefficient automorphism is isometric. -/
theorem evaluated_formNorm_action
    (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
    (t : X) (g : Γ) (x : EvaluatedModuleSpace B M t) :
    PositiveModuleForm.formNorm (B := B)
      (evaluatedModuleOfOriginal B t (U.action g (evaluatedModuleToOriginal t x))) =
        PositiveModuleForm.formNorm (B := B) x := by
  have hinner :
      ⟪(evaluatedModuleOfOriginal B t (U.action g (evaluatedModuleToOriginal t x))),
        (evaluatedModuleOfOriginal B t (U.action g (evaluatedModuleToOriginal t x)))⟫_(Bᵐᵒᵖ) =
      opStarAlgEquiv (β.automorphism g) ⟪x, x⟫_(Bᵐᵒᵖ) := by
    simpa only [evaluatedModule_inner, evaluatedModule_to_of, opStarAlgEquiv_apply,
      CStarAlgebraAction.continuousSections, MonoidHom.coe_mk, OneHom.coe_mk,
      continuousCoefficientEquiv_apply,
      MulOpposite.unop_op] using
      congrArg (fun b : C(X, B)ᵐᵒᵖ => MulOpposite.op (MulOpposite.unop b t))
        (U.inner_action g (evaluatedModuleToOriginal t x) (evaluatedModuleToOriginal t x))
  simp only [PositiveModuleForm.formNorm, hinner, StarAlgEquiv.norm_map]

/-- The actual compatible group action descends to the genuine completed
fibres, including its identity and multiplication laws. -/
def fibre (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
    (t : X) : EquivariantHilbertModule β (HilbertModuleFibre B M t) where
  action :=
    { toFun g := hilbertModuleFibreLinearIsometryEquiv t (U.action g).toLinearEquiv
        (U.evaluated_formNorm_action t g)
      map_one' := by
        apply LinearIsometryEquiv.ext
        intro z
        refine (hilbertModuleFibreMk_denseRange (B := B) (M := M) t).induction_on z ?_ ?_
        · exact isClosed_eq (by fun_prop) (by fun_prop)
        · intro x
          simp only [hilbertModuleFibreLinearIsometryEquiv_mk,
            LinearIsometryEquiv.coe_one, id_eq]
          change hilbertModuleFibreMk (B := B) t (U.action 1 x) =
            hilbertModuleFibreMk (B := B) t x
          exact congrArg (hilbertModuleFibreMk (B := B) t) (U.one_apply x)
      map_mul' g h := by
        apply LinearIsometryEquiv.ext
        intro z
        refine (hilbertModuleFibreMk_denseRange (B := B) (M := M) t).induction_on z ?_ ?_
        · exact isClosed_eq (by fun_prop) (by fun_prop)
        · intro x
          simp only [LinearIsometryEquiv.coe_mul, Function.comp_apply,
            hilbertModuleFibreLinearIsometryEquiv_mk]
          change hilbertModuleFibreMk (B := B) t (U.action (g * h) x) =
            hilbertModuleFibreMk (B := B) t (U.action g (U.action h x))
          exact congrArg (hilbertModuleFibreMk (B := B) t) (U.mul_apply g h x) }
  inner_action g x y := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := M) t).induction_on₂
      (isClosed_eq (by fun_prop)
        ((StarAlgEquiv.isometry (opStarAlgEquiv (β.automorphism g))).continuous.comp
          CStarModule.continuous_inner))
      (fun ξ η => ?_) x y
    change ⟪hilbertModuleFibreLinearIsometryEquiv t (U.action g).toLinearEquiv
        (U.evaluated_formNorm_action t g) (hilbertModuleFibreMk (B := B) t ξ),
      hilbertModuleFibreLinearIsometryEquiv t (U.action g).toLinearEquiv
        (U.evaluated_formNorm_action t g) (hilbertModuleFibreMk (B := B) t η)⟫_(Bᵐᵒᵖ) = _
    simp only [hilbertModuleFibreLinearIsometryEquiv_mk, hilbertModuleFibre_inner_mk]
    simpa only [opStarAlgEquiv_apply, CStarAlgebraAction.continuousSections,
      MonoidHom.coe_mk, OneHom.coe_mk, continuousCoefficientEquiv_apply, MulOpposite.unop_op,
      LinearIsometryEquiv.coe_toLinearEquiv] using
      congrArg (fun b : C(X, B)ᵐᵒᵖ => MulOpposite.op (MulOpposite.unop b t))
        (U.inner_action g ξ η)

omit [CompleteSpace M] in
@[simp] theorem fibre_action_mk
    (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
    (t : X) (g : Γ) (x : M) :
    (U.fibre t).action g (hilbertModuleFibreMk (B := B) t x) =
      hilbertModuleFibreMk (B := B) t (U.action g x) :=
  hilbertModuleFibreLinearIsometryEquiv_mk t (U.action g).toLinearEquiv
    (U.evaluated_formNorm_action t g) x

/-- Compatibility of the action and grading persists under actual descent. -/
theorem preservesGrading_fibre
    (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
    (γ : GradedHilbertModule (CStarGrading.trivial : CStarGrading C(X, B)) M)
    (h : U.PreservesGrading γ) (t : X) :
    (U.fibre t).PreservesGrading (γ.fibre t) := by
  intro g z
  refine (hilbertModuleFibreMk_denseRange (B := B) (M := M) t).induction_on z ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro x
    simp only [fibre_action_mk, GradedHilbertModule.fibre_grading_mk]
    exact congrArg (hilbertModuleFibreMk (B := B) t) (h g x)

/-- Fibre operator descent intertwines the genuine conjugation actions. -/
theorem fibre_conjugateOperator
    (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
    (t : X) (g : Γ) (T : AdjointableMap C(X, B) M M) :
    (U.fibre t).conjugateOperator g (hilbertModuleFibreOperator t T) =
      hilbertModuleFibreOperator t (U.conjugateOperator g T) := by
  apply hilbertModuleFibreOperator_ext t
  intro x
  simp only [EquivariantHilbertModule.conjugateMap_apply,
    fibre_action_mk, hilbertModuleFibreOperator_mk]

end EquivariantHilbertModule

namespace KasparovCycle

variable {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

/-- Every genuine cycle on an arbitrary interval-coefficient module has a
genuine cycle on each of its evaluated radical-quotient completions. -/
def fibre (c : KasparovCycle α (β.continuousSections (X := X)) M) (t : X) :
    KasparovCycle α β (HilbertModuleFibre B M t) where
  countablyGenerated := c.countablyGenerated.fibre t
  grading := c.grading.fibre t
  groupAction := c.groupAction.fibre t
  grading_preserved := c.groupAction.preservesGrading_fibre c.grading c.grading_preserved t
  representation := (hilbertModuleFibreOperatorHom t).toNonUnitalStarAlgHom.comp c.representation
  representation_even a := c.grading.isEven_fibre t (c.representation_even a)
  representation_equivariant g a := by
    change (c.groupAction.fibre t).conjugateOperator g
      (hilbertModuleFibreOperator t (c.representation a)) =
        hilbertModuleFibreOperator t (c.representation (α.automorphism g a))
    rw [c.groupAction.fibre_conjugateOperator]
    exact congrArg (hilbertModuleFibreOperator (B := B) t) (c.representation_equivariant g a)
  operator := hilbertModuleFibreOperator t c.operator
  operator_odd := c.grading.isOdd_fibre t c.operator_odd
  selfadjoint_mod_compact a := by
    change IsModuleCompact ((hilbertModuleFibreOperator t c.operator -
      star (hilbertModuleFibreOperator t c.operator)) *
        hilbertModuleFibreOperator t (c.representation a))
    have h := (c.selfadjoint_mod_compact a).fibre t
    simpa only [hilbertModuleFibreOperator_mul, hilbertModuleFibreOperator_sub,
      hilbertModuleFibreOperator_star] using h
  square_mod_compact a := by
    change IsModuleCompact ((hilbertModuleFibreOperator t c.operator *
      hilbertModuleFibreOperator t c.operator - 1) *
        hilbertModuleFibreOperator t (c.representation a))
    have h := (c.square_mod_compact a).fibre t
    simpa only [hilbertModuleFibreOperator_mul, hilbertModuleFibreOperator_sub,
      hilbertModuleFibreOperator_one] using h
  commutator_compact a := by
    change IsModuleCompact (hilbertModuleFibreOperator t c.operator *
      hilbertModuleFibreOperator t (c.representation a) -
        hilbertModuleFibreOperator t (c.representation a) *
          hilbertModuleFibreOperator t c.operator)
    have h := (c.commutator_compact a).fibre t
    simpa only [hilbertModuleFibreOperator_mul, hilbertModuleFibreOperator_sub] using h
  equivariance_mod_compact g a := by
    change IsModuleCompact (((c.groupAction.fibre t).conjugateOperator g
      (hilbertModuleFibreOperator t c.operator) - hilbertModuleFibreOperator t c.operator) *
        hilbertModuleFibreOperator t (c.representation a))
    have h := (c.equivariance_mod_compact g a).fibre t
    simpa only [hilbertModuleFibreOperator_mul, hilbertModuleFibreOperator_sub,
      c.groupAction.fibre_conjugateOperator] using h

@[simp] theorem fibre_operator_mk
    (c : KasparovCycle α (β.continuousSections (X := X)) M) (t : X) (x : M) :
    (c.fibre t).operator (hilbertModuleFibreMk (B := B) t x) =
      hilbertModuleFibreMk (B := B) t (c.operator x) :=
  hilbertModuleFibreOperator_mk t c.operator x

@[simp] theorem fibre_representation_mk
    (c : KasparovCycle α (β.continuousSections (X := X)) M) (t : X) (a : A) (x : M) :
    (c.fibre t).representation a (hilbertModuleFibreMk (B := B) t x) =
      hilbertModuleFibreMk (B := B) t (c.representation a x) :=
  hilbertModuleFibreOperator_mk t (c.representation a) x

@[simp] theorem fibre_grading_mk
    (c : KasparovCycle α (β.continuousSections (X := X)) M) (t : X) (x : M) :
    (c.fibre t).grading.grading (hilbertModuleFibreMk (B := B) t x) =
      hilbertModuleFibreMk (B := B) t (c.grading.grading x) :=
  c.grading.fibre_grading_mk t x

@[simp] theorem fibre_action_mk
    (c : KasparovCycle α (β.continuousSections (X := X)) M) (t : X) (g : Γ) (x : M) :
    (c.fibre t).groupAction.action g (hilbertModuleFibreMk (B := B) t x) =
      hilbertModuleFibreMk (B := B) t (c.groupAction.action g x) :=
  c.groupAction.fibre_action_mk t g x

/-- Exact degeneracy also descends through actual fibre evaluation. -/
theorem isDegenerate_fibre
    (c : KasparovCycle α (β.continuousSections (X := X)) M) (hc : c.IsDegenerate) (t : X) :
    (c.fibre t).IsDegenerate := by
  constructor
  · intro a
    change (hilbertModuleFibreOperator t c.operator -
      star (hilbertModuleFibreOperator t c.operator)) *
        hilbertModuleFibreOperator t (c.representation a) = 0
    have h := congrArg (hilbertModuleFibreOperator (B := B) t) (hc.1 a)
    simpa only [hilbertModuleFibreOperator_mul, hilbertModuleFibreOperator_sub,
      hilbertModuleFibreOperator_star, hilbertModuleFibreOperator_zero] using h
  constructor
  · intro a
    change (hilbertModuleFibreOperator t c.operator *
      hilbertModuleFibreOperator t c.operator - 1) *
        hilbertModuleFibreOperator t (c.representation a) = 0
    have h := congrArg (hilbertModuleFibreOperator (B := B) t) (hc.2.1 a)
    simpa only [hilbertModuleFibreOperator_mul, hilbertModuleFibreOperator_sub,
      hilbertModuleFibreOperator_one, hilbertModuleFibreOperator_zero] using h
  constructor
  · intro a
    change hilbertModuleFibreOperator t c.operator *
      hilbertModuleFibreOperator t (c.representation a) -
        hilbertModuleFibreOperator t (c.representation a) *
          hilbertModuleFibreOperator t c.operator = 0
    have h := congrArg (hilbertModuleFibreOperator (B := B) t) (hc.2.2.1 a)
    simpa only [hilbertModuleFibreOperator_mul, hilbertModuleFibreOperator_sub,
      hilbertModuleFibreOperator_zero] using h
  · intro g a
    change ((c.groupAction.fibre t).conjugateOperator g
      (hilbertModuleFibreOperator t c.operator) - hilbertModuleFibreOperator t c.operator) *
        hilbertModuleFibreOperator t (c.representation a) = 0
    have h := congrArg (hilbertModuleFibreOperator (B := B) t) (hc.2.2.2 g a)
    simpa only [hilbertModuleFibreOperator_mul, hilbertModuleFibreOperator_sub,
      hilbertModuleFibreOperator_zero, c.groupAction.fibre_conjugateOperator] using h

end KasparovCycle

section OperatorPaths

open unitInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace KasparovOperatorHomotopy

variable {c : KasparovCycle α β E} {T₀ T₁ : AdjointableMap B E E}

/-- The general fibre construction applied to the actual interval cycle of
an operator path is isomorphic to the path cycle at every parameter. -/
def intervalFibreIso (h : KasparovOperatorHomotopy c T₀ T₁) (t : I) :
    KasparovCycleIso (h.intervalCycle.fibre t) (h.cycleAt t) where
  moduleEquiv := continuousSectionHilbertModuleFibreEquiv (B := B) t
  grading_intertwine z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := C(I, E)) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [KasparovCycle.fibre_grading_mk,
        continuousSectionHilbertModuleFibreEquiv_mk,
        continuousSectionHilbertModuleFibreEquiv_mk]
      rfl
  action_intertwine g z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := C(I, E)) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [KasparovCycle.fibre_action_mk,
        continuousSectionHilbertModuleFibreEquiv_mk,
        continuousSectionHilbertModuleFibreEquiv_mk]
      rfl
  representation_intertwine a z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := C(I, E)) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [KasparovCycle.fibre_representation_mk,
        continuousSectionHilbertModuleFibreEquiv_mk,
        continuousSectionHilbertModuleFibreEquiv_mk]
      rfl
  operator_intertwine z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := C(I, E)) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [KasparovCycle.fibre_operator_mk,
        continuousSectionHilbertModuleFibreEquiv_mk,
        continuousSectionHilbertModuleFibreEquiv_mk]
      rfl

/-- The source endpoint is identified by a genuine whole-cycle isomorphism. -/
def intervalFibreZeroIso (h : KasparovOperatorHomotopy c T₀ T₁) :
    KasparovCycleIso (h.intervalCycle.fibre 0) (c.withOperator T₀ h.source_conditions) := by
  simpa only [source_cycleAt] using h.intervalFibreIso 0

/-- The target endpoint is identified by a genuine whole-cycle isomorphism. -/
def intervalFibreOneIso (h : KasparovOperatorHomotopy c T₀ T₁) :
    KasparovCycleIso (h.intervalCycle.fibre 1) (c.withOperator T₁ h.target_conditions) := by
  simpa only [target_cycleAt] using h.intervalFibreIso 1

end KasparovOperatorHomotopy
end OperatorPaths
end BC4lean.KKTheory
