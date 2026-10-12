import BC4lean.ConeHilbertModule
import BC4lean.IntervalKasparovFibre
import BC4lean.BundledKasparovDirectSum

/-! # A genuine cone homotopy for degenerate Kasparov cycles

An exactly degenerate cycle acts by constant data on the actual cone of
sections vanishing at zero. All four defects are exactly zero there, so this
is a genuine cycle over `C([0,1],B)`. Its general fibre at zero is the actual
zero module and its general fibre at one is the original module, with
whole-cycle endpoint isomorphisms. Degenerate cycles are not declared zero
by adding an unproved relation.

The construction requires exact degeneracy. Constant compact defects of a
general cycle are not asserted compact on the cone module.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory

open scoped InnerProductSpace

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {E : Type uE}
  [Group Γ] [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- Actual evaluation at one on the closed cone module. -/
def coneEvaluationOne : ConeHilbertModule B E →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := fun x => x.1 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun x => by
      simp only [one_mul]
      change ‖x.val 1‖ ≤ ‖x‖
      exact x.val.norm_coe_le_norm 1)

omit [PartialOrder B] [StarOrderedRing B] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E] in
@[simp] theorem coneEvaluationOne_apply (x : ConeHilbertModule B E) :
    coneEvaluationOne x = x.1 1 := rfl

omit [PartialOrder B] [StarOrderedRing B] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E] in
theorem coneEvaluationOne_surjective : Function.Surjective (coneEvaluationOne (B := B) (E := E)) := by
  intro x
  refine ⟨coneGenerator (B := B) x, ?_⟩
  change (coneGenerator (B := B) x).val 1 = x
  exact coneGenerator_apply_one (B := B) x

/-- The fibre at one of the actual cone is the original Hilbert module. -/
def coneOneFibreEquiv :
    HilbertModuleEquiv B (HilbertModuleFibre B (ConeHilbertModule B E) (1 : unitInterval)) E :=
  hilbertModuleFibreEquivOfEvaluation 1 coneEvaluationOne
    (fun _ _ => rfl) coneEvaluationOne_surjective

@[simp] theorem coneOneFibreEquiv_mk (x : ConeHilbertModule B E) :
    coneOneFibreEquiv (hilbertModuleFibreMk (B := B) 1 x) = x.1 1 :=
  hilbertModuleFibreEquivOfEvaluation_mk 1 coneEvaluationOne _ _ x

/-- The fibre at zero of the actual cone is the actual zero Hilbert module. -/
def coneZeroFibreEquiv :
    HilbertModuleEquiv B (HilbertModuleFibre B (ConeHilbertModule B E) (0 : unitInterval))
      ZeroHilbertModule.{uE} :=
  hilbertModuleFibreEquivOfEvaluation 0 (0 : ConeHilbertModule B E →L[ℂ] ZeroHilbertModule.{uE})
    (fun x y => by
      change (0 : Bᵐᵒᵖ) = MulOpposite.op
        (MulOpposite.unop ⟪x.1 0, y.1 0⟫_(Bᵐᵒᵖ))
      simp only [ConeHilbertModule.apply_zero, CStarModule.inner_zero_left,
        MulOpposite.unop_zero, MulOpposite.op_zero])
    (fun x => ⟨0, Subsingleton.elim _ _⟩)

namespace GradedHilbertModule

/-- The actual grading acts pointwise on cone sections. -/
def cone (γ : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E) :
    GradedHilbertModule (CStarGrading.trivial : CStarGrading C(unitInterval, B))
      (ConeHilbertModule B E) :=
  GradedHilbertModule.ofSelfadjointInvolution (coneOperator γ.toAdjointable)
    (by rw [← coneOperator_adjoint]; rfl)
    (by rw [← coneOperator_comp, γ.toAdjointable_sq]; exact coneOperator_one)

omit [CompleteSpace E] in
@[simp] theorem cone_grading_apply
    (γ : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E)
    (x : ConeHilbertModule B E) (t : unitInterval) :
    ((γ.cone).grading x).1 t = γ.grading (x.1 t) := rfl

omit [CompleteSpace E] in
theorem isEven_cone
    (γ : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E)
    {T : AdjointableMap B E E} (hT : γ.IsEven γ T) :
    γ.cone.IsEven γ.cone (coneOperator T) := by
  intro x
  apply Subtype.ext
  ext t
  exact hT (x.1 t)

omit [CompleteSpace E] in
theorem isOdd_cone
    (γ : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E)
    {T : AdjointableMap B E E} (hT : γ.IsOdd γ T) :
    γ.cone.IsOdd γ.cone (coneOperator T) := by
  intro x
  apply Subtype.ext
  ext t
  exact hT (x.1 t)

end GradedHilbertModule

namespace EquivariantHilbertModule

variable {β : CStarAlgebraAction Γ B}

/-- A compatible action preserves vanishing at zero and acts pointwise on
the actual cone module. -/
def cone (U : EquivariantHilbertModule β E) :
    EquivariantHilbertModule (β.continuousSections (X := unitInterval)) (ConeHilbertModule B E) where
  action :=
    { toFun g := coneIsometryEquiv (B := B) (U.action g)
      map_one' := by
        apply LinearIsometryEquiv.ext
        intro x
        apply Subtype.ext
        ext t
        exact U.one_apply (x.1 t)
      map_mul' g h := by
        apply LinearIsometryEquiv.ext
        intro x
        apply Subtype.ext
        ext t
        exact U.mul_apply g h (x.1 t) }
  inner_action g x y := by
    apply MulOpposite.unop_injective
    ext t
    exact congrArg MulOpposite.unop (U.inner_action g (x.1 t) (y.1 t))

omit [CompleteSpace E] in
@[simp] theorem cone_action_apply (U : EquivariantHilbertModule β E)
    (g : Γ) (x : ConeHilbertModule B E) (t : unitInterval) :
    ((U.cone).action g x).1 t = U.action g (x.1 t) := rfl

omit [CompleteSpace E] in
theorem preservesGrading_cone (U : EquivariantHilbertModule β E)
    (γ : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E)
    (h : U.PreservesGrading γ) : U.cone.PreservesGrading γ.cone := by
  intro g x
  apply Subtype.ext
  ext t
  exact h g (x.1 t)

omit [CompleteSpace E] in
theorem cone_conjugateOperator (U : EquivariantHilbertModule β E) (g : Γ)
    (T : AdjointableMap B E E) :
    U.cone.conjugateOperator g (coneOperator T) = coneOperator (U.conjugateOperator g T) := by
  apply AdjointableMap.ext
  intro x
  apply Subtype.ext
  ext t
  rfl

end EquivariantHilbertModule

namespace KasparovCycle

variable {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

/-- An exactly degenerate cycle gives an actual interval cycle on the cone,
whose defects are proved zero rather than assumed compact pointwise. -/
def degenerateCone (c : KasparovCycle α β E) (hc : c.IsDegenerate) :
    KasparovCycle α (β.continuousSections (X := unitInterval)) (ConeHilbertModule B E) where
  countablyGenerated := cone_isCountablyGenerated c.countablyGenerated
  grading := c.grading.cone
  groupAction := c.groupAction.cone
  grading_preserved := c.groupAction.preservesGrading_cone c.grading c.grading_preserved
  representation := coneOperatorHom.toNonUnitalStarAlgHom.comp c.representation
  representation_even a := c.grading.isEven_cone (c.representation_even a)
  representation_equivariant g a := by
    change c.groupAction.cone.conjugateOperator g (coneOperator (c.representation a)) = _
    rw [c.groupAction.cone_conjugateOperator, c.representation_equivariant]
    rfl
  operator := coneOperator c.operator
  operator_odd := c.grading.isOdd_cone c.operator_odd
  selfadjoint_mod_compact a := by
    change IsModuleCompact ((coneOperator c.operator - star (coneOperator c.operator)) *
      coneOperator (c.representation a))
    have h := congrArg (coneOperator (B := B) (E := E) (F := E)) (hc.1 a)
    simp only [coneOperator_mul, coneOperator_sub, coneOperator_star, coneOperator_zero] at h
    rw [h]
    exact IsModuleCompact.zero
  square_mod_compact a := by
    change IsModuleCompact ((coneOperator c.operator * coneOperator c.operator - 1) *
      coneOperator (c.representation a))
    have h := congrArg (coneOperator (B := B) (E := E) (F := E)) (hc.2.1 a)
    simp only [coneOperator_mul, coneOperator_sub, coneOperator_one, coneOperator_zero] at h
    rw [h]
    exact IsModuleCompact.zero
  commutator_compact a := by
    change IsModuleCompact (coneOperator c.operator * coneOperator (c.representation a) -
      coneOperator (c.representation a) * coneOperator c.operator)
    have h := congrArg (coneOperator (B := B) (E := E) (F := E)) (hc.2.2.1 a)
    simp only [coneOperator_mul, coneOperator_sub, coneOperator_zero] at h
    rw [h]
    exact IsModuleCompact.zero
  equivariance_mod_compact g a := by
    change IsModuleCompact ((c.groupAction.cone.conjugateOperator g (coneOperator c.operator) -
      coneOperator c.operator) * coneOperator (c.representation a))
    rw [c.groupAction.cone_conjugateOperator]
    have h := congrArg (coneOperator (B := B) (E := E) (F := E)) (hc.2.2.2 g a)
    simp only [coneOperator_mul, coneOperator_sub, coneOperator_zero] at h
    rw [h]
    exact IsModuleCompact.zero

/-- The actual zero-endpoint fibre cycle is isomorphic to the genuine zero
cycle, by the unitary identification of the whole cone fibre. -/
def degenerateConeZeroFibreIso (c : KasparovCycle α β E) (hc : c.IsDegenerate) :
    KasparovCycleIso ((c.degenerateCone hc).fibre 0) (zeroKasparovCycle α β) where
  moduleEquiv := coneZeroFibreEquiv
  grading_intertwine _ := Subsingleton.elim _ _
  action_intertwine _ _ := Subsingleton.elim _ _
  representation_intertwine _ _ := Subsingleton.elim _ _
  operator_intertwine _ := Subsingleton.elim _ _

/-- Evaluation at one intertwines every part of the cycle data, giving the
actual original cycle as the target endpoint of the degenerate cone. -/
def degenerateConeOneFibreIso (c : KasparovCycle α β E) (hc : c.IsDegenerate) :
    KasparovCycleIso ((c.degenerateCone hc).fibre 1) c where
  moduleEquiv := coneOneFibreEquiv
  grading_intertwine z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := ConeHilbertModule B E) 1).induction_on
      z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [KasparovCycle.fibre_grading_mk, coneOneFibreEquiv_mk, coneOneFibreEquiv_mk]
      rfl
  action_intertwine g z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := ConeHilbertModule B E) 1).induction_on
      z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [KasparovCycle.fibre_action_mk, coneOneFibreEquiv_mk, coneOneFibreEquiv_mk]
      rfl
  representation_intertwine a z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := ConeHilbertModule B E) 1).induction_on
      z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [KasparovCycle.fibre_representation_mk, coneOneFibreEquiv_mk, coneOneFibreEquiv_mk]
      rfl
  operator_intertwine z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := ConeHilbertModule B E) 1).induction_on
      z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [KasparovCycle.fibre_operator_mk, coneOneFibreEquiv_mk, coneOneFibreEquiv_mk]
      rfl

end KasparovCycle
end BC4lean.KKTheory
