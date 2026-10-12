import BC4lean.KasparovHomotopyRelation
import BC4lean.IntervalModuleFibreNorm

/-! # Reversal of a genuine arbitrary-module interval homotopy

Precomposition with `t ↦ 1 - t` is an actual involutive star-automorphism of
the possibly nonunital continuous coefficient algebra. Twisting an arbitrary
interval module by this automorphism preserves its existing norm and replaces
its coefficient-valued inner product by the reversed coefficient function.
Adjointable maps and actual rank-one maps transport isometrically; compactness
then follows from the genuine operator-norm closure.

The completed evaluated fibre at `t` is identified by an actual Hilbert-module
unitary with the original fibre at `1 - t`. All cycle data intertwines. Hence
reversal gives an actual single full interval witness in the reverse direction.
No interval gluing or transitivity of single witnesses is asserted here.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Reversal of an actual continuous coefficient function, also for nonunital coefficients. -/
def intervalReversalCoefficient : C(unitInterval, B) ≃⋆ₐ[ℂ] C(unitInterval, B) where
  toFun b := b.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩
  invFun b := b.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩
  left_inv b := by ext t; exact congrArg b (unitInterval.symm_symm t)
  right_inv b := by ext t; exact congrArg b (unitInterval.symm_symm t)
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_star' _ := rfl
  map_smul' _ _ := rfl

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem intervalReversalCoefficient_apply (b : C(unitInterval, B)) (t : unitInterval) :
    intervalReversalCoefficient b t = b (unitInterval.symm t) := rfl

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem intervalReversalCoefficient_involutive (b : C(unitInterval, B)) :
    intervalReversalCoefficient (intervalReversalCoefficient b) = b := by
  ext t
  exact congrArg b (unitInterval.symm_symm t)

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem intervalReversal_op_involutive (a : C(unitInterval, B)ᵐᵒᵖ) :
    opStarAlgEquiv intervalReversalCoefficient (opStarAlgEquiv intervalReversalCoefficient a) = a := by
  apply MulOpposite.unop_injective
  exact intervalReversalCoefficient_involutive _

omit [StarOrderedRing B] in
/-- The actual coefficient reversal preserves the pointwise positive order. -/
theorem intervalReversal_op_nonneg (a : C(unitInterval, B)ᵐᵒᵖ) (ha : 0 ≤ a) :
    0 ≤ opStarAlgEquiv intervalReversalCoefficient a := by
  change ∀ t, 0 ≤ MulOpposite.unop a (unitInterval.symm t)
  change ∀ t, 0 ≤ MulOpposite.unop a t at ha
  intro t
  exact ha (unitInterval.symm t)

/-- A separate module carrier with the original complex space and norm. Its
continuous coefficient action and inner product are twisted below. -/
def IntervalReversedModule (_B M : Type*) := M

variable {M N : Type*}
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(unitInterval, B)ᵐᵒᵖ M] [CStarModule C(unitInterval, B)ᵐᵒᵖ M]
  [NormedAddCommGroup N] [NormedSpace ℂ N]
  [SMul C(unitInterval, B)ᵐᵒᵖ N] [CStarModule C(unitInterval, B)ᵐᵒᵖ N]

/-- Typed conversion selecting the original module's coefficient and inner-product instances. -/
def intervalReversedToOriginal (x : IntervalReversedModule B M) : M := x

/-- Typed conversion into the module carrying the genuinely reversed coefficient data. -/
def intervalReversedOfOriginal (_B : Type*) (x : M) : IntervalReversedModule _B M := x

instance intervalReversedNormedAddCommGroup : NormedAddCommGroup (IntervalReversedModule B M) :=
  inferInstanceAs (NormedAddCommGroup M)

instance intervalReversedNormedSpace : NormedSpace ℂ (IntervalReversedModule B M) :=
  inferInstanceAs (NormedSpace ℂ M)

instance intervalReversedSMul : SMul C(unitInterval, B)ᵐᵒᵖ (IntervalReversedModule B M) where
  smul a x := intervalReversedOfOriginal B
    (opStarAlgEquiv intervalReversalCoefficient a • intervalReversedToOriginal x)

/-- The underlying complex-linear isometry changes no vectors or norms. -/
def intervalReversedLinearIsometry : M ≃ₗᵢ[ℂ] IntervalReversedModule B M where
  toFun := intervalReversedOfOriginal B
  invFun := intervalReversedToOriginal
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

/-- The actual reversed coefficient-valued inner product. -/
instance intervalReversedCStarModule :
    CStarModule C(unitInterval, B)ᵐᵒᵖ (IntervalReversedModule B M) where
  inner x y := opStarAlgEquiv intervalReversalCoefficient ⟪(intervalReversedToOriginal x), (intervalReversedToOriginal y)⟫_(C(unitInterval, B)ᵐᵒᵖ)
  inner_add_right := by
    intro x y z
    change opStarAlgEquiv intervalReversalCoefficient
      ⟪(intervalReversedToOriginal x), (intervalReversedToOriginal y) + intervalReversedToOriginal z⟫_(C(unitInterval, B)ᵐᵒᵖ) = _
    rw [CStarModule.inner_add_right, map_add]
  inner_self_nonneg := intervalReversal_op_nonneg _ CStarModule.inner_self_nonneg
  inner_self := by
    intro x
    change opStarAlgEquiv intervalReversalCoefficient
      ⟪(intervalReversedToOriginal x), (intervalReversedToOriginal x)⟫_(C(unitInterval, B)ᵐᵒᵖ) = 0 ↔ x = 0
    constructor
    · intro hx
      have hzero : ⟪intervalReversedToOriginal x, intervalReversedToOriginal x⟫_(C(unitInterval, B)ᵐᵒᵖ) = 0 :=
        (opStarAlgEquiv (intervalReversalCoefficient (B := B))).injective
          (hx.trans (map_zero (opStarAlgEquiv (intervalReversalCoefficient (B := B)))).symm)
      exact (CStarModule.inner_self (A := C(unitInterval, B)ᵐᵒᵖ) (E := M)
        (x := intervalReversedToOriginal x)).mp hzero
    · intro hx
      subst x
      change opStarAlgEquiv intervalReversalCoefficient ⟪(0 : M), 0⟫_(C(unitInterval, B)ᵐᵒᵖ) = 0
      rw [CStarModule.inner_zero_left, map_zero]
  inner_op_smul_right := by
    intro a x y
    change opStarAlgEquiv intervalReversalCoefficient
      ⟪(intervalReversedToOriginal x), opStarAlgEquiv intervalReversalCoefficient a • (intervalReversedToOriginal y)⟫_(C(unitInterval, B)ᵐᵒᵖ) = _
    rw [CStarModule.inner_op_smul_right, map_mul, intervalReversal_op_involutive]
  inner_smul_right_complex := by
    intro c x y
    change opStarAlgEquiv intervalReversalCoefficient
      ⟪(intervalReversedToOriginal x), c • (intervalReversedToOriginal y)⟫_(C(unitInterval, B)ᵐᵒᵖ) = _
    rw [CStarModule.inner_smul_right_complex, map_smul]
  star_inner x y := by
    change star (opStarAlgEquiv intervalReversalCoefficient
      ⟪(intervalReversedToOriginal x), (intervalReversedToOriginal y)⟫_(C(unitInterval, B)ᵐᵒᵖ)) = _
    rw [← map_star, CStarModule.star_inner]
  norm_eq_sqrt_norm_inner_self x := by
    change ‖(intervalReversedToOriginal x)‖ = Real.sqrt
      ‖opStarAlgEquiv intervalReversalCoefficient ⟪(intervalReversedToOriginal x), (intervalReversedToOriginal x)⟫_(C(unitInterval, B)ᵐᵒᵖ)‖
    rw [StarAlgEquiv.norm_map]
    exact CStarModule.norm_eq_sqrt_norm_inner_self _

omit [StarOrderedRing B] in
@[simp] theorem intervalReversed_inner_apply (x y : IntervalReversedModule B M) (t : unitInterval) :
    MulOpposite.unop ⟪x, y⟫_(C(unitInterval, B)ᵐᵒᵖ) t =
      MulOpposite.unop ⟪(intervalReversedToOriginal x), (intervalReversedToOriginal y)⟫_(C(unitInterval, B)ᵐᵒᵖ) (unitInterval.symm t) := rfl

instance intervalReversedCompleteSpace [CompleteSpace M] :
    CompleteSpace (IntervalReversedModule B M) := inferInstanceAs (CompleteSpace M)

omit [StarOrderedRing B] in
/-- Countable generation transports through the actual semilinear isometry;
the coefficient automorphism is involutive and hence supplies every old coefficient. -/
theorem IsCountablyGeneratedModule.intervalReversed
    (h : IsCountablyGeneratedModule C(unitInterval, B) M) :
    IsCountablyGeneratedModule C(unitInterval, B) (IntervalReversedModule B M) := by
  apply h.map_linearIsometryEquiv (intervalReversedLinearIsometry (B := B))
    (opStarAlgEquiv (intervalReversalCoefficient (B := B)))
  intro a x
  change a • x =
    opStarAlgEquiv intervalReversalCoefficient (opStarAlgEquiv intervalReversalCoefficient a) • x
  rw [intervalReversal_op_involutive]

/-- The bounded adjoint pair on a reversed module has the original continuous
linear maps and their original norms. -/
def intervalReversedOperator (T : AdjointableMap C(unitInterval, B) M N) :
    AdjointableMap C(unitInterval, B) (IntervalReversedModule B M) (IntervalReversedModule B N) where
  toCLM := T.toCLM
  adjointCLM := T.adjointCLM
  adjoint_identity x y := congrArg (opStarAlgEquiv (intervalReversalCoefficient (B := B)))
    (T.adjoint_identity (intervalReversedToOriginal x) (intervalReversedToOriginal y))

omit [StarOrderedRing B] in
@[simp] theorem intervalReversedOperator_apply
    (T : AdjointableMap C(unitInterval, B) M N) (x : IntervalReversedModule B M) :
    intervalReversedOperator T x = T (intervalReversedToOriginal x) := rfl

omit [StarOrderedRing B] in
@[simp] theorem intervalReversedOperator_norm (T : AdjointableMap C(unitInterval, B) M N) :
    ‖intervalReversedOperator T‖ = ‖T‖ := rfl

omit [StarOrderedRing B] in
@[simp] theorem intervalReversedOperator_zero :
    intervalReversedOperator (0 : AdjointableMap C(unitInterval, B) M N) = 0 := by ext x; rfl

omit [StarOrderedRing B] in
@[simp] theorem intervalReversedOperator_add (S T : AdjointableMap C(unitInterval, B) M N) :
    intervalReversedOperator (S + T) = intervalReversedOperator S + intervalReversedOperator T := by
  ext x
  rfl

omit [StarOrderedRing B] in
@[simp] theorem intervalReversedOperator_sub (S T : AdjointableMap C(unitInterval, B) M N) :
    intervalReversedOperator (S - T) = intervalReversedOperator S - intervalReversedOperator T := by
  ext x
  rfl

omit [StarOrderedRing B] in
@[simp] theorem intervalReversedOperator_smul (c : ℂ) (T : AdjointableMap C(unitInterval, B) M N) :
    intervalReversedOperator (c • T) = c • intervalReversedOperator T := by ext x; rfl

omit [StarOrderedRing B] in
@[simp] theorem intervalReversedOperator_adjoint (T : AdjointableMap C(unitInterval, B) M N) :
    intervalReversedOperator T.adjoint = (intervalReversedOperator T).adjoint := rfl

omit [StarOrderedRing B] in
@[simp] theorem intervalReversedOperator_mul (S T : AdjointableMap C(unitInterval, B) M M) :
    intervalReversedOperator (S * T) = intervalReversedOperator S * intervalReversedOperator T := by
  ext x
  rfl

omit [StarOrderedRing B] in
@[simp] theorem intervalReversedOperator_one :
    intervalReversedOperator (1 : AdjointableMap C(unitInterval, B) M M) = 1 := by ext x; rfl

omit [StarOrderedRing B] in
@[simp] theorem intervalReversedOperator_star (T : AdjointableMap C(unitInterval, B) M M) :
    intervalReversedOperator (star T) = star (intervalReversedOperator T) := rfl

/-- Reversal is a genuine complex-linear isometry on rectangular operator spaces. -/
def intervalReversedOperatorLinearIsometry :
    AdjointableMap C(unitInterval, B) M N →ₗᵢ[ℂ]
      AdjointableMap C(unitInterval, B) (IntervalReversedModule B M) (IntervalReversedModule B N) where
  toFun := intervalReversedOperator
  map_add' := intervalReversedOperator_add
  map_smul' := intervalReversedOperator_smul
  norm_map' := intervalReversedOperator_norm

/-- The reversed rank-one map is the actual rank-one map between reversed
modules: the two coefficient reversals cancel exactly. -/
@[simp] theorem intervalReversedOperator_rankOne (x : N) (y : M) :
    intervalReversedOperator (moduleRankOne (B := C(unitInterval, B)) x y) =
      moduleRankOne (B := C(unitInterval, B))
        (intervalReversedLinearIsometry (B := B) x) (intervalReversedLinearIsometry (B := B) y) := by
  ext z
  change ⟪y, (intervalReversedToOriginal z)⟫_(C(unitInterval, B)ᵐᵒᵖ) • x =
    opStarAlgEquiv intervalReversalCoefficient
      (opStarAlgEquiv intervalReversalCoefficient ⟪y, (intervalReversedToOriginal z)⟫_(C(unitInterval, B)ᵐᵒᵖ)) • x
  rw [intervalReversal_op_involutive]

/-- Actual compactness transports through the norm-continuous linear isometry
because it transports the rank-one generators and their norm closure. -/
theorem IsModuleCompact.intervalReversed {T : AdjointableMap C(unitInterval, B) M N}
    (hT : IsModuleCompact T) : IsModuleCompact (intervalReversedOperator T) := by
  let f := intervalReversedOperatorLinearIsometry (B := B) (M := M) (N := N)
  let S := (moduleCompact C(unitInterval, B) (IntervalReversedModule B M)
    (IntervalReversedModule B N)).comap f.toLinearMap
  have hS : IsClosed (S : Set (AdjointableMap C(unitInterval, B) M N)) :=
    moduleCompact_isClosed.preimage f.continuous
  have hθ (x : N) (y : M) : moduleRankOne (B := C(unitInterval, B)) x y ∈ S := by
    change intervalReversedOperator (moduleRankOne (B := C(unitInterval, B)) x y) ∈
      moduleCompact C(unitInterval, B) (IntervalReversedModule B M) (IntervalReversedModule B N)
    rw [intervalReversedOperator_rankOne]
    exact moduleRankOne_mem_moduleCompact _ _
  exact moduleCompact_le_of_isClosed S hS hθ hT

/-- Endomorphism reversal preserves the actual complex star-algebra operations. -/
def intervalReversedOperatorHom : AdjointableMap C(unitInterval, B) M M →⋆ₙₐ[ℂ]
    AdjointableMap C(unitInterval, B) (IntervalReversedModule B M) (IntervalReversedModule B M) where
  toFun := intervalReversedOperator
  map_zero' := intervalReversedOperator_zero
  map_add' := intervalReversedOperator_add
  map_mul' := intervalReversedOperator_mul
  map_smul' := intervalReversedOperator_smul
  map_star' := intervalReversedOperator_star

namespace GradedHilbertModule

/-- A trivial-coefficient grading is retained on the reversed module. -/
def intervalReversed (γ : GradedHilbertModule
    (CStarGrading.trivial : CStarGrading C(unitInterval, B)) M) :
    GradedHilbertModule (CStarGrading.trivial : CStarGrading C(unitInterval, B)) (IntervalReversedModule B M) where
  grading := γ.grading
  involutive := γ.involutive
  inner_grading x y := by
    change opStarAlgEquiv intervalReversalCoefficient
      ⟪γ.grading (intervalReversedToOriginal x), γ.grading (intervalReversedToOriginal y)⟫_(C(unitInterval, B)ᵐᵒᵖ) =
      opStarAlgEquiv intervalReversalCoefficient
        ⟪intervalReversedToOriginal x, intervalReversedToOriginal y⟫_(C(unitInterval, B)ᵐᵒᵖ)
    simpa only [CStarGrading.op_trivial_apply] using
      congrArg (opStarAlgEquiv (intervalReversalCoefficient (B := B)))
        (γ.inner_grading (intervalReversedToOriginal x) (intervalReversedToOriginal y))

end GradedHilbertModule

variable {Γ A : Type*} [Group Γ] [NonUnitalCStarAlgebra A]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

/-- Coefficient reversal commutes with the actual pointwise coefficient action. -/
theorem intervalReversal_op_commute (g : Γ) (a : C(unitInterval, B)ᵐᵒᵖ) :
    opStarAlgEquiv intervalReversalCoefficient
      (opStarAlgEquiv ((β.continuousSections (X := unitInterval)).automorphism g) a) =
    opStarAlgEquiv ((β.continuousSections (X := unitInterval)).automorphism g)
      (opStarAlgEquiv intervalReversalCoefficient a) := by
  apply MulOpposite.unop_injective
  ext t
  rfl

namespace EquivariantHilbertModule

/-- The actual pointwise coefficient action remains compatible with reversal
on an arbitrary interval module, because the coefficient actions commute. -/
def intervalReversed (U : EquivariantHilbertModule
    (β.continuousSections (X := unitInterval)) M) :
    EquivariantHilbertModule (β.continuousSections (X := unitInterval)) (IntervalReversedModule B M) where
  action := U.action
  inner_action g x y := by
    change opStarAlgEquiv intervalReversalCoefficient
      ⟪U.action g (intervalReversedToOriginal x), U.action g (intervalReversedToOriginal y)⟫_(C(unitInterval, B)ᵐᵒᵖ) =
      opStarAlgEquiv ((β.continuousSections (X := unitInterval)).automorphism g)
        (opStarAlgEquiv intervalReversalCoefficient
          ⟪intervalReversedToOriginal x, intervalReversedToOriginal y⟫_(C(unitInterval, B)ᵐᵒᵖ))
    rw [U.inner_action, intervalReversal_op_commute]

theorem intervalReversed_conjugateOperator
    (U : EquivariantHilbertModule (β.continuousSections (X := unitInterval)) M)
    (g : Γ) (T : AdjointableMap C(unitInterval, B) M M) :
    U.intervalReversed.conjugateOperator g (intervalReversedOperator T) =
      intervalReversedOperator (U.conjugateOperator g T) := by
  ext x
  rfl

end EquivariantHilbertModule

variable [CompleteSpace M]

namespace KasparovCycle

/-- Reverse an actual cycle over continuous interval coefficients on an
arbitrary complete module, transporting all compact defects honestly. -/
def intervalReversed (c : KasparovCycle α (β.continuousSections (X := unitInterval)) M) :
    KasparovCycle α (β.continuousSections (X := unitInterval)) (IntervalReversedModule B M) where
  countablyGenerated := c.countablyGenerated.intervalReversed
  grading := c.grading.intervalReversed
  groupAction := c.groupAction.intervalReversed
  grading_preserved := c.grading_preserved
  representation := intervalReversedOperatorHom.comp c.representation
  representation_even a := c.representation_even a
  representation_equivariant g a := by
    change c.groupAction.intervalReversed.conjugateOperator g
      (intervalReversedOperator (c.representation a)) =
        intervalReversedOperator (c.representation (α.automorphism g a))
    rw [c.groupAction.intervalReversed_conjugateOperator, c.representation_equivariant]
  operator := intervalReversedOperator c.operator
  operator_odd := c.operator_odd
  selfadjoint_mod_compact a := by
    change IsModuleCompact ((intervalReversedOperator c.operator - star (intervalReversedOperator c.operator)) *
      intervalReversedOperator (c.representation a))
    simpa only [intervalReversedOperator_mul, intervalReversedOperator_sub,
      intervalReversedOperator_star] using (c.selfadjoint_mod_compact a).intervalReversed
  square_mod_compact a := by
    change IsModuleCompact ((intervalReversedOperator c.operator * intervalReversedOperator c.operator - 1) *
      intervalReversedOperator (c.representation a))
    simpa only [intervalReversedOperator_mul, intervalReversedOperator_sub,
      intervalReversedOperator_one] using (c.square_mod_compact a).intervalReversed
  commutator_compact a := by
    change IsModuleCompact (intervalReversedOperator c.operator * intervalReversedOperator (c.representation a) -
      intervalReversedOperator (c.representation a) * intervalReversedOperator c.operator)
    simpa only [intervalReversedOperator_mul, intervalReversedOperator_sub] using
      (c.commutator_compact a).intervalReversed
  equivariance_mod_compact g a := by
    change IsModuleCompact ((c.groupAction.intervalReversed.conjugateOperator g (intervalReversedOperator c.operator) -
      intervalReversedOperator c.operator) * intervalReversedOperator (c.representation a))
    simpa only [intervalReversedOperator_mul, intervalReversedOperator_sub,
      c.groupAction.intervalReversed_conjugateOperator] using
        (c.equivariance_mod_compact g a).intervalReversed

end KasparovCycle

/-- Actual evaluation of a reversed module into the original reflected fibre. -/
def intervalReversedFibreEvaluation (t : unitInterval) :
    IntervalReversedModule B M →L[ℂ] HilbertModuleFibre B M (unitInterval.symm t) :=
  (hilbertModuleFibreMk (B := B) (M := M) (unitInterval.symm t)).comp
    (intervalReversedLinearIsometry (B := B) (M := M)).symm.toLinearIsometry.toContinuousLinearMap

/-- The reversed completed evaluated fibre is identified with the original
reflected fibre. Surjectivity is the proved genuine fibre-quotient theorem. -/
def intervalReversedFibreEquiv (t : unitInterval) :
    HilbertModuleEquiv B (HilbertModuleFibre B (IntervalReversedModule B M) t)
      (HilbertModuleFibre B M (unitInterval.symm t)) :=
  hilbertModuleFibreEquivOfEvaluation t (intervalReversedFibreEvaluation (B := B) t)
    (fun x y => by
      change ⟪hilbertModuleFibreMk (B := B) (M := M) (unitInterval.symm t) (intervalReversedToOriginal x),
        hilbertModuleFibreMk (B := B) (M := M) (unitInterval.symm t) (intervalReversedToOriginal y)⟫_(Bᵐᵒᵖ) = _
      rw [hilbertModuleFibre_inner_mk]
      rfl)
    ((hilbertModuleFibreMk_surjective (B := B) (M := M) (unitInterval.symm t)).comp
      (intervalReversedLinearIsometry (B := B) (M := M)).symm.surjective)

@[simp] theorem intervalReversedFibreEquiv_mk (t : unitInterval) (x : IntervalReversedModule B M) :
    intervalReversedFibreEquiv (B := B) t (hilbertModuleFibreMk (B := B) (M := IntervalReversedModule B M) t x) =
      hilbertModuleFibreMk (B := B) (M := M) (unitInterval.symm t) (intervalReversedToOriginal x) :=
  hilbertModuleFibreEquivOfEvaluation_mk t (intervalReversedFibreEvaluation (B := B) t) _ _ x

/-- Direct evaluation at a specified reflected parameter avoids transporting
completed fibre carriers through an endpoint equality. -/
def intervalReversedFibreEquivAt (t s : unitInterval) (hs : unitInterval.symm t = s) :
    HilbertModuleEquiv B (HilbertModuleFibre B (IntervalReversedModule B M) t)
      (HilbertModuleFibre B M s) :=
  hilbertModuleFibreEquivOfEvaluation t
    ((hilbertModuleFibreMk (B := B) (M := M) s).comp
      (intervalReversedLinearIsometry (B := B) (M := M)).symm.toLinearIsometry.toContinuousLinearMap)
    (fun x y => by
      change ⟪hilbertModuleFibreMk (B := B) (M := M) s (intervalReversedToOriginal x),
        hilbertModuleFibreMk (B := B) (M := M) s (intervalReversedToOriginal y)⟫_(Bᵐᵒᵖ) = _
      rw [hilbertModuleFibre_inner_mk]
      change MulOpposite.op (MulOpposite.unop
        ⟪intervalReversedToOriginal x, intervalReversedToOriginal y⟫_(C(unitInterval, B)ᵐᵒᵖ) s) =
        MulOpposite.op (MulOpposite.unop
          ⟪intervalReversedToOriginal x, intervalReversedToOriginal y⟫_(C(unitInterval, B)ᵐᵒᵖ)
            (unitInterval.symm t))
      rw [hs])
    ((hilbertModuleFibreMk_surjective (B := B) (M := M) s).comp
      (intervalReversedLinearIsometry (B := B) (M := M)).symm.surjective)

@[simp] theorem intervalReversedFibreEquivAt_mk (t s : unitInterval)
    (hs : unitInterval.symm t = s) (x : IntervalReversedModule B M) :
    intervalReversedFibreEquivAt t s hs
      (hilbertModuleFibreMk (B := B) (M := IntervalReversedModule B M) t x) =
      hilbertModuleFibreMk (B := B) (M := M) s (intervalReversedToOriginal x) :=
  hilbertModuleFibreEquivOfEvaluation_mk t _ _ _ x

namespace KasparovCycleIso

/-- Reversal of an arbitrary interval cycle identifies every part of the
completed fibre cycle with the original cycle at the reflected parameter. -/
def intervalReversedFibre
    (c : KasparovCycle α (β.continuousSections (X := unitInterval)) M) (t : unitInterval) :
    KasparovCycleIso (c.intervalReversed.fibre t) (c.fibre (unitInterval.symm t)) where
  moduleEquiv := intervalReversedFibreEquiv t
  grading_intertwine z := by
    refine (hilbertModuleFibreMk_denseRange
      (B := B) (M := IntervalReversedModule B M) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [KasparovCycle.fibre_grading_mk, intervalReversedFibreEquiv_mk,
        intervalReversedFibreEquiv_mk, KasparovCycle.fibre_grading_mk]
      rfl
  action_intertwine g z := by
    refine (hilbertModuleFibreMk_denseRange
      (B := B) (M := IntervalReversedModule B M) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [KasparovCycle.fibre_action_mk, intervalReversedFibreEquiv_mk,
        intervalReversedFibreEquiv_mk, KasparovCycle.fibre_action_mk]
      rfl
  representation_intertwine a z := by
    refine (hilbertModuleFibreMk_denseRange
      (B := B) (M := IntervalReversedModule B M) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [KasparovCycle.fibre_representation_mk, intervalReversedFibreEquiv_mk,
        intervalReversedFibreEquiv_mk, KasparovCycle.fibre_representation_mk]
      rfl
  operator_intertwine z := by
    refine (hilbertModuleFibreMk_denseRange
      (B := B) (M := IntervalReversedModule B M) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      rw [KasparovCycle.fibre_operator_mk, intervalReversedFibreEquiv_mk,
        intervalReversedFibreEquiv_mk, KasparovCycle.fibre_operator_mk]
      rfl

/-- The specified reflected fibre has an actual whole-cycle unitary built
by direct evaluation, without a cast of completed fibre module structures. -/
def intervalReversedFibreAt
    (c : KasparovCycle α (β.continuousSections (X := unitInterval)) M)
    (t s : unitInterval) (hs : unitInterval.symm t = s) :
    KasparovCycleIso (c.intervalReversed.fibre t) (c.fibre s) where
  moduleEquiv := intervalReversedFibreEquivAt t s hs
  grading_intertwine z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective
      (B := B) (M := IntervalReversedModule B M) t z
    rw [KasparovCycle.fibre_grading_mk, intervalReversedFibreEquivAt_mk,
      intervalReversedFibreEquivAt_mk, KasparovCycle.fibre_grading_mk]
    rfl
  action_intertwine g z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective
      (B := B) (M := IntervalReversedModule B M) t z
    rw [KasparovCycle.fibre_action_mk, intervalReversedFibreEquivAt_mk,
      intervalReversedFibreEquivAt_mk, KasparovCycle.fibre_action_mk]
    rfl
  representation_intertwine a z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective
      (B := B) (M := IntervalReversedModule B M) t z
    rw [KasparovCycle.fibre_representation_mk, intervalReversedFibreEquivAt_mk,
      intervalReversedFibreEquivAt_mk, KasparovCycle.fibre_representation_mk]
    rfl
  operator_intertwine z := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective
      (B := B) (M := IntervalReversedModule B M) t z
    rw [KasparovCycle.fibre_operator_mk, intervalReversedFibreEquivAt_mk,
      intervalReversedFibreEquivAt_mk, KasparovCycle.fibre_operator_mk]
    rfl

end KasparovCycleIso

namespace FullKasparovHomotopy

set_option maxHeartbeats 1000000 in
/-- Symmetry is represented by a single genuine reversed interval cycle on
the actual twisted arbitrary module, with actual whole-cycle endpoint unitaries. -/
def symm {c d : BundledKasparovCycle α β} (h : FullKasparovHomotopy c d) :
    FullKasparovHomotopy d c where
  intervalCycle := BundledKasparovCycle.of h.intervalCycle.cycle.intervalReversed
  sourceIso := (KasparovCycleIso.intervalReversedFibreAt
    h.intervalCycle.cycle 0 1 unitInterval.symm_zero).trans h.targetIso
  targetIso := (KasparovCycleIso.intervalReversedFibreAt
    h.intervalCycle.cycle 1 0 unitInterval.symm_one).trans h.sourceIso

end FullKasparovHomotopy
end BC4lean.KKTheory
