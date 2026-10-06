import BC4lean.IntervalHilbertModule
import BC4lean.KasparovOperatorHomotopy
import BC4lean.EquivariantCompactOperator
import BC4lean.KasparovCycleTransport

/-! # Operator paths as genuine interval-coefficient Kasparov cycles

A norm-continuous operator homotopy on a fixed equivariant graded Hilbert
module defines an actual Kasparov cycle over `C([0,1],B)`. Its compact defects
are proved compact as module operators on continuous sections by uniform
finite-rank partition approximation.
-/

noncomputable section
namespace BC4lean.KKTheory

open unitInterval
open scoped InnerProductSpace

variable {Γ A B E F X : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

omit [PartialOrder B] [StarOrderedRing B] [CompactSpace X] in
/-- A coefficient automorphism acts pointwise on continuous coefficients. -/
def continuousCoefficientEquiv (e : B ≃⋆ₐ[ℂ] B) : C(X, B) ≃⋆ₐ[ℂ] C(X, B) where
  toFun b := ⟨fun t => e (b t), (StarAlgEquiv.isometry e).continuous.comp b.continuous⟩
  invFun b := ⟨fun t => e.symm (b t), (StarAlgEquiv.isometry e.symm).continuous.comp b.continuous⟩
  left_inv b := by ext t; exact e.symm_apply_apply (b t)
  right_inv b := by ext t; exact e.apply_symm_apply (b t)
  map_mul' b c := by ext t; exact e.map_mul (b t) (c t)
  map_add' b c := by ext t; exact e.map_add (b t) (c t)
  map_star' b := by ext t; exact map_star e (b t)
  map_smul' c b := by ext t; exact map_smul e c (b t)

omit [CompactSpace X] in
@[simp] theorem continuousCoefficientEquiv_apply (e : B ≃⋆ₐ[ℂ] B) (b : C(X, B)) (t : X) :
    continuousCoefficientEquiv e b t = e (b t) := rfl

/-- A coefficient action acts pointwise, with the parameter fixed. -/
def CStarAlgebraAction.continuousSections (β : CStarAlgebraAction Γ B) :
    CStarAlgebraAction Γ C(X, B) where
  automorphism :=
    { toFun := fun g => continuousCoefficientEquiv (β.automorphism g)
      map_one' := by ext b t; exact β.one_apply (b t)
      map_mul' := fun g h => by ext b t; exact β.mul_apply g h (b t) }

/-- A module isometry acts pointwise, preserving the existing supremum norm. -/
def continuousSectionIsometryEquiv (e : E ≃ₗᵢ[ℂ] F) : C(X, E) ≃ₗᵢ[ℂ] C(X, F) where
  toFun x := ⟨fun t => e (x t), e.continuous.comp x.continuous⟩
  invFun y := ⟨fun t => e.symm (y t), e.symm.continuous.comp y.continuous⟩
  left_inv x := by ext t; exact e.symm_apply_apply (x t)
  right_inv y := by ext t; exact e.apply_symm_apply (y t)
  map_add' x y := by ext t; exact e.map_add (x t) (y t)
  map_smul' c x := by ext t; exact e.map_smul c (x t)
  norm_map' x := by
    simp only [ContinuousMap.norm_eq_iSup_norm]
    congr 1
    funext t
    exact e.norm_map (x t)

@[simp] theorem continuousSectionIsometryEquiv_apply (e : E ≃ₗᵢ[ℂ] F) (x : C(X, E)) (t : X) :
    continuousSectionIsometryEquiv e x t = e (x t) := rfl

/-- The fixed module grading extends to continuous sections. -/
def GradedHilbertModule.continuousSections
    (γ : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E) :
    GradedHilbertModule (CStarGrading.trivial : CStarGrading C(X, B)) C(X, E) where
  grading := continuousSectionIsometryEquiv γ.grading
  involutive x := by ext t; exact γ.involutive (x t)
  inner_grading x y := by
    apply MulOpposite.unop_injective
    ext t
    exact congrArg MulOpposite.unop (γ.inner_grading (x t) (y t))

/-- The fixed compatible group action extends to continuous sections. -/
def EquivariantHilbertModule.continuousSections {β : CStarAlgebraAction Γ B}
    (U : EquivariantHilbertModule β E) :
    EquivariantHilbertModule (β.continuousSections (X := X)) C(X, E) where
  action :=
    { toFun := fun g => continuousSectionIsometryEquiv (U.action g)
      map_one' := by ext x t; exact U.one_apply (x t)
      map_mul' := fun g h => by ext x t; exact U.mul_apply g h (x t) }
  inner_action g x y := by
    apply MulOpposite.unop_injective
    ext t
    exact congrArg MulOpposite.unop (U.inner_action g (x t) (y t))

/-- A constant operator acts pointwise on sections. -/
def continuousSectionConstantOperator (T : AdjointableMap B E F) :
    AdjointableMap C(X, B) C(X, E) C(X, F) :=
  continuousSectionOperator (ContinuousMap.const X T)

@[simp] theorem continuousSectionConstantOperator_apply
    (T : AdjointableMap B E F) (x : C(X, E)) (t : X) :
    continuousSectionConstantOperator T x t = T (x t) := rfl

/-- Constant section operators preserve the full complex star-algebra structure. -/
def continuousSectionConstantOperatorHom :
    AdjointableMap B E E →⋆ₙₐ[ℂ] AdjointableMap C(X, B) C(X, E) C(X, E) where
  toFun := continuousSectionConstantOperator
  map_zero' := by ext x t; rfl
  map_add' S T := by ext x t; rfl
  map_mul' S T := by ext x t; rfl
  map_star' T := by ext x t; rfl
  map_smul' c T := by ext x t; rfl

variable [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace KasparovOperatorHomotopy

variable {c : KasparovCycle α β E} {T₀ T₁ : AdjointableMap B E E}

/-- A fixed-module operator homotopy gives a genuine interval-coefficient
Kasparov cycle, with actual compact module defects on `C(I,E)`. -/
def intervalCycle (h : KasparovOperatorHomotopy c T₀ T₁) :
    KasparovCycle α (β.continuousSections (X := I)) C(I, E) where
  countablyGenerated := continuousSection_isCountablyGenerated c.countablyGenerated
  grading := c.grading.continuousSections
  groupAction := c.groupAction.continuousSections
  grading_preserved := by
    intro g x
    ext t
    exact c.grading_preserved g (x t)
  representation := continuousSectionConstantOperatorHom.comp c.representation
  representation_even := by
    intro a x
    ext t
    exact c.representation_even a (x t)
  representation_equivariant := by
    intro g a
    ext x t
    exact congrArg (fun T : AdjointableMap B E E => T (x t))
      (c.representation_equivariant g a)
  operator := continuousSectionOperator ⟨h.path, h.path.continuous⟩
  operator_odd := by
    intro x
    ext t
    exact (h.conditions t).operator_odd (x t)
  selfadjoint_mod_compact := by
    intro a
    let D : C(I, AdjointableMap B E E) :=
      ⟨fun t => (h.path t - star (h.path t)) * c.representation a,
        (h.path.continuous.sub h.path.continuous.star).mul continuous_const⟩
    have hD := continuousSectionOperator_isModuleCompact D
      (fun t => (h.conditions t).selfadjoint_mod_compact a)
    convert hD using 1
    ext x t
    rfl
  square_mod_compact := by
    intro a
    let D : C(I, AdjointableMap B E E) :=
      ⟨fun t => (h.path t * h.path t - 1) * c.representation a,
        ((h.path.continuous.mul h.path.continuous).sub continuous_const).mul continuous_const⟩
    have hD := continuousSectionOperator_isModuleCompact D
      (fun t => (h.conditions t).square_mod_compact a)
    convert hD using 1
    ext x t
    rfl
  commutator_compact := by
    intro a
    let D : C(I, AdjointableMap B E E) :=
      ⟨fun t => h.path t * c.representation a - c.representation a * h.path t,
        (h.path.continuous.mul continuous_const).sub (continuous_const.mul h.path.continuous)⟩
    have hD := continuousSectionOperator_isModuleCompact D
      (fun t => (h.conditions t).commutator_compact a)
    convert hD using 1
    ext x t
    rfl
  equivariance_mod_compact := by
    intro g a
    let D : C(I, AdjointableMap B E E) :=
      ⟨fun t => (c.groupAction.conjugateOperator g (h.path t) - h.path t) * c.representation a,
        (((c.groupAction.conjugateMapContinuousLinearMap c.groupAction g).continuous.comp
          h.path.continuous).sub h.path.continuous).mul continuous_const⟩
    have hD := continuousSectionOperator_isModuleCompact D
      (fun t => (h.conditions t).equivariance_mod_compact g a)
    convert hD using 1
    ext x t
    rfl

/-- Evaluation of the interval operator is the original path operator. -/
@[simp] theorem intervalCycle_operator_apply (h : KasparovOperatorHomotopy c T₀ T₁)
    (x : C(I, E)) (t : I) : h.intervalCycle.operator x t = h.path t (x t) := rfl

@[simp] theorem intervalCycle_operator_at_zero (h : KasparovOperatorHomotopy c T₀ T₁)
    (x : E) : h.intervalCycle.operator (ContinuousMap.const I x) 0 = T₀ x := by
  simp only [intervalCycle_operator_apply, ContinuousMap.const_apply, h.path.source]

@[simp] theorem intervalCycle_operator_at_one (h : KasparovOperatorHomotopy c T₀ T₁)
    (x : E) : h.intervalCycle.operator (ContinuousMap.const I x) 1 = T₁ x := by
  simp only [intervalCycle_operator_apply, ContinuousMap.const_apply, h.path.target]

/-- The canonical evaluated-inner-product quotient fibre carries the cycle
obtained from the path at `t`. This construction is for continuous-section
interval cycles; general varying interval modules require a separate fibre construction. -/
def fibreCycle (h : KasparovOperatorHomotopy c T₀ T₁) (t : I) :
    KasparovCycle α β (ContinuousSectionFibre E t) :=
  (h.cycleAt t).transport (continuousSectionFibreModuleEquiv (B := B) t).symm

/-- Evaluation intertwines every part of the quotient-fibre cycle with the
original path cycle, giving an actual cycle isomorphism. -/
def fibreCycleIso (h : KasparovOperatorHomotopy c T₀ T₁) (t : I) :
    KasparovCycleIso (h.fibreCycle t) (h.cycleAt t) :=
  ((h.cycleAt t).transportIso (continuousSectionFibreModuleEquiv (B := B) t).symm).symm

/-- The fibre operator is the descent of the actual interval operator on
quotient representatives. -/
theorem fibreCycle_operator_mk (h : KasparovOperatorHomotopy c T₀ T₁) (t : I) (x : C(I, E)) :
    (h.fibreCycle t).operator (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (h.intervalCycle.operator x) := by
  apply (continuousSectionFibreIsometryEquiv t).injective
  change continuousSectionFibreIsometryEquiv t
    ((continuousSectionFibreIsometryEquiv t).symm
      (h.path t (continuousSectionFibreIsometryEquiv t (Submodule.Quotient.mk x)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, continuousSectionFibreIsometryEquiv_mk,
    continuousSectionFibreIsometryEquiv_mk]
  rfl

theorem fibreCycle_representation_mk (h : KasparovOperatorHomotopy c T₀ T₁)
    (t : I) (a : A) (x : C(I, E)) :
    (h.fibreCycle t).representation a (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (h.intervalCycle.representation a x) := by
  apply (continuousSectionFibreIsometryEquiv t).injective
  change continuousSectionFibreIsometryEquiv t
    ((continuousSectionFibreIsometryEquiv t).symm
      (c.representation a (continuousSectionFibreIsometryEquiv t (Submodule.Quotient.mk x)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, continuousSectionFibreIsometryEquiv_mk,
    continuousSectionFibreIsometryEquiv_mk]
  rfl

theorem fibreCycle_grading_mk (h : KasparovOperatorHomotopy c T₀ T₁) (t : I) (x : C(I, E)) :
    (h.fibreCycle t).grading.grading (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (h.intervalCycle.grading.grading x) := by
  apply (continuousSectionFibreIsometryEquiv t).injective
  change continuousSectionFibreIsometryEquiv t
    ((continuousSectionFibreIsometryEquiv t).symm
      (c.grading.grading (continuousSectionFibreIsometryEquiv t (Submodule.Quotient.mk x)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, continuousSectionFibreIsometryEquiv_mk,
    continuousSectionFibreIsometryEquiv_mk]
  rfl

theorem fibreCycle_action_mk (h : KasparovOperatorHomotopy c T₀ T₁)
    (t : I) (g : Γ) (x : C(I, E)) :
    (h.fibreCycle t).groupAction.action g (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (h.intervalCycle.groupAction.action g x) := by
  apply (continuousSectionFibreIsometryEquiv t).injective
  change continuousSectionFibreIsometryEquiv t
    ((continuousSectionFibreIsometryEquiv t).symm
      (c.groupAction.action g (continuousSectionFibreIsometryEquiv t (Submodule.Quotient.mk x)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, continuousSectionFibreIsometryEquiv_mk,
    continuousSectionFibreIsometryEquiv_mk]
  rfl

/-- The zero endpoint has the complete original endpoint cycle as its fibre. -/
def fibreCycleZeroIso (h : KasparovOperatorHomotopy c T₀ T₁) :
    KasparovCycleIso (h.fibreCycle 0) (c.withOperator T₀ h.source_conditions) := by
  simpa only [source_cycleAt] using h.fibreCycleIso 0

/-- The one endpoint has the complete original endpoint cycle as its fibre. -/
def fibreCycleOneIso (h : KasparovOperatorHomotopy c T₀ T₁) :
    KasparovCycleIso (h.fibreCycle 1) (c.withOperator T₁ h.target_conditions) := by
  simpa only [target_cycleAt] using h.fibreCycleIso 1

end KasparovOperatorHomotopy
end BC4lean.KKTheory
