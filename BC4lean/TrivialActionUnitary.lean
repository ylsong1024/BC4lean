import BC4lean.EquivariantHilbertModule
import BC4lean.HilbertModuleEquiv
import Mathlib.Algebra.Star.Unitary

/-!
# An actual trivial-coefficient module action as a unitary representation




Input is an already constructed `EquivariantHilbertModule` over the trivial
coefficient action. This helper does not assume or construct a descent action.
No completeness, countability, amenability, or exactness assumption is used.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

namespace EquivariantHilbertModule

variable {Γ C H : Type*} [Group Γ]
  [NonUnitalCStarAlgebra C] [PartialOrder C]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [SMul Cᵐᵒᵖ H] [CStarModule Cᵐᵒᵖ H]

variable (W : EquivariantHilbertModule
  (CStarAlgebraAction.trivial : CStarAlgebraAction Γ C) H)

/-- Each actual action is a coefficient-form unitary when coefficients act trivially. -/
def trivialActionHilbertEquiv (g : Γ) : HilbertModuleEquiv C H H where
  linearIsometryEquiv := W.action g
  inner_map x y := by
    have h := W.inner_action g x y
    change ⟪W.action g x, W.action g y⟫_(Cᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪x, y⟫_(Cᵐᵒᵖ)) at h
    simpa only [MulOpposite.op_unop] using h

@[simp] theorem trivialActionHilbertEquiv_apply (g : Γ) (x : H) :
    W.trivialActionHilbertEquiv g x = W.action g x := rfl

/-- The same genuine action as an adjointable coefficient-linear operator. -/
def trivialActionOperator (g : Γ) : AdjointableMap C H H :=
  (W.trivialActionHilbertEquiv g).toAdjointable

@[simp] theorem trivialActionOperator_apply (g : Γ) (x : H) :
    W.trivialActionOperator g x = W.action g x := rfl

/-- The stored adjoint is exactly the actual inverse group action. -/
@[simp] theorem trivialActionOperator_adjoint (g : Γ) :
    (W.trivialActionOperator g).adjoint = W.trivialActionOperator g⁻¹ := by
  apply AdjointableMap.ext
  intro x
  change (W.action g).symm x = W.action g⁻¹ x
  apply (W.action g).injective
  rw [LinearIsometryEquiv.apply_symm_apply, W.apply_inv_apply]

@[simp] theorem trivialActionOperator_star (g : Γ) :
    star (W.trivialActionOperator g) = W.trivialActionOperator g⁻¹ :=
  W.trivialActionOperator_adjoint g

@[simp] theorem trivialActionOperator_one :
    W.trivialActionOperator 1 = (1 : AdjointableMap C H H) := by
  apply AdjointableMap.ext
  intro x
  change W.action 1 x = x
  exact W.one_apply x

@[simp] theorem trivialActionOperator_mul (g h : Γ) :
    W.trivialActionOperator (g * h) =
      W.trivialActionOperator g * W.trivialActionOperator h := by
  apply AdjointableMap.ext
  intro x
  change W.action (g * h) x = W.action g (W.action h x)
  exact W.mul_apply g h x

/-- The two unitary equations follow from the two actual group inverse laws. -/
def trivialActionUnitary (g : Γ) : unitary (AdjointableMap C H H) :=
  ⟨W.trivialActionOperator g, Unitary.mem_iff.mpr (by
    constructor
    · apply AdjointableMap.ext
      intro x
      change (W.trivialActionOperator g).adjoint
        (W.trivialActionOperator g x) = x
      rw [W.trivialActionOperator_adjoint]
      change W.action g⁻¹ (W.action g x) = x
      exact W.inv_apply_apply g x
    · apply AdjointableMap.ext
      intro x
      change W.trivialActionOperator g
        ((W.trivialActionOperator g).adjoint x) = x
      rw [W.trivialActionOperator_adjoint]
      change W.action g (W.action g⁻¹ x) = x
      exact W.apply_inv_apply g x)⟩

@[simp] theorem trivialActionUnitary_coe (g : Γ) :
    (W.trivialActionUnitary g : AdjointableMap C H H) =
      W.trivialActionOperator g := rfl

/-- The actual given group action, bundled into the unitary group of adjointables. -/
def trivialActionUnitaryHom : Γ →* unitary (AdjointableMap C H H) where
  toFun := W.trivialActionUnitary
  map_one' := by
    apply Subtype.ext
    change W.trivialActionOperator 1 = (1 : AdjointableMap C H H)
    exact W.trivialActionOperator_one
  map_mul' g h := by
    apply Subtype.ext
    change W.trivialActionOperator (g * h) =
      W.trivialActionOperator g * W.trivialActionOperator h
    exact W.trivialActionOperator_mul g h

@[simp] theorem trivialActionUnitaryHom_coe (g : Γ) :
    (W.trivialActionUnitaryHom g : AdjointableMap C H H) =
      W.trivialActionOperator g := rfl

@[simp] theorem trivialActionUnitaryHom_apply (g : Γ) (x : H) :
    (W.trivialActionUnitaryHom g : AdjointableMap C H H) x =
      W.action g x := rfl

@[simp] theorem trivialActionUnitaryHom_adjoint (g : Γ) :
    (W.trivialActionUnitaryHom g : AdjointableMap C H H).adjoint =
      (W.trivialActionUnitaryHom g⁻¹ : AdjointableMap C H H) :=
  W.trivialActionOperator_adjoint g

@[simp] theorem trivialActionUnitaryHom_star (g : Γ) :
    star (W.trivialActionUnitaryHom g : AdjointableMap C H H) =
      (W.trivialActionUnitaryHom g⁻¹ : AdjointableMap C H H) :=
  W.trivialActionOperator_star g

/-- The abstract module-action conjugate equals conjugation by the actual operator. -/
theorem trivialActionOperator_conjugate (g : Γ) (T : AdjointableMap C H H) :
    W.conjugateOperator g T =
      W.trivialActionOperator g * T * star (W.trivialActionOperator g) := by
  rw [W.trivialActionOperator_star]
  apply AdjointableMap.ext
  intro x
  rfl

/-- Moving the genuine action to the left conjugates T by the inverse element. -/
theorem trivialActionOperator_intertwine (g : Γ) (T : AdjointableMap C H H) :
    T * W.trivialActionOperator g =
      W.trivialActionOperator g * W.conjugateOperator g⁻¹ T := by
  apply AdjointableMap.ext
  intro x
  change T (W.action g x) =
    W.action g (W.action g⁻¹ (T (W.action (g⁻¹)⁻¹ x)))
  rw [inv_inv, W.apply_inv_apply]

/-- The conjugation identity with the bundled unitary representation. -/
theorem trivialActionUnitaryHom_conjugate (g : Γ) (T : AdjointableMap C H H) :
    W.conjugateOperator g T =
      (W.trivialActionUnitaryHom g : AdjointableMap C H H) * T *
        star (W.trivialActionUnitaryHom g : AdjointableMap C H H) :=
  W.trivialActionOperator_conjugate g T

/-- The requested intertwining identity with the bundled unitary representation. -/
theorem trivialActionUnitaryHom_intertwine (g : Γ) (T : AdjointableMap C H H) :
    T * (W.trivialActionUnitaryHom g : AdjointableMap C H H) =
      (W.trivialActionUnitaryHom g : AdjointableMap C H H) *
        W.conjugateOperator g⁻¹ T :=
  W.trivialActionOperator_intertwine g T

end EquivariantHilbertModule
end BC4lean.KKTheory

