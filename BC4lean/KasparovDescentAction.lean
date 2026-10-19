import BC4lean.ReducedCrossedLeftRegular
import BC4lean.TrivialActionUnitary

/-! # The actual diagonal unitary action on the reduced coefficient extension

The two original factor maps are the given semilinear
action on E and the actual left regular multiplier on the standard crossed
module.  The existing completed interior-tensor construction proves that
these maps respect balancing and the null quotient, preserve the norm, and
extend with actual inverses to the completion.  No such conclusion is assumed.

The original source coefficient representation is induced by T ↦ T ⊗ 1.
Its covariance is proved here.  Reduced-norm continuity of finite integrated
source sums is a separate theorem; no representation of the completed source
crossed product and no KK descent map is declared here.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent

open scoped InnerProductSpace KasparovDescent

variable {Γ B : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  (β : CStarAlgebraAction Γ B) (E : Type*)
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- The actual diagonal group action on the genuine completed coefficient
extension.  The right crossed coefficients have the trivial action. -/
def groupAction (U : EquivariantHilbertModule β E) :
    EquivariantHilbertModule
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ (ReducedCrossedProduct β))
      (Module β E) :=
  U.interiorTensor (leftRegularAction β) (coefficientRepresentation_equivariant β)

/-- The actual formula on elementary vectors, after balancing and completion. -/
@[simp] theorem groupAction_mk (U : EquivariantHilbertModule β E) (g : Γ)
    (x : E) (c : (ReducedCrossedProduct β)ᵐᵒᵖ) :
    (groupAction β E U).action g (mk β E x c) =
      mk β E (U.action g x)
        (MulOpposite.op (leftRegular β g (MulOpposite.unop c))) :=
  U.interiorTensor_action_mk (leftRegularAction β)
    (coefficientRepresentation_equivariant β) g x c

/-- The diagonal action preserves the whole crossed coefficient inner product. -/
theorem groupAction_inner (U : EquivariantHilbertModule β E) (g : Γ)
    (x y : Module β E) :
    ⟪(groupAction β E U).action g x,
        (groupAction β E U).action g y⟫_((ReducedCrossedProduct β)ᵐᵒᵖ) =
      ⟪x, y⟫_((ReducedCrossedProduct β)ᵐᵒᵖ) := by
  have h := (groupAction β E U).inner_action g x y
  change ⟪(groupAction β E U).action g x,
      (groupAction β E U).action g y⟫_((ReducedCrossedProduct β)ᵐᵒᵖ) =
    MulOpposite.op (MulOpposite.unop
      ⟪x, y⟫_((ReducedCrossedProduct β)ᵐᵒᵖ)) at h
  simpa only [MulOpposite.op_unop] using h

/-- The actual tensor action conjugates T ⊗ 1 to the tensor of the original
conjugated operator. -/
theorem groupAction_conjugateOperator (U : EquivariantHilbertModule β E)
    (g : Γ) (T : AdjointableMap B E E) :
    (groupAction β E U).conjugateOperator g (operatorHom β E T) =
      operatorHom β E (U.conjugateOperator g T) :=
  U.interiorTensor_conjugateOperator (leftRegularAction β)
    (coefficientRepresentation_equivariant β) g T

/-- The group acts by genuine coefficient-linear adjointable unitaries. -/
def groupUnitaryHom (U : EquivariantHilbertModule β E) :
    Γ →* unitary
      (AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E)) :=
  (groupAction β E U).trivialActionUnitaryHom

/-- The actual group operator on the completed module. -/
def groupOperator (U : EquivariantHilbertModule β E) (g : Γ) :
    AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) :=
  (groupAction β E U).trivialActionOperator g

@[simp] theorem groupOperator_apply (U : EquivariantHilbertModule β E)
    (g : Γ) (x : Module β E) :
    groupOperator β E U g x = (groupAction β E U).action g x := rfl

@[simp] theorem groupUnitaryHom_coe (U : EquivariantHilbertModule β E) (g : Γ) :
    (groupUnitaryHom β E U g :
      AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E)) =
      groupOperator β E U g := rfl

@[simp] theorem groupOperator_mk (U : EquivariantHilbertModule β E) (g : Γ)
    (x : E) (c : (ReducedCrossedProduct β)ᵐᵒᵖ) :
    groupOperator β E U g (mk β E x c) =
      mk β E (U.action g x)
        (MulOpposite.op (leftRegular β g (MulOpposite.unop c))) :=
  groupAction_mk β E U g x c

@[simp] theorem groupOperator_adjoint (U : EquivariantHilbertModule β E) (g : Γ) :
    (groupOperator β E U g).adjoint = groupOperator β E U g⁻¹ :=
  (groupAction β E U).trivialActionOperator_adjoint g

@[simp] theorem groupOperator_star (U : EquivariantHilbertModule β E) (g : Γ) :
    star (groupOperator β E U g) = groupOperator β E U g⁻¹ :=
  groupOperator_adjoint β E U g

@[simp] theorem groupOperator_one (U : EquivariantHilbertModule β E) :
    groupOperator β E U 1 = 1 :=
  (groupAction β E U).trivialActionOperator_one

@[simp] theorem groupOperator_mul (U : EquivariantHilbertModule β E) (g h : Γ) :
    groupOperator β E U (g * h) =
      groupOperator β E U g * groupOperator β E U h :=
  (groupAction β E U).trivialActionOperator_mul g h

theorem groupOperator_mem_unitary (U : EquivariantHilbertModule β E) (g : Γ) :
    groupOperator β E U g ∈ unitary
      (AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E)) :=
  (groupUnitaryHom β E U g).property

/-- Conjugation by the actual group unitary is the tensor of the original
semilinear conjugation. -/
theorem groupOperator_conjugate (U : EquivariantHilbertModule β E)
    (g : Γ) (T : AdjointableMap B E E) :
    groupOperator β E U g * operatorHom β E T * star (groupOperator β E U g) =
      operatorHom β E (U.conjugateOperator g T) := by
  calc
    _ = (groupAction β E U).conjugateOperator g (operatorHom β E T) := by
      simpa only [groupOperator] using
        ((groupAction β E U).trivialActionOperator_conjugate g (operatorHom β E T)).symm
    _ = _ := groupAction_conjugateOperator β E U g T

/-- The orientation used for localized compact defects of F ⊗ 1. -/
theorem operatorHom_mul_groupOperator (U : EquivariantHilbertModule β E)
    (g : Γ) (T : AdjointableMap B E E) :
    operatorHom β E T * groupOperator β E U g =
      groupOperator β E U g * operatorHom β E (U.conjugateOperator g⁻¹ T) := by
  simpa only [groupOperator, groupAction_conjugateOperator] using
    (groupAction β E U).trivialActionOperator_intertwine g (operatorHom β E T)

/-- The actual diagonal action is jointly continuous for a discrete group. -/
theorem groupAction_continuous [TopologicalSpace Γ] [DiscreteTopology Γ]
    (U : EquivariantHilbertModule β E) :
    Continuous (fun p : Γ × Module β E => (groupAction β E U).action p.1 p.2) :=
  (groupAction β E U).continuous_action

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- The original source coefficients act by the genuine induced first-factor
operators.  This does not integrate or complete the group direction. -/
def sourceRepresentation (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E) :
    A →⋆ₙₐ[ℂ] AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) :=
  (operatorHom β E).toNonUnitalStarAlgHom.comp π

@[simp] theorem sourceRepresentation_apply
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E) (a : A) :
    sourceRepresentation β E π a = operatorHom β E (π a) := rfl

/-- Original source equivariance gives actual covariance of the induced
source coefficients and the constructed group unitaries. -/
theorem sourceRepresentation_equivariant
    (α : CStarAlgebraAction Γ A) (U : EquivariantHilbertModule β E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))
    (g : Γ) (a : A) :
    (groupAction β E U).conjugateOperator g (sourceRepresentation β E π a) =
      sourceRepresentation β E π (α.automorphism g a) := by
  simpa only [sourceRepresentation_apply, hπ] using
    groupAction_conjugateOperator β E U g (π a)

/-- The covariant-pair equation holds in the actual adjointable algebra. -/
theorem sourceRepresentation_covariance
    (α : CStarAlgebraAction Γ A) (U : EquivariantHilbertModule β E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))
    (g : Γ) (a : A) :
    sourceRepresentation β E π (α.automorphism g a) * groupOperator β E U g =
      groupOperator β E U g * sourceRepresentation β E π a := by
  have h := congrArg
    (fun T : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) =>
      T * groupOperator β E U g) (groupOperator_conjugate β E U g (π a))
  rw [hπ g a] at h
  simpa only [sourceRepresentation_apply, mul_assoc,
    (groupOperator_mem_unitary β E U g).1, mul_one] using h.symm

/-- The concrete covariant generator on the actual descended module. -/
def sourceGenerator (U : EquivariantHilbertModule β E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E) (a : A) (g : Γ) :
    AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) :=
  sourceRepresentation β E π a * groupOperator β E U g

@[simp] theorem sourceGenerator_mk (U : EquivariantHilbertModule β E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E) (a : A) (g : Γ)
    (x : E) (c : (ReducedCrossedProduct β)ᵐᵒᵖ) :
    sourceGenerator β E U π a g (mk β E x c) =
      mk β E (π a (U.action g x))
        (MulOpposite.op (leftRegular β g (MulOpposite.unop c))) := by
  simp only [sourceGenerator, AdjointableMap.mul_apply, sourceRepresentation_apply,
    groupOperator_mk, operatorHom_mk]

/-- Covariance puts the group operator first and twists the coefficient by
the inverse action. This is the useful orientation for localized defects. -/
theorem sourceGenerator_group_first (α : CStarAlgebraAction Γ A)
    (U : EquivariantHilbertModule β E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))
    (a : A) (g : Γ) :
    sourceGenerator β E U π a g =
      groupOperator β E U g * sourceRepresentation β E π (α.automorphism g⁻¹ a) := by
  have h := sourceRepresentation_covariance β E α U π hπ g (α.automorphism g⁻¹ a)
  simpa only [sourceGenerator, α.apply_inv_apply] using h


end BC4lean.KKTheory.KasparovDescent
