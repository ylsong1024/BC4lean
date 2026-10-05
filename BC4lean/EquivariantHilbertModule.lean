import BC4lean.GradedHilbertModule
import BC4lean.RankOneOperator
import Mathlib.Topology.Algebra.MulAction

/-! # Compatible group actions on right Hilbert C⋆-modules

The group acts on the coefficient algebra by actual star-algebra automorphisms
and on the module by actual complex-linear isometry equivalences; the action
laws are bundled as monoid homomorphisms. Inner-product compatibility implies
compatibility with the right coefficient action. Joint continuity is proved for
discrete groups, so in particular for the countable discrete groups in this
project. No countability assumption is needed for these structural laws.

Conjugation by the group action acts on adjointable maps and transports rank-one
maps to rank-one maps, even when the coefficient action is nontrivial.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace

variable {Γ B : Type*} [Group Γ] [NonUnitalCStarAlgebra B]

/-- An action on a possibly nonunital C⋆-algebra by complex star-automorphisms. -/
structure CStarAlgebraAction (Γ B : Type*) [Group Γ] [NonUnitalCStarAlgebra B] where
  automorphism : Γ →* (B ≃⋆ₐ[ℂ] B)

namespace CStarAlgebraAction

/-- The trivial coefficient action. -/
def trivial : CStarAlgebraAction Γ B where
  automorphism := 1

@[simp] theorem one_apply (α : CStarAlgebraAction Γ B) (b : B) :
    α.automorphism 1 b = b := by simp

@[simp] theorem mul_apply (α : CStarAlgebraAction Γ B) (g h : Γ) (b : B) :
    α.automorphism (g * h) b = α.automorphism g (α.automorphism h b) := by
  simp

@[simp] theorem inv_apply_apply (α : CStarAlgebraAction Γ B) (g : Γ) (b : B) :
    α.automorphism g⁻¹ (α.automorphism g b) = b := by
  rw [← α.mul_apply, inv_mul_cancel, α.one_apply]

@[simp] theorem apply_inv_apply (α : CStarAlgebraAction Γ B) (g : Γ) (b : B) :
    α.automorphism g (α.automorphism g⁻¹ b) = b := by
  rw [← α.mul_apply, mul_inv_cancel, α.one_apply]

/-- The associated coefficient action satisfies the Mathlib `MulAction` laws. -/
@[instance_reducible] def mulAction (α : CStarAlgebraAction Γ B) : MulAction Γ B where
  smul g b := α.automorphism g b
  one_smul := α.one_apply
  mul_smul := α.mul_apply

/-- A grading-preserving action on the coefficient algebra. -/
def PreservesGrading (α : CStarAlgebraAction Γ B) (β : CStarGrading B) : Prop :=
  ∀ g b, α.automorphism g (β.automorphism b) = β.automorphism (α.automorphism g b)

@[simp] theorem preservesGrading_trivial (α : CStarAlgebraAction Γ B) :
    α.PreservesGrading CStarGrading.trivial := fun _ _ => rfl

/-- A discrete coefficient action is jointly continuous. -/
theorem continuous_action [TopologicalSpace Γ] [DiscreteTopology Γ]
    (α : CStarAlgebraAction Γ B) :
    Continuous (fun p : Γ × B => α.automorphism p.1 p.2) :=
  continuous_prod_of_discrete_left.mpr fun g => (StarAlgEquiv.isometry (α.automorphism g)).continuous

/-- Continuity for the bundled coefficient `MulAction`. -/
theorem continuousSMul [TopologicalSpace Γ] [DiscreteTopology Γ]
    (α : CStarAlgebraAction Γ B) :
    letI : MulAction Γ B := α.mulAction
    ContinuousSMul Γ B := by
  let : MulAction Γ B := α.mulAction
  exact ⟨α.continuous_action⟩

end CStarAlgebraAction

variable [PartialOrder B]
variable {E F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H]

/-- A compatible isometric group action on a right pre-Hilbert module. -/
structure EquivariantHilbertModule (α : CStarAlgebraAction Γ B) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] where
  action : Γ →* (E ≃ₗᵢ[ℂ] E)
  inner_action : ∀ g x y,
    ⟪action g x, action g y⟫_(Bᵐᵒᵖ) =
      opStarAlgEquiv (α.automorphism g) ⟪x, y⟫_(Bᵐᵒᵖ)

namespace EquivariantHilbertModule

variable {α : CStarAlgebraAction Γ B}

@[simp] theorem one_apply (U : EquivariantHilbertModule α E) (x : E) :
    U.action 1 x = x := by simp

@[simp] theorem mul_apply (U : EquivariantHilbertModule α E) (g h : Γ) (x : E) :
    U.action (g * h) x = U.action g (U.action h x) := by simp

@[simp] theorem inv_apply_apply (U : EquivariantHilbertModule α E) (g : Γ) (x : E) :
    U.action g⁻¹ (U.action g x) = x := by
  rw [← U.mul_apply, inv_mul_cancel, U.one_apply]

@[simp] theorem apply_inv_apply (U : EquivariantHilbertModule α E) (g : Γ) (x : E) :
    U.action g (U.action g⁻¹ x) = x := by
  rw [← U.mul_apply, mul_inv_cancel, U.one_apply]

/-- Compatibility with right coefficients follows from inner-product compatibility. -/
@[simp] theorem map_op_smul (U : EquivariantHilbertModule α E) (g : Γ)
    (a : Bᵐᵒᵖ) (x : E) :
    U.action g (a • x) = opStarAlgEquiv (α.automorphism g) a • U.action g x := by
  apply module_inner_ext_left (B := B)
  intro z
  obtain ⟨y, rfl⟩ := (U.action g).surjective z
  rw [U.inner_action, CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_left,
    U.inner_action, map_mul, map_star]

/-- The associated module action has identity and multiplication laws. -/
@[instance_reducible] def mulAction (U : EquivariantHilbertModule α E) : MulAction Γ E where
  smul g x := U.action g x
  one_smul := U.one_apply
  mul_smul := U.mul_apply

/-- Every group element acts isometrically. -/
theorem isometry (U : EquivariantHilbertModule α E) (g : Γ) : Isometry (U.action g) :=
  (U.action g).isometry

/-- Joint continuity of the action for a discrete group. -/
theorem continuous_action [TopologicalSpace Γ] [DiscreteTopology Γ]
    (U : EquivariantHilbertModule α E) :
    Continuous (fun p : Γ × E => U.action p.1 p.2) :=
  continuous_prod_of_discrete_left.mpr fun g => (U.action g).continuous

/-- Continuity for the bundled module `MulAction`. -/
theorem continuousSMul [TopologicalSpace Γ] [DiscreteTopology Γ]
    (U : EquivariantHilbertModule α E) :
    letI : MulAction Γ E := U.mulAction
    ContinuousSMul Γ E := by
  let : MulAction Γ E := U.mulAction
  exact ⟨U.continuous_action⟩

/-- The trivial compatible module action over the trivial coefficient action. -/
def trivial : EquivariantHilbertModule (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B) E where
  action := 1
  inner_action g x y := by rfl

/-- Compatibility of an action with a module grading. -/
def PreservesGrading {β : CStarGrading B} (U : EquivariantHilbertModule α E)
    (γ : GradedHilbertModule β E) : Prop :=
  ∀ g x, U.action g (γ.grading x) = γ.grading (U.action g x)

/-- Moving the group action through an inner product twists its coefficient. -/
theorem inner_action_left (U : EquivariantHilbertModule α E) (g : Γ) (x y : E) :
    ⟪U.action g x, y⟫_(Bᵐᵒᵖ) =
      opStarAlgEquiv (α.automorphism g) ⟪x, U.action g⁻¹ y⟫_(Bᵐᵒᵖ) := by
  simpa only [apply_inv_apply] using U.inner_action g x (U.action g⁻¹ y)

theorem inner_action_right (U : EquivariantHilbertModule α E) (g : Γ) (x y : E) :
    opStarAlgEquiv (α.automorphism g) ⟪U.action g⁻¹ x, y⟫_(Bᵐᵒᵖ) =
      ⟪x, U.action g y⟫_(Bᵐᵒᵖ) := by
  simpa only [apply_inv_apply] using (U.inner_action g (U.action g⁻¹ x) y).symm

/-- Transport an adjointable map by compatible source and target actions. -/
def conjugateMap (U : EquivariantHilbertModule α E) (V : EquivariantHilbertModule α F)
    (g : Γ) (T : AdjointableMap B E F) : AdjointableMap B E F where
  toCLM := (V.action g).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (T.toCLM.comp (U.action g⁻¹).toContinuousLinearEquiv.toContinuousLinearMap)
  adjointCLM := (U.action g).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (T.adjointCLM.comp (V.action g⁻¹).toContinuousLinearEquiv.toContinuousLinearMap)
  adjoint_identity x y := by
    change ⟪V.action g (T (U.action g⁻¹ x)), y⟫_(Bᵐᵒᵖ) =
      ⟪x, U.action g (T.adjointCLM (V.action g⁻¹ y))⟫_(Bᵐᵒᵖ)
    rw [V.inner_action_left, T.adjoint_identity, U.inner_action_right]

/-- Conjugation of an operator by a compatible group action. -/
abbrev conjugateOperator (U : EquivariantHilbertModule α E) (g : Γ)
    (T : AdjointableMap B E E) : AdjointableMap B E E := U.conjugateMap U g T

@[simp] theorem conjugateMap_apply (U : EquivariantHilbertModule α E)
    (V : EquivariantHilbertModule α F) (g : Γ) (T : AdjointableMap B E F) (x : E) :
    U.conjugateMap V g T x = V.action g (T (U.action g⁻¹ x)) := rfl

@[simp] theorem conjugateMap_adjoint (U : EquivariantHilbertModule α E)
    (V : EquivariantHilbertModule α F) (g : Γ) (T : AdjointableMap B E F) :
    (U.conjugateMap V g T).adjoint = V.conjugateMap U g T.adjoint := rfl

@[simp] theorem conjugateMap_one (U : EquivariantHilbertModule α E)
    (V : EquivariantHilbertModule α F) (T : AdjointableMap B E F) :
    U.conjugateMap V 1 T = T := by
  ext x
  simp

@[simp] theorem conjugateMap_zero (U : EquivariantHilbertModule α E)
    (V : EquivariantHilbertModule α F) (g : Γ) :
    U.conjugateMap V g AdjointableMap.zero = AdjointableMap.zero := by
  ext x
  simp

@[simp] theorem conjugateOperator_zero (U : EquivariantHilbertModule α E) (g : Γ) :
    U.conjugateOperator g AdjointableMap.zero = AdjointableMap.zero := U.conjugateMap_zero U g

/-- Conjugation is an actual group action on adjointable maps. -/
theorem conjugateMap_mul (U : EquivariantHilbertModule α E)
    (V : EquivariantHilbertModule α F) (g h : Γ) (T : AdjointableMap B E F) :
    U.conjugateMap V (g * h) T = U.conjugateMap V g (U.conjugateMap V h T) := by
  ext x
  simp only [conjugateMap_apply, mul_apply, mul_inv_rev]

/-- The induced action on adjointable maps satisfies the Mathlib action laws. -/
@[instance_reducible] def mapMulAction (U : EquivariantHilbertModule α E) (V : EquivariantHilbertModule α F) :
    MulAction Γ (AdjointableMap B E F) where
  smul g T := U.conjugateMap V g T
  one_smul := U.conjugateMap_one V
  mul_smul g h T := U.conjugateMap_mul V g h T

/-- Conjugation is contractive for the operator norm. -/
theorem conjugateMap_norm_le (U : EquivariantHilbertModule α E)
    (V : EquivariantHilbertModule α F) (g : Γ) (T : AdjointableMap B E F) :
    ‖(U.conjugateMap V g T).toCLM‖ ≤ ‖T.toCLM‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖V.action g (T (U.action g⁻¹ x))‖ ≤ ‖T.toCLM‖ * ‖x‖
  rw [(V.action g).norm_map]
  simpa only [(U.action g⁻¹).norm_map] using T.toCLM.le_opNorm (U.action g⁻¹ x)

/-- The operator norm is invariant under conjugation. -/
theorem conjugateMap_norm (U : EquivariantHilbertModule α E)
    (V : EquivariantHilbertModule α F) (g : Γ) (T : AdjointableMap B E F) :
    ‖(U.conjugateMap V g T).toCLM‖ = ‖T.toCLM‖ := by
  apply le_antisymm (U.conjugateMap_norm_le V g T)
  have h : U.conjugateMap V g⁻¹ (U.conjugateMap V g T) = T := by
    rw [← U.conjugateMap_mul, inv_mul_cancel, U.conjugateMap_one]
  calc
    ‖T.toCLM‖ = ‖(U.conjugateMap V g⁻¹ (U.conjugateMap V g T)).toCLM‖ := by rw [h]
    _ ≤ ‖(U.conjugateMap V g T).toCLM‖ :=
      U.conjugateMap_norm_le V g⁻¹ (U.conjugateMap V g T)

@[simp] theorem conjugateMap_add (U : EquivariantHilbertModule α E)
    (V : EquivariantHilbertModule α F) (g : Γ) (S T : AdjointableMap B E F) :
    U.conjugateMap V g (S.add T) = (U.conjugateMap V g S).add (U.conjugateMap V g T) := by
  ext x
  simp only [conjugateMap_apply, AdjointableMap.add_apply, map_add]

@[simp] theorem conjugateMap_smul (U : EquivariantHilbertModule α E)
    (V : EquivariantHilbertModule α F) (g : Γ) (T : AdjointableMap B E F) (c : ℂ) :
    U.conjugateMap V g (T.smul c) = (U.conjugateMap V g T).smul c := by
  ext x
  simp only [conjugateMap_apply, AdjointableMap.smul_apply, map_smul]

@[simp] theorem conjugateOperator_id (U : EquivariantHilbertModule α E) (g : Γ) :
    U.conjugateOperator g AdjointableMap.id = AdjointableMap.id := by
  ext x
  simp

/-- Conjugation respects composition. -/
theorem conjugateMap_comp (U : EquivariantHilbertModule α E)
    (V : EquivariantHilbertModule α F) (W : EquivariantHilbertModule α H)
    (g : Γ) (S : AdjointableMap B F H) (T : AdjointableMap B E F) :
    U.conjugateMap W g (S.comp T) = (V.conjugateMap W g S).comp (U.conjugateMap V g T) := by
  ext x
  simp only [conjugateMap_apply, AdjointableMap.comp_apply, inv_apply_apply]

/-- Conjugation preserves even maps when the module actions preserve grading. -/
theorem conjugateMap_isEven {β : CStarGrading B}
    (U : EquivariantHilbertModule α E) (V : EquivariantHilbertModule α F)
    {γE : GradedHilbertModule β E} {γF : GradedHilbertModule β F}
    (hU : U.PreservesGrading γE) (hV : V.PreservesGrading γF)
    (g : Γ) {T : AdjointableMap B E F} (hT : GradedHilbertModule.IsEven γE γF T) :
    GradedHilbertModule.IsEven γE γF (U.conjugateMap V g T) := by
  intro x
  simp only [conjugateMap_apply]
  rw [← hV g, hT, ← hU g⁻¹]

/-- Conjugation preserves odd maps when the module actions preserve grading. -/
theorem conjugateMap_isOdd {β : CStarGrading B}
    (U : EquivariantHilbertModule α E) (V : EquivariantHilbertModule α F)
    {γE : GradedHilbertModule β E} {γF : GradedHilbertModule β F}
    (hU : U.PreservesGrading γE) (hV : V.PreservesGrading γF)
    (g : Γ) {T : AdjointableMap B E F} (hT : GradedHilbertModule.IsOdd γE γF T) :
    GradedHilbertModule.IsOdd γE γF (U.conjugateMap V g T) := by
  intro x
  simp only [conjugateMap_apply]
  rw [← hV g, hT, ← hU g⁻¹]
  exact map_neg (V.action g) _

variable [StarOrderedRing B]

/-- Rank-one operators transform by the same action on both vectors. -/
theorem conjugateMap_rankOne (U : EquivariantHilbertModule α E)
    (V : EquivariantHilbertModule α F) (g : Γ) (x : F) (y : E) :
    U.conjugateMap V g (moduleRankOne x y) =
      moduleRankOne (V.action g x) (U.action g y) := by
  ext z
  simp only [conjugateMap_apply, moduleRankOne_apply, map_op_smul]
  rw [← U.inner_action_left]

end EquivariantHilbertModule
end BC4lean.KKTheory
