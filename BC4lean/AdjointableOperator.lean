import BC4lean.HilbertCStarModule

/-! # Adjointable maps of right Hilbert C⋆-modules

An adjointable map is a bounded complex-linear map with a bounded adjoint for
the coefficient-valued inner product. Module linearity is proved from the
adjoint identity. Completeness is not needed for these algebraic identities.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace
open CStarModule

variable {B E F G H : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H]

/-- A bounded adjointable map, storing its uniquely determined adjoint. -/
structure AdjointableMap (B E F : Type*) [NonUnitalCStarAlgebra B]
    [PartialOrder B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] where
  toCLM : E →L[ℂ] F
  adjointCLM : F →L[ℂ] E
  adjoint_identity : ∀ x y, ⟪toCLM x, y⟫_(Bᵐᵒᵖ) = ⟪x, adjointCLM y⟫_(Bᵐᵒᵖ)

namespace AdjointableMap

instance instCoeFun : CoeFun (AdjointableMap B E F) (fun _ => E → F) := ⟨fun T => T.toCLM⟩

/-- Uniqueness of an adjoint. -/
theorem adjoint_unique (T : AdjointableMap B E F) (S : F →L[ℂ] E)
    (hS : ∀ x y, ⟪T x, y⟫_(Bᵐᵒᵖ) = ⟪x, S y⟫_(Bᵐᵒᵖ)) : S = T.adjointCLM := by
  ext y
  apply module_inner_ext_right (B := B)
  intro x
  rw [← hS, T.adjoint_identity]

@[ext] theorem ext {S T : AdjointableMap B E F} (h : ∀ x, S x = T x) : S = T := by
  have hf : S.toCLM = T.toCLM := ContinuousLinearMap.ext h
  have ha : S.adjointCLM = T.adjointCLM := T.adjoint_unique S.adjointCLM (by
    intro x y
    rw [← h x]
    exact S.adjoint_identity x y)
  cases S
  cases T
  cases hf
  cases ha
  rfl

/-- Every adjointable complex-linear map respects the right coefficient action. -/
@[simp] theorem map_op_smul (T : AdjointableMap B E F) (a : Bᵐᵒᵖ) (x : E) :
    T (a • x) = a • T x := by
  apply module_inner_ext_left (B := B)
  intro y
  rw [T.adjoint_identity, inner_op_smul_left, inner_op_smul_left, T.adjoint_identity]

/-- The adjoint as an adjointable map in the reverse direction. -/
def adjoint (T : AdjointableMap B E F) : AdjointableMap B F E where
  toCLM := T.adjointCLM
  adjointCLM := T.toCLM
  adjoint_identity x y := by
    simpa only [CStarModule.star_inner] using (congrArg star (T.adjoint_identity y x)).symm

@[simp] theorem adjoint_adjoint (T : AdjointableMap B E F) : T.adjoint.adjoint = T := rfl

/-- Zero adjointable map. -/
def zero : AdjointableMap B E F where
  toCLM := 0
  adjointCLM := 0
  adjoint_identity _ _ := by simp

@[simp] theorem zero_apply (x : E) : (zero : AdjointableMap B E F) x = 0 := rfl

@[simp] theorem adjoint_zero : (zero : AdjointableMap B E F).adjoint = zero := rfl

/-- Identity adjointable operator. -/
def id : AdjointableMap B E E where
  toCLM := ContinuousLinearMap.id ℂ E
  adjointCLM := ContinuousLinearMap.id ℂ E
  adjoint_identity _ _ := rfl

@[simp] theorem id_apply (x : E) : (id : AdjointableMap B E E) x = x := rfl

@[simp] theorem adjoint_id : (id : AdjointableMap B E E).adjoint = id := rfl

/-- Composition, with the adjoints in reverse order. -/
def comp (S : AdjointableMap B F G) (T : AdjointableMap B E F) : AdjointableMap B E G where
  toCLM := S.toCLM.comp T.toCLM
  adjointCLM := T.adjointCLM.comp S.adjointCLM
  adjoint_identity x y := by
    change ⟪S (T x), y⟫_(Bᵐᵒᵖ) = ⟪x, T.adjointCLM (S.adjointCLM y)⟫_(Bᵐᵒᵖ)
    rw [S.adjoint_identity, T.adjoint_identity]

@[simp] theorem comp_apply (S : AdjointableMap B F G) (T : AdjointableMap B E F) (x : E) :
    S.comp T x = S (T x) := rfl

@[simp] theorem adjoint_comp (S : AdjointableMap B F G) (T : AdjointableMap B E F) :
    (S.comp T).adjoint = T.adjoint.comp S.adjoint := rfl

@[simp] theorem id_comp (T : AdjointableMap B E F) : id.comp T = T := by ext; rfl

@[simp] theorem comp_id (T : AdjointableMap B E F) : T.comp id = T := by ext; rfl

theorem comp_assoc (R : AdjointableMap B G H) (S : AdjointableMap B F G)
    (T : AdjointableMap B E F) : (R.comp S).comp T = R.comp (S.comp T) := by ext; rfl

/-- Sum of adjointable maps. -/
def add (S T : AdjointableMap B E F) : AdjointableMap B E F where
  toCLM := S.toCLM + T.toCLM
  adjointCLM := S.adjointCLM + T.adjointCLM
  adjoint_identity x y := by
    change ⟪S x + T x, y⟫_(Bᵐᵒᵖ) = ⟪x, S.adjointCLM y + T.adjointCLM y⟫_(Bᵐᵒᵖ)
    rw [CStarModule.inner_add_left, CStarModule.inner_add_right, S.adjoint_identity, T.adjoint_identity]

@[simp] theorem add_apply (S T : AdjointableMap B E F) (x : E) :
    S.add T x = S x + T x := rfl

@[simp] theorem adjoint_add (S T : AdjointableMap B E F) :
    (S.add T).adjoint = S.adjoint.add T.adjoint := rfl

/-- Complex scalar multiplication; the adjoint is conjugate-linear. -/
def smul (c : ℂ) (T : AdjointableMap B E F) : AdjointableMap B E F where
  toCLM := c • T.toCLM
  adjointCLM := star c • T.adjointCLM
  adjoint_identity x y := by
    change ⟪c • T x, y⟫_(Bᵐᵒᵖ) = ⟪x, star c • T.adjointCLM y⟫_(Bᵐᵒᵖ)
    rw [inner_smul_left_complex, inner_smul_right_complex, T.adjoint_identity]

@[simp] theorem smul_apply (c : ℂ) (T : AdjointableMap B E F) (x : E) :
    T.smul c x = c • T x := rfl

@[simp] theorem adjoint_smul (c : ℂ) (T : AdjointableMap B E F) :
    (T.smul c).adjoint = T.adjoint.smul (star c) := by ext; rfl

end AdjointableMap
end BC4lean.KKTheory
