import BC4lean.AdjointableOperator
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-! # Gradings on coefficient algebras and Hilbert modules

A grading on a possibly nonunital coefficient algebra is an involutive complex
star-algebra automorphism. A module grading is an involutive complex-linear
isometry transporting its coefficient-valued inner product by that automorphism.
Thus nontrivially graded coefficients are supported. When the coefficient
grading is trivial, the module grading is a selfadjoint unitary adjointable
operator. For a nontrivial coefficient grading it is generally semilinear over
B and is not a B-linear adjointable operator.

Completeness is supplied by `CompleteSpace E` when the module is used as a
Hilbert module; the algebraic grading laws also hold on pre-Hilbert modules.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace

variable {B : Type*} [NonUnitalCStarAlgebra B]

/-- Transport a star-algebra automorphism to the opposite algebra. -/
def opStarAlgEquiv (e : B ≃⋆ₐ[ℂ] B) : Bᵐᵒᵖ ≃⋆ₐ[ℂ] Bᵐᵒᵖ where
  toFun a := MulOpposite.op (e (MulOpposite.unop a))
  invFun a := MulOpposite.op (e.symm (MulOpposite.unop a))
  left_inv a := by simp
  right_inv a := by simp
  map_mul' a b := by simp only [MulOpposite.unop_mul, map_mul, MulOpposite.op_mul]
  map_add' a b := by simp only [MulOpposite.unop_add, map_add, MulOpposite.op_add]
  map_star' a := by simp only [MulOpposite.unop_star, map_star, MulOpposite.op_star]
  map_smul' c a := by simp only [MulOpposite.unop_smul, map_smul, MulOpposite.op_smul]

@[simp] theorem opStarAlgEquiv_apply (e : B ≃⋆ₐ[ℂ] B) (a : Bᵐᵒᵖ) :
    opStarAlgEquiv e a = MulOpposite.op (e (MulOpposite.unop a)) := rfl

/-- A Z/2-grading of a possibly nonunital complex C⋆-algebra. -/
structure CStarGrading (B : Type*) [NonUnitalCStarAlgebra B] where
  automorphism : B ≃⋆ₐ[ℂ] B
  involutive : Function.Involutive automorphism

namespace CStarGrading

/-- The grading concentrated in even degree. -/
def trivial : CStarGrading B where
  automorphism := StarAlgEquiv.refl ℂ B
  involutive _ := rfl

@[simp] theorem trivial_apply (a : B) : (trivial : CStarGrading B).automorphism a = a := rfl

@[simp] theorem automorphism_sq (β : CStarGrading B) (a : B) :
    β.automorphism (β.automorphism a) = a := β.involutive a

@[simp] theorem op_automorphism_sq (β : CStarGrading B) (a : Bᵐᵒᵖ) :
    opStarAlgEquiv β.automorphism (opStarAlgEquiv β.automorphism a) = a := by
  simp

@[simp] theorem op_trivial_apply (a : Bᵐᵒᵖ) :
    opStarAlgEquiv (trivial : CStarGrading B).automorphism a = a := by simp

end CStarGrading

variable [PartialOrder B]
variable {E F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H]

/-- A compatible Z/2-grading on a right pre-Hilbert B-module. -/
structure GradedHilbertModule (β : CStarGrading B) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] where
  grading : E ≃ₗᵢ[ℂ] E
  involutive : Function.Involutive grading
  inner_grading : ∀ x y,
    ⟪grading x, grading y⟫_(Bᵐᵒᵖ) = opStarAlgEquiv β.automorphism ⟪x, y⟫_(Bᵐᵒᵖ)

namespace GradedHilbertModule

variable {β : CStarGrading B}

@[simp] theorem grading_sq (γ : GradedHilbertModule β E) (x : E) :
    γ.grading (γ.grading x) = x := γ.involutive x

/-- The even component of a vector for the Z/2-grading. -/
def evenPart (γ : GradedHilbertModule β E) (x : E) : E :=
  (2 : ℂ)⁻¹ • (x + γ.grading x)

/-- The odd component of a vector for the Z/2-grading. -/
def oddPart (γ : GradedHilbertModule β E) (x : E) : E :=
  (2 : ℂ)⁻¹ • (x - γ.grading x)

@[simp] theorem grading_evenPart (γ : GradedHilbertModule β E) (x : E) :
    γ.grading (γ.evenPart x) = γ.evenPart x := by
  simp only [evenPart, map_smul, map_add, grading_sq]
  rw [add_comm]

@[simp] theorem grading_oddPart (γ : GradedHilbertModule β E) (x : E) :
    γ.grading (γ.oddPart x) = -γ.oddPart x := by
  simp only [oddPart, map_smul, map_sub, grading_sq]
  rw [← smul_neg, neg_sub]

/-- Every vector splits into its even and odd components. -/
theorem evenPart_add_oddPart (γ : GradedHilbertModule β E) (x : E) :
    γ.evenPart x + γ.oddPart x = x := by
  simp only [evenPart, oddPart, ← smul_add]
  have h : (x + γ.grading x) + (x - γ.grading x) = (2 : ℂ) • x := by
    rw [two_smul]
    abel
  rw [h, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]

/-- The even eigenspace is a complex submodule. -/
def evenSubmodule (γ : GradedHilbertModule β E) : Submodule ℂ E where
  carrier := {x | γ.grading x = x}
  zero_mem' := map_zero _
  add_mem' hx hy := by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [map_add, hx, hy]
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [map_smul, hx]

/-- The odd eigenspace is a complex submodule. -/
def oddSubmodule (γ : GradedHilbertModule β E) : Submodule ℂ E where
  carrier := {x | γ.grading x = -x}
  zero_mem' := by simp
  add_mem' hx hy := by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [map_add, hx, hy, neg_add]
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [map_smul, hx, smul_neg]

@[simp] theorem mem_evenSubmodule (γ : GradedHilbertModule β E) (x : E) :
    x ∈ γ.evenSubmodule ↔ γ.grading x = x := Iff.rfl

@[simp] theorem mem_oddSubmodule (γ : GradedHilbertModule β E) (x : E) :
    x ∈ γ.oddSubmodule ↔ γ.grading x = -x := Iff.rfl

/-- The two degrees have zero intersection. -/
theorem even_odd_intersection (γ : GradedHilbertModule β E) {x : E}
    (hx₀ : x ∈ γ.evenSubmodule) (hx₁ : x ∈ γ.oddSubmodule) : x = 0 := by
  have h : x = -x := hx₀.symm.trans hx₁
  have hh : (2 : ℂ) • x = 0 := by
    simpa only [two_smul] using (eq_neg_iff_add_eq_zero.mp h)
  exact (smul_eq_zero.mp hh).resolve_left (by norm_num)

/-- Both homogeneous spaces are closed in the module norm. -/
theorem isClosed_evenSubmodule (γ : GradedHilbertModule β E) :
    IsClosed (γ.evenSubmodule : Set E) :=
  isClosed_eq γ.grading.continuous continuous_id

theorem isClosed_oddSubmodule (γ : GradedHilbertModule β E) :
    IsClosed (γ.oddSubmodule : Set E) :=
  isClosed_eq γ.grading.continuous continuous_neg

/-- Compatibility with the right coefficient action follows from the inner product. -/
@[simp] theorem map_op_smul (γ : GradedHilbertModule β E) (a : Bᵐᵒᵖ) (x : E) :
    γ.grading (a • x) = opStarAlgEquiv β.automorphism a • γ.grading x := by
  apply module_inner_ext_left (B := B)
  intro z
  obtain ⟨y, rfl⟩ := γ.grading.surjective z
  rw [γ.inner_grading, CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_left,
    γ.inner_grading, map_mul, map_star]

/-- Moving a grading through an inner product twists its coefficient. -/
theorem inner_grading_left (γ : GradedHilbertModule β E) (x y : E) :
    ⟪γ.grading x, y⟫_(Bᵐᵒᵖ) =
      opStarAlgEquiv β.automorphism ⟪x, γ.grading y⟫_(Bᵐᵒᵖ) := by
  simpa only [grading_sq] using γ.inner_grading x (γ.grading y)

/-- The trivial module grading over trivially graded coefficients. -/
def trivial : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E where
  grading := LinearIsometryEquiv.refl ℂ E
  involutive _ := rfl
  inner_grading x y := by simp

/-- For trivially graded B, the grading is adjointable and selfadjoint. -/
def toAdjointable (γ : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E) :
    AdjointableMap B E E where
  toCLM := γ.grading.toContinuousLinearEquiv.toContinuousLinearMap
  adjointCLM := γ.grading.toContinuousLinearEquiv.toContinuousLinearMap
  adjoint_identity x y := by
    simpa using γ.inner_grading_left x y

@[simp] theorem toAdjointable_apply
    (γ : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E) (x : E) :
    γ.toAdjointable x = γ.grading x := rfl

@[simp] theorem toAdjointable_adjoint
    (γ : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E) :
    γ.toAdjointable.adjoint = γ.toAdjointable := rfl

/-- The selfadjoint grading operator is unitary. -/
@[simp] theorem toAdjointable_sq
    (γ : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E) :
    γ.toAdjointable.comp γ.toAdjointable = AdjointableMap.id := by
  ext x
  exact γ.grading_sq x

/-- Build a module grading from a selfadjoint involution on an ungraded coefficient algebra. -/
def ofSelfadjointInvolution (T : AdjointableMap B E E)
    (hself : T.adjoint = T) (hsq : T.comp T = AdjointableMap.id) :
    GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E := by
  have hinv : Function.Involutive T := by
    intro x
    exact congrArg (fun S : AdjointableMap B E E => S x) hsq
  have hinner : ∀ x y, ⟪T x, T y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) := by
    intro x y
    rw [T.adjoint_identity]
    change ⟪x, T.adjoint (T y)⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ)
    rw [hself, hinv]
  have hnorm : ∀ x, ‖T x‖ = ‖x‖ := by
    intro x
    have hs : ‖T x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [CStarModule.norm_sq_eq (Bᵐᵒᵖ), hinner, ← CStarModule.norm_sq_eq (Bᵐᵒᵖ)]
    nlinarith [norm_nonneg (T x), norm_nonneg x]
  exact
    { grading :=
        { toLinearEquiv :=
            { toLinearMap := T.toCLM.toLinearMap
              invFun := T
              left_inv := hinv
              right_inv := hinv }
          norm_map' := hnorm }
      involutive := hinv
      inner_grading := fun x y => by
        change ⟪T x, T y⟫_(Bᵐᵒᵖ) =
          opStarAlgEquiv (CStarGrading.trivial : CStarGrading B).automorphism ⟪x, y⟫_(Bᵐᵒᵖ)
        rw [CStarGrading.op_trivial_apply]
        exact hinner x y }

@[simp] theorem ofSelfadjointInvolution_apply (T : AdjointableMap B E E)
    (hself : T.adjoint = T) (hsq : T.comp T = AdjointableMap.id) (x : E) :
    (ofSelfadjointInvolution T hself hsq).grading x = T x := rfl

@[simp] theorem ofSelfadjointInvolution_toAdjointable (T : AdjointableMap B E E)
    (hself : T.adjoint = T) (hsq : T.comp T = AdjointableMap.id) :
    (ofSelfadjointInvolution T hself hsq).toAdjointable = T := by
  ext x
  rfl

/-- An even adjointable map commutes with the source and target gradings. -/
def IsEven (γE : GradedHilbertModule β E) (γF : GradedHilbertModule β F)
    (T : AdjointableMap B E F) : Prop :=
  ∀ x, γF.grading (T x) = T (γE.grading x)

/-- An odd adjointable map anticommutes with the source and target gradings. -/
def IsOdd (γE : GradedHilbertModule β E) (γF : GradedHilbertModule β F)
    (T : AdjointableMap B E F) : Prop :=
  ∀ x, γF.grading (T x) = -T (γE.grading x)

variable {γE : GradedHilbertModule β E} {γF : GradedHilbertModule β F}
  {γH : GradedHilbertModule β H}

@[simp] theorem isEven_id (γ : GradedHilbertModule β E) :
    IsEven γ γ AdjointableMap.id := fun _ => rfl

@[simp] theorem isEven_zero : IsEven γE γF AdjointableMap.zero := by
  intro x
  simp

@[simp] theorem isOdd_zero : IsOdd γE γF AdjointableMap.zero := by
  intro x
  simp

theorem IsEven.add {S T : AdjointableMap B E F} (hS : IsEven γE γF S)
    (hT : IsEven γE γF T) : IsEven γE γF (S.add T) := by
  intro x
  change γF.grading (S x + T x) = S (γE.grading x) + T (γE.grading x)
  rw [map_add, hS x, hT x]

theorem IsOdd.add {S T : AdjointableMap B E F} (hS : IsOdd γE γF S)
    (hT : IsOdd γE γF T) : IsOdd γE γF (S.add T) := by
  intro x
  change γF.grading (S x + T x) = -(S (γE.grading x) + T (γE.grading x))
  rw [map_add, hS x, hT x, neg_add]

theorem IsEven.smul {T : AdjointableMap B E F} (hT : IsEven γE γF T) (c : ℂ) :
    IsEven γE γF (T.smul c) := by
  intro x
  change γF.grading (c • T x) = c • T (γE.grading x)
  rw [map_smul, hT x]

theorem IsOdd.smul {T : AdjointableMap B E F} (hT : IsOdd γE γF T) (c : ℂ) :
    IsOdd γE γF (T.smul c) := by
  intro x
  change γF.grading (c • T x) = -(c • T (γE.grading x))
  rw [map_smul, hT x, smul_neg]

theorem IsEven.comp {S : AdjointableMap B F H} {T : AdjointableMap B E F}
    (hS : IsEven γF γH S) (hT : IsEven γE γF T) : IsEven γE γH (S.comp T) := by
  intro x
  change γH.grading (S (T x)) = S (T (γE.grading x))
  rw [hS (T x), hT x]

theorem IsEven.comp_odd {S : AdjointableMap B F H} {T : AdjointableMap B E F}
    (hS : IsEven γF γH S) (hT : IsOdd γE γF T) : IsOdd γE γH (S.comp T) := by
  intro x
  change γH.grading (S (T x)) = -S (T (γE.grading x))
  rw [hS (T x), hT x]
  exact S.toCLM.map_neg _

theorem IsOdd.comp_even {S : AdjointableMap B F H} {T : AdjointableMap B E F}
    (hS : IsOdd γF γH S) (hT : IsEven γE γF T) : IsOdd γE γH (S.comp T) := by
  intro x
  change γH.grading (S (T x)) = -S (T (γE.grading x))
  rw [hS (T x), hT x]

theorem IsOdd.comp_odd {S : AdjointableMap B F H} {T : AdjointableMap B E F}
    (hS : IsOdd γF γH S) (hT : IsOdd γE γF T) : IsEven γE γH (S.comp T) := by
  intro x
  change γH.grading (S (T x)) = S (T (γE.grading x))
  rw [hS (T x), hT x, S.toCLM.map_neg, neg_neg]

/-- Adjoint preserves even degree, also for nontrivially graded coefficients. -/
theorem IsEven.adjoint {T : AdjointableMap B E F} (hT : IsEven γE γF T) :
    IsEven γF γE T.adjoint := by
  intro y
  apply module_inner_ext_right (B := B)
  intro x
  calc
    ⟪x, γE.grading (T.adjoint y)⟫_(Bᵐᵒᵖ) =
        opStarAlgEquiv β.automorphism ⟪γE.grading x, T.adjoint y⟫_(Bᵐᵒᵖ) := by
      simpa only [grading_sq] using γE.inner_grading (γE.grading x) (T.adjoint y)
    _ = opStarAlgEquiv β.automorphism ⟪T (γE.grading x), y⟫_(Bᵐᵒᵖ) := by
      rw [T.adjoint_identity]
      rfl
    _ = opStarAlgEquiv β.automorphism ⟪γF.grading (T x), y⟫_(Bᵐᵒᵖ) := by rw [hT]
    _ = ⟪T x, γF.grading y⟫_(Bᵐᵒᵖ) := by
      rw [γF.inner_grading_left, CStarGrading.op_automorphism_sq]
    _ = ⟪x, T.adjoint (γF.grading y)⟫_(Bᵐᵒᵖ) := T.adjoint_identity x (γF.grading y)

/-- Adjoint preserves odd degree, also for nontrivially graded coefficients. -/
theorem IsOdd.adjoint {T : AdjointableMap B E F} (hT : IsOdd γE γF T) :
    IsOdd γF γE T.adjoint := by
  intro y
  apply module_inner_ext_right (B := B)
  intro x
  have hTx : T (γE.grading x) = -γF.grading (T x) := by
    rw [hT, neg_neg]
  calc
    ⟪x, γE.grading (T.adjoint y)⟫_(Bᵐᵒᵖ) =
        opStarAlgEquiv β.automorphism ⟪γE.grading x, T.adjoint y⟫_(Bᵐᵒᵖ) := by
      simpa only [grading_sq] using γE.inner_grading (γE.grading x) (T.adjoint y)
    _ = opStarAlgEquiv β.automorphism ⟪T (γE.grading x), y⟫_(Bᵐᵒᵖ) := by
      rw [T.adjoint_identity]
      rfl
    _ = -opStarAlgEquiv β.automorphism ⟪γF.grading (T x), y⟫_(Bᵐᵒᵖ) := by
      rw [hTx, CStarModule.inner_neg_left, map_neg]
    _ = -⟪T x, γF.grading y⟫_(Bᵐᵒᵖ) := by
      rw [γF.inner_grading_left, CStarGrading.op_automorphism_sq]
    _ = ⟪x, -T.adjoint (γF.grading y)⟫_(Bᵐᵒᵖ) := by
      rw [CStarModule.inner_neg_right, T.adjoint_identity]
      rfl

end GradedHilbertModule
end BC4lean.KKTheory
