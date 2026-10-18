import BC4lean.ReducedCrossedNorm
import BC4lean.ModuleTensorCompact
import BC4lean.InteriorModuleTensorCountableGeneration

/-! # The actual coefficient module and operator for reduced descent

For the concrete reduced crossed product `C = B ⋊ᵣ Γ`, this constructs the
completed interior module `E ⊗_B C` using the genuine coefficient inclusion.
Every adjointable `T` acts by the actual `T ⊗ 1`, with its adjoint, norm bound,
and preservation of compact module operators proved by the existing completed
tensor construction. The crossed coefficient order is its canonical spectral
order, available through the `KasparovDescent` scope.

An integrated source crossed-product representation, full homotopy descent,
and compatibility with Kasparov products remain separate constructions. No
Kasparov descent map is defined by this module.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped InnerProductSpace

variable {Γ B : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]

/-- The actual crossed coefficient algebra has its canonical C⋆ order. -/
scoped instance crossedPartialOrder (β : CStarAlgebraAction Γ B) :
    PartialOrder (ReducedCrossedProduct β) := CStarAlgebra.spectralOrder _

open scoped KasparovDescent

scoped instance crossedStarOrderedRing (β : CStarAlgebraAction Γ B) :
    StarOrderedRing (ReducedCrossedProduct β) := CStarAlgebra.spectralOrderedRing _

open scoped KasparovDescent

/-- The original coefficients act on the standard crossed-product module
through the actual isometric coefficient inclusion. -/
def coefficientRepresentation (β : CStarAlgebraAction Γ B) :
    B →⋆ₙₐ[ℂ] AdjointableMap (ReducedCrossedProduct β)
      (ReducedCrossedProduct β)ᵐᵒᵖ (ReducedCrossedProduct β)ᵐᵒᵖ :=
  standardLeftMul.comp (coefficientToReducedCrossed β)

@[simp] theorem coefficientRepresentation_apply (β : CStarAlgebraAction Γ B)
    (b : B) (c : (ReducedCrossedProduct β)ᵐᵒᵖ) :
    coefficientRepresentation β b c =
      MulOpposite.op (coefficientToReducedCrossed β b * MulOpposite.unop c) := rfl

/-- Every original coefficient acts compactly on the standard crossed module. -/
theorem coefficientRepresentation_compact (β : CStarAlgebraAction Γ B) (b : B) :
    IsModuleCompact (coefficientRepresentation β b) :=
  standardLeftMul_mem_moduleCompact (coefficientToReducedCrossed β b)

variable (β : CStarAlgebraAction Γ B) (E : Type*)
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- The actual completed coefficient extension over the actual reduced crossed product. -/
abbrev Module := InteriorModuleTensor (E := E) (coefficientRepresentation β)

/-- Countable groups and separable coefficients give the actual module the
countable generation required by Kasparov cycles. -/
theorem countablyGenerated [Countable Γ] [TopologicalSpace.SeparableSpace B]
    (hE : IsCountablyGeneratedModule B E) :
    IsCountablyGeneratedModule (ReducedCrossedProduct β) (Module β E) :=
  hE.interiorTensor standard_module_isCountablyGenerated (coefficientRepresentation β)

/-- Elementary vectors in the genuine completed module. -/
def mk (x : E) (c : (ReducedCrossedProduct β)ᵐᵒᵖ) : Module β E :=
  interiorModuleTensorMk (coefficientRepresentation β) x c

theorem mk_balance (b : B) (x : E) (c : (ReducedCrossedProduct β)ᵐᵒᵖ) :
    mk β E (MulOpposite.op b • x) c =
      mk β E x (MulOpposite.op (coefficientToReducedCrossed β b * MulOpposite.unop c)) :=
  interiorModuleTensorMk_balance (coefficientRepresentation β) b x c

/-- Elementary vectors have the actual crossed coefficient inner product. -/
theorem mk_inner (x y : E) (c d : (ReducedCrossedProduct β)ᵐᵒᵖ) :
    ⟪mk β E x c, mk β E y d⟫_((ReducedCrossedProduct β)ᵐᵒᵖ) =
      MulOpposite.op (star (MulOpposite.unop c) *
        (coefficientToReducedCrossed β (MulOpposite.unop ⟪x, y⟫_(Bᵐᵒᵖ)) *
          MulOpposite.unop d)) := by
  rw [mk, mk, interiorModuleTensorInner_mk_mk]
  rfl

/-- The operator part of descent is an actual unital star homomorphism. -/
def operatorHom : AdjointableMap B E E →⋆ₐ[ℂ]
    AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) :=
  interiorModuleTensorOperatorHom (coefficientRepresentation β)

@[simp] theorem operatorHom_mk (T : AdjointableMap B E E) (x : E)
    (c : (ReducedCrossedProduct β)ᵐᵒᵖ) :
    operatorHom β E T (mk β E x c) = mk β E (T x) c :=
  interiorModuleTensorOperator_mk (coefficientRepresentation β) T x c

theorem norm_operatorHom_le (T : AdjointableMap B E E) :
    ‖operatorHom β E T‖ ≤ ‖T‖ :=
  interiorModuleTensorOperator_norm_le (coefficientRepresentation β) T

@[simp] theorem operatorHom_adjoint (T : AdjointableMap B E E) :
    (operatorHom β E T).adjoint = operatorHom β E T.adjoint :=
  interiorModuleTensorOperator_adjoint (coefficientRepresentation β) T

theorem operatorHom_mul (S T : AdjointableMap B E E) :
    operatorHom β E (S * T) = operatorHom β E S * operatorHom β E T :=
  map_mul (operatorHom β E) S T

/-- Genuine compact module operators remain compact after this coefficient extension. -/
theorem operatorHom_compact {T : AdjointableMap B E E} (hT : IsModuleCompact T) :
    IsModuleCompact (operatorHom β E T) :=
  hT.interiorModuleTensorOperator (coefficientRepresentation β)
    (coefficientRepresentation_compact β)

end BC4lean.KKTheory.KasparovDescent
