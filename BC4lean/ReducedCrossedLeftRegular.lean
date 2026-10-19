import BC4lean.KasparovDescentModule
import BC4lean.GradedEquivariantInteriorModuleTensor
import Mathlib.Analysis.Normed.Operator.Mul

/-! # Left regular multipliers on the actual crossed coefficient module

The regular unitary need not belong to the nonunital
crossed algebra.  Its left product nevertheless preserves the actual closed
algebra, by the explicit formula on generators and closed linear-span density.
This gives genuine unitary operators on the standard crossed coefficient
module, with the original coefficient covariance.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent

open scoped InnerProductSpace KasparovDescent

/-- A continuous complex-linear map carries the actual closure of a span into
a closed target submodule once this is proved on the generators. The entire
proof is checked with abstract normed spaces and contains no regular-module
or operator-algebra instances. -/
private theorem closedSubmodule_maps_closure_span
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (K : Submodule ℂ W) (hK : IsClosed (K : Set W))
    (L : V →L[ℂ] W) (s : Set V) (hgen : ∀ v ∈ s, L v ∈ K)
    {v : V} (hv : v ∈ closure (Submodule.span ℂ s : Set V)) : L v ∈ K := by
  have hspan : Submodule.span ℂ s ≤ K.comap L.toLinearMap :=
    Submodule.span_le.mpr hgen
  exact closure_minimal hspan (hK.preimage L.continuous) hv

/-- Invariance of a closed submodule follows from its actual closure-of-span
description and the action of the continuous map on those generators. -/
private theorem closedSubmodule_maps_of_eq_closure_span
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (K : Submodule ℂ V) (hK : IsClosed (K : Set V))
    (L : V →L[ℂ] V) (s : Set V)
    (hspan : (K : Set V) = closure (Submodule.span ℂ s : Set V))
    (hgen : ∀ v ∈ s, L v ∈ K) {v : V} (hv : v ∈ K) : L v ∈ K := by
  apply closedSubmodule_maps_closure_span K hK L s hgen
  rw [← hspan]
  exact hv

variable {Γ B : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]

theorem regular_mem_unitary (g : Γ) :
    reducedCrossedRegular (B := B) g ∈ unitary
      (AdjointableMap B (ReducedCrossedHilbertModule B Γ)
        (ReducedCrossedHilbertModule B Γ)) := by
  constructor
  · rw [reducedCrossedRegular_star, ← reducedCrossedRegular_mul,
      inv_mul_cancel, reducedCrossedRegular_one]
  · rw [reducedCrossedRegular_star, ← reducedCrossedRegular_mul,
      mul_inv_cancel, reducedCrossedRegular_one]

/-- The ambient regular unitaries are genuine left multipliers on generators. -/
theorem regular_mul_generator (β : CStarAlgebraAction Γ B)
    (g h : Γ) (b : B) :
    reducedCrossedRegular g * reducedCrossedGenerator β b h =
      reducedCrossedGenerator β (β.automorphism g b) (g * h) := by
  unfold reducedCrossedGenerator
  rw [← mul_assoc, ← reducedCrossed_covariance β g b,
    mul_assoc, ← reducedCrossedRegular_mul]

private def ambientLeftRegularLinear (g : Γ) :
    AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ)
      →ₗ[ℂ]
        AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ) where
  toFun T := reducedCrossedRegular g * T
  map_add' := mul_add _
  map_smul' c T := mul_smul_comm c _ T

/-- The actual continuous left multiplication map in the ambient operator algebra. -/
private def ambientLeftRegularCLM (g : Γ) :
    AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ)
      →L[ℂ]
        AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ) :=
  ContinuousLinearMap.mul ℂ
    (AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ))
    (reducedCrossedRegular (B := B) g)

/-- Left multiplication preserves the actual reduced algebra, including
nonunital coefficients. The abstract closed-span lemma is instantiated with
the proved generator formula and the foundation's genuine span-closure equality. -/
theorem regular_mul_mem (β : CStarAlgebraAction Γ B) (g : Γ)
    {T : AdjointableMap B (ReducedCrossedHilbertModule B Γ)
      (ReducedCrossedHilbertModule B Γ)}
    (hT : T ∈ reducedCrossedAlgebra β) :
    reducedCrossedRegular g * T ∈ reducedCrossedAlgebra β := by
  apply closedSubmodule_maps_of_eq_closure_span
    (reducedCrossedAlgebra β).toSubmodule (reducedCrossedAlgebra_isClosed β)
    (ambientLeftRegularCLM (B := B) g)
    (Set.range (fun p : B × Γ => reducedCrossedGenerator β p.1 p.2))
    (reducedCrossedAlgebra_coe_eq_closure_span β) ?_ hT
  rintro _ ⟨⟨b, h⟩, rfl⟩
  change reducedCrossedRegular g * reducedCrossedGenerator β b h ∈
    reducedCrossedAlgebra β
  rw [regular_mul_generator]
  exact reducedCrossedGenerator_mem β _ _

/-- The left regular multiplier restricted to the actual closed algebra. -/
def leftRegular (β : CStarAlgebraAction Γ B) (g : Γ)
    (c : ReducedCrossedProduct β) : ReducedCrossedProduct β :=
  ⟨reducedCrossedRegular (B := B) g * (c : AdjointableMap B
    (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ)),
    regular_mul_mem β g c.property⟩

@[simp] theorem leftRegular_coe (β : CStarAlgebraAction Γ B) (g : Γ)
    (c : ReducedCrossedProduct β) :
    (leftRegular β g c : AdjointableMap B (ReducedCrossedHilbertModule B Γ)
      (ReducedCrossedHilbertModule B Γ)) = reducedCrossedRegular (B := B) g * (c : AdjointableMap B
        (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ)) := rfl

/-- The actual left multiplier on the standard module is a complex linear
isometry equivalence.  Its inverse is the multiplier for the inverse group element. -/
def leftRegularIsometry (β : CStarAlgebraAction Γ B) (g : Γ) :
    (ReducedCrossedProduct β)ᵐᵒᵖ ≃ₗᵢ[ℂ] (ReducedCrossedProduct β)ᵐᵒᵖ where
  toLinearEquiv :=
    { toFun c := MulOpposite.op (leftRegular β g (MulOpposite.unop c))
      invFun c := MulOpposite.op (leftRegular β g⁻¹ (MulOpposite.unop c))
      left_inv c := by
        apply MulOpposite.unop_injective
        apply Subtype.ext
        change reducedCrossedRegular g⁻¹ *
          (reducedCrossedRegular g * ((MulOpposite.unop c : ReducedCrossedProduct β) :
            AdjointableMap B (ReducedCrossedHilbertModule B Γ)
              (ReducedCrossedHilbertModule B Γ))) = _
        rw [← mul_assoc, ← reducedCrossedRegular_mul,
          inv_mul_cancel, reducedCrossedRegular_one, one_mul]
      right_inv c := by
        apply MulOpposite.unop_injective
        apply Subtype.ext
        change reducedCrossedRegular g *
          (reducedCrossedRegular g⁻¹ * ((MulOpposite.unop c : ReducedCrossedProduct β) :
            AdjointableMap B (ReducedCrossedHilbertModule B Γ)
              (ReducedCrossedHilbertModule B Γ))) = _
        rw [← mul_assoc, ← reducedCrossedRegular_mul,
          mul_inv_cancel, reducedCrossedRegular_one, one_mul]
      map_add' c d := by
        apply MulOpposite.unop_injective
        apply Subtype.ext
        exact mul_add _ _ _
      map_smul' z c := by
        apply MulOpposite.unop_injective
        apply Subtype.ext
        exact mul_smul_comm z _ _ }
  norm_map' c := by
    change ‖reducedCrossedRegular g * ((MulOpposite.unop c : ReducedCrossedProduct β) :
      AdjointableMap B (ReducedCrossedHilbertModule B Γ)
        (ReducedCrossedHilbertModule B Γ))‖ = ‖((MulOpposite.unop c : ReducedCrossedProduct β) :
      AdjointableMap B (ReducedCrossedHilbertModule B Γ)
        (ReducedCrossedHilbertModule B Γ))‖
    exact CStarRing.norm_mem_unitary_mul _ (regular_mem_unitary g)

@[simp] theorem leftRegularIsometry_apply (β : CStarAlgebraAction Γ B) (g : Γ)
    (c : (ReducedCrossedProduct β)ᵐᵒᵖ) :
    leftRegularIsometry β g c = MulOpposite.op (leftRegular β g (MulOpposite.unop c)) := rfl

/-- The standard crossed module has the genuine left regular action over
the trivial action on its right coefficient algebra. -/
def leftRegularAction (β : CStarAlgebraAction Γ B) :
    EquivariantHilbertModule
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ (ReducedCrossedProduct β))
      (ReducedCrossedProduct β)ᵐᵒᵖ where
  action :=
    { toFun := leftRegularIsometry β
      map_one' := by
        apply LinearIsometryEquiv.ext
        intro c
        apply MulOpposite.unop_injective
        apply Subtype.ext
        change reducedCrossedRegular (B := B) (1 : Γ) * _ = _
        rw [reducedCrossedRegular_one, one_mul]
        rfl
      map_mul' g h := by
        apply LinearIsometryEquiv.ext
        intro c
        apply MulOpposite.unop_injective
        apply Subtype.ext
        change reducedCrossedRegular (g * h) * ((MulOpposite.unop c : ReducedCrossedProduct β) :
          AdjointableMap B (ReducedCrossedHilbertModule B Γ)
            (ReducedCrossedHilbertModule B Γ)) =
          reducedCrossedRegular g * (reducedCrossedRegular h * _)
        rw [reducedCrossedRegular_mul, mul_assoc] }
  inner_action g c d := by
    change MulOpposite.op
      (star (leftRegular β g (MulOpposite.unop c)) *
        leftRegular β g (MulOpposite.unop d)) =
      MulOpposite.op (star (MulOpposite.unop c) * MulOpposite.unop d)
    apply congrArg MulOpposite.op
    apply Subtype.ext
    change star (reducedCrossedRegular g * ((MulOpposite.unop c : ReducedCrossedProduct β) :
        AdjointableMap B (ReducedCrossedHilbertModule B Γ)
          (ReducedCrossedHilbertModule B Γ))) *
      (reducedCrossedRegular g * ((MulOpposite.unop d : ReducedCrossedProduct β) :
        AdjointableMap B (ReducedCrossedHilbertModule B Γ)
          (ReducedCrossedHilbertModule B Γ))) = _
    calc
      _ = star ((MulOpposite.unop c : ReducedCrossedProduct β) :
          AdjointableMap B (ReducedCrossedHilbertModule B Γ)
            (ReducedCrossedHilbertModule B Γ)) *
          ((star (reducedCrossedRegular g) * reducedCrossedRegular g) *
            ((MulOpposite.unop d : ReducedCrossedProduct β) :
              AdjointableMap B (ReducedCrossedHilbertModule B Γ)
                (ReducedCrossedHilbertModule B Γ))) := by
        simp only [star_mul, mul_assoc]
      _ = _ := by
        rw [(regular_mem_unitary (B := B) g).1, one_mul]
        rfl

@[simp] theorem leftRegularAction_apply (β : CStarAlgebraAction Γ B) (g : Γ)
    (c : (ReducedCrossedProduct β)ᵐᵒᵖ) :
    (leftRegularAction β).action g c =
      MulOpposite.op (leftRegular β g (MulOpposite.unop c)) := rfl

/-- The actual coefficient inclusion intertwines the original coefficient
action with the concrete left regular action.  This is exactly the factor
condition used by the proved balanced interior-tensor isometry construction. -/
theorem coefficientRepresentation_equivariant (β : CStarAlgebraAction Γ B) :
    ModuleTensorRepresentationEquivariant (coefficientRepresentation β) β
      (leftRegularAction β) := by
  intro g b c
  apply MulOpposite.unop_injective
  apply Subtype.ext
  change reducedCrossedRegular g *
      (reducedCrossedCoefficient β b * ((MulOpposite.unop c : ReducedCrossedProduct β) :
        AdjointableMap B (ReducedCrossedHilbertModule B Γ)
          (ReducedCrossedHilbertModule B Γ))) =
    reducedCrossedCoefficient β (β.automorphism g b) *
      (reducedCrossedRegular g * _)
  rw [← mul_assoc, ← reducedCrossed_covariance β g b, mul_assoc]

end BC4lean.KKTheory.KasparovDescent
