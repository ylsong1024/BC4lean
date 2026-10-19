import BC4lean.AlgebraicCrossedProductMap
import BC4lean.IndexedStandardReducedCrossedEquiv
import BC4lean.ReducedSourceRegularBound
import BC4lean.ReducedCrossedRepresentationExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The actual reduced crossed-product map of an equivariant star homomorphism

The coefficientwise finite map has a genuine reduced-norm estimate. To prove
it, the standard representation of the target coefficient algebra is composed
with the original homomorphism. Its finite regular action is exactly the
target regular crossed-product action under the actual finite-vector
identification. The previously proved regular norm bound therefore applies
even when the coefficient homomorphism is degenerate or noninjective.

Dense extension then constructs the actual completed star homomorphism.
Generator formulas, preservation of coefficients, identity, and composition
are proved on the concrete dense regular algebra.


-/

noncomputable section
namespace BC4lean.KKTheory

open scoped CStarAlgebra Topology

variable {Γ A B : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] in
/-- On every finite vector, the actual mapped target generator is precisely
the source regular generator for the represented coefficient map. -/
theorem algebraicCrossedMap_generator_mk
    (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B)
    (φ : A →⋆ₙₐ[ℂ] B)
    (hφ : ∀ g a, φ (α.automorphism g a) = β.automorphism g (φ a))
    (a : A) (g : Γ) (ξ : Γ →₀ Bᵐᵒᵖ) :
    reducedCrossedGenerator β (φ a) g (reducedCrossedMk ξ) =
      reducedCrossedMk
        (ReducedSourceRegular.finiteGenerator α (standardLeftMul.comp φ) a g ξ) := by
  let L : (Γ →₀ Bᵐᵒᵖ) →ₗ[ℂ] ReducedCrossedHilbertModule B Γ :=
    (reducedCrossedGenerator β (φ a) g).toCLM.toLinearMap.comp reducedCrossedMk
  let R : (Γ →₀ Bᵐᵒᵖ) →ₗ[ℂ] ReducedCrossedHilbertModule B Γ :=
    reducedCrossedMk.comp
      (ReducedSourceRegular.finiteGenerator α (standardLeftMul.comp φ) a g)
  change L ξ = R ξ
  induction ξ using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add ξ η hξ hη => rw [map_add, map_add, hξ, hη]
  | single t c =>
    change reducedCrossedGenerator β (φ a) g (reducedCrossedInclusion t c) =
      reducedCrossedMk (ReducedSourceRegular.finiteGenerator α
        (standardLeftMul.comp φ) a g (Finsupp.single t c))
    rw [ReducedSourceRegular.regularGenerator_inclusion,
      ReducedSourceRegular.finiteGenerator_single, ← reducedCrossedInclusion_apply]
    change reducedCrossedInclusion (g * t)
        (MulOpposite.op (β.automorphism (g * t)⁻¹ (φ a) * MulOpposite.unop c)) =
      reducedCrossedInclusion (g * t)
        (MulOpposite.op (φ (α.automorphism (g * t)⁻¹ a) * MulOpposite.unop c))
    rw [hφ]

/-- Exact finite regular-action identity for the coefficientwise map. -/
theorem algebraicCrossedMap_operator_mk
    (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B)
    (φ : A →⋆ₙₐ[ℂ] B)
    (hφ : ∀ g a, φ (α.automorphism g a) = β.automorphism g (φ a))
    (f : AlgebraicCrossedProduct α) (ξ : Γ →₀ Bᵐᵒᵖ) :
    algebraicCrossedOperatorHom β (AlgebraicCrossedProduct.map α β φ hφ f)
        (reducedCrossedMk ξ) =
      reducedCrossedMk
        (ReducedSourceRegular.finiteAction α (standardLeftMul.comp φ) f ξ) := by
  induction f using AlgebraicCrossedProduct.induction_on α with
  | zero =>
    simp only [map_zero, AdjointableMap.coe_zero_apply,
      ReducedSourceRegular.finiteAction_zero, LinearMap.zero_apply]
  | single g a =>
    simpa only [AlgebraicCrossedProduct.map_single, algebraicCrossedOperatorHom_single,
      ReducedSourceRegular.finiteAction_single] using
      algebraicCrossedMap_generator_mk α β φ hφ a g ξ
  | add f h hf hh =>
    simp only [map_add, AdjointableMap.coe_add_apply, hf, hh,
      ReducedSourceRegular.finiteAction_add, LinearMap.add_apply]

/-- The finite coefficientwise map is genuinely reduced-norm contractive.
The only hypothesis on the original coefficient homomorphism is its original
equivariance; no norm bound or factorization conclusion is assumed. -/
theorem algebraicCrossedMap_operator_norm_le
    (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B)
    (φ : A →⋆ₙₐ[ℂ] B)
    (hφ : ∀ g a, φ (α.automorphism g a) = β.automorphism g (φ a))
    (f : AlgebraicCrossedProduct α) :
    ‖algebraicCrossedOperatorHom β (AlgebraicCrossedProduct.map α β φ hφ f)‖ ≤
      ‖algebraicCrossedOperatorHom α f‖ := by
  change ‖(algebraicCrossedOperatorHom β
    (AlgebraicCrossedProduct.map α β φ hφ f)).toCLM‖ ≤
      ‖algebraicCrossedOperatorHom α f‖
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  refine (reducedCrossedMk_denseRange (B := B) (Γ := Γ)).induction_on x
    (isClosed_le
      (continuous_norm.comp (algebraicCrossedOperatorHom β
        (AlgebraicCrossedProduct.map α β φ hφ f)).toCLM.continuous)
      (continuous_const.mul continuous_norm)) ?_
  intro ξ
  change ‖algebraicCrossedOperatorHom β
      (AlgebraicCrossedProduct.map α β φ hφ f) (reducedCrossedMk ξ)‖ ≤
    ‖algebraicCrossedOperatorHom α f‖ * ‖reducedCrossedMk ξ‖
  rw [algebraicCrossedMap_operator_mk α β φ hφ f ξ,
    ← IndexedStandardReducedCrossed.mk_norm,
    ← IndexedStandardReducedCrossed.mk_norm]
  exact ReducedSourceRegular.finiteAction_norm_le α (standardLeftMul.comp φ) f ξ

/-- The same actual reduced bound with codomain in the constructed closed
target algebra, rather than its ambient operator algebra. -/
theorem algebraicCrossedMap_norm_le
    (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B)
    (φ : A →⋆ₙₐ[ℂ] B)
    (hφ : ∀ g a, φ (α.automorphism g a) = β.automorphism g (φ a))
    (f : AlgebraicCrossedProduct α) :
    ‖algebraicToReducedCrossed β (AlgebraicCrossedProduct.map α β φ hφ f)‖ ≤
      algebraicCrossedReducedNorm α f :=
  algebraicCrossedMap_operator_norm_le α β φ hφ f

/-- The actual completed reduced crossed-product star homomorphism of an
arbitrary equivariant nonunital coefficient star homomorphism. -/
def reducedCrossedMap (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B)
    (φ : A →⋆ₙₐ[ℂ] B)
    (hφ : ∀ g a, φ (α.automorphism g a) = β.automorphism g (φ a)) :
    ReducedCrossedProduct α →⋆ₙₐ[ℂ] ReducedCrossedProduct β :=
  extendReducedRepresentation α
    ((algebraicToReducedCrossed β).comp (AlgebraicCrossedProduct.map α β φ hφ))
    (algebraicCrossedMap_norm_le α β φ hφ)

@[simp] theorem reducedCrossedMap_algebraic
    (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B)
    (φ : A →⋆ₙₐ[ℂ] B)
    (hφ : ∀ g a, φ (α.automorphism g a) = β.automorphism g (φ a))
    (f : AlgebraicCrossedProduct α) :
    reducedCrossedMap α β φ hφ (algebraicToReducedCrossed α f) =
      algebraicToReducedCrossed β (AlgebraicCrossedProduct.map α β φ hφ f) :=
  extendReducedRepresentation_algebraic α
    ((algebraicToReducedCrossed β).comp (AlgebraicCrossedProduct.map α β φ hφ))
    (algebraicCrossedMap_norm_le α β φ hφ) f

/-- The completed map preserves every actual coefficient-group generator. -/
@[simp] theorem reducedCrossedMap_generator
    (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B)
    (φ : A →⋆ₙₐ[ℂ] B)
    (hφ : ∀ g a, φ (α.automorphism g a) = β.automorphism g (φ a)) (a : A) (g : Γ) :
    reducedCrossedMap α β φ hφ
        ⟨reducedCrossedGenerator α a g, reducedCrossedGenerator_mem α a g⟩ =
      ⟨reducedCrossedGenerator β (φ a) g, reducedCrossedGenerator_mem β (φ a) g⟩ := by
  have hgen : (⟨reducedCrossedGenerator α a g,
        reducedCrossedGenerator_mem α a g⟩ : ReducedCrossedProduct α) =
      algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a) := by
    apply Subtype.ext
    exact (algebraicToReducedCrossed_single α g a).symm
  rw [hgen, reducedCrossedMap_algebraic, AlgebraicCrossedProduct.map_single]
  apply Subtype.ext
  exact algebraicToReducedCrossed_single β g (φ a)

/-- The original coefficient inclusion is its finite singleton at the
group identity. -/
theorem coefficientToReducedCrossed_eq_algebraic_single_one
    (α : CStarAlgebraAction Γ A) (a : A) :
    coefficientToReducedCrossed α a =
      algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α 1 a) := by
  apply Subtype.ext
  change reducedCrossedCoefficient α a =
    algebraicCrossedOperatorHom α (AlgebraicCrossedProduct.single α 1 a)
  rw [algebraicCrossedOperatorHom_single]
  simp only [reducedCrossedGenerator, reducedCrossedRegular_one, mul_one]

@[simp] theorem reducedCrossedMap_coefficient
    (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B)
    (φ : A →⋆ₙₐ[ℂ] B)
    (hφ : ∀ g a, φ (α.automorphism g a) = β.automorphism g (φ a)) (a : A) :
    reducedCrossedMap α β φ hφ (coefficientToReducedCrossed α a) =
      coefficientToReducedCrossed β (φ a) := by
  rw [coefficientToReducedCrossed_eq_algebraic_single_one,
    reducedCrossedMap_algebraic, AlgebraicCrossedProduct.map_single,
    ← coefficientToReducedCrossed_eq_algebraic_single_one]

theorem reducedCrossedMap_norm_le
    (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B)
    (φ : A →⋆ₙₐ[ℂ] B)
    (hφ : ∀ g a, φ (α.automorphism g a) = β.automorphism g (φ a))
    (c : ReducedCrossedProduct α) :
    ‖reducedCrossedMap α β φ hφ c‖ ≤ ‖c‖ :=
  NonUnitalStarAlgHom.norm_apply_le (reducedCrossedMap α β φ hφ) c

theorem reducedCrossedMap_continuous
    (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B)
    (φ : A →⋆ₙₐ[ℂ] B)
    (hφ : ∀ g a, φ (α.automorphism g a) = β.automorphism g (φ a)) :
    Continuous (reducedCrossedMap α β φ hφ) := map_continuous _

/-- Continuous star homomorphisms on the concrete reduced crossed product
are determined by the original finite regular generators. -/
theorem reducedCrossedHom_ext {R : Type*} [NonUnitalCStarAlgebra R]
    (α : CStarAlgebraAction Γ A)
    (F G : ReducedCrossedProduct α →⋆ₙₐ[ℂ] R)
    (h : ∀ a g,
      F ⟨reducedCrossedGenerator α a g, reducedCrossedGenerator_mem α a g⟩ =
        G ⟨reducedCrossedGenerator α a g, reducedCrossedGenerator_mem α a g⟩) :
    F = G := by
  have halg : ∀ f : AlgebraicCrossedProduct α,
      F (algebraicToReducedCrossed α f) = G (algebraicToReducedCrossed α f) := by
    intro f
    induction f using AlgebraicCrossedProduct.induction_on α with
    | zero => simp
    | single g a =>
      have hgen : algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a) =
          (⟨reducedCrossedGenerator α a g,
            reducedCrossedGenerator_mem α a g⟩ : ReducedCrossedProduct α) := by
        apply Subtype.ext
        exact algebraicToReducedCrossed_single α g a
      rw [hgen]
      exact h a g
    | add f k hf hk => simp only [map_add, hf, hk]
  apply NonUnitalStarAlgHom.ext
  intro c
  exact congrFun ((algebraicToReducedCrossed_denseRange α).equalizer
    (map_continuous F) (map_continuous G) (funext halg)) c

@[simp] theorem reducedCrossedMap_id (α : CStarAlgebraAction Γ A) :
    reducedCrossedMap α α (NonUnitalStarAlgHom.id ℂ A) (fun _ _ => rfl) =
      NonUnitalStarAlgHom.id ℂ (ReducedCrossedProduct α) := by
  apply reducedCrossedHom_ext α
  intro a g
  exact reducedCrossedMap_generator α α (NonUnitalStarAlgHom.id ℂ A)
    (fun _ _ => rfl) a g

theorem reducedCrossedMap_comp {D : Type*}
    [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B)
    (δ : CStarAlgebraAction Γ D) (φ : A →⋆ₙₐ[ℂ] B) (ψ : B →⋆ₙₐ[ℂ] D)
    (hφ : ∀ g a, φ (α.automorphism g a) = β.automorphism g (φ a))
    (hψ : ∀ g b, ψ (β.automorphism g b) = δ.automorphism g (ψ b)) :
    reducedCrossedMap α δ (ψ.comp φ)
        (AlgebraicCrossedProduct.equivariant_comp α β δ φ ψ hφ hψ) =
      (reducedCrossedMap β δ ψ hψ).comp (reducedCrossedMap α β φ hφ) := by
  apply reducedCrossedHom_ext α
  intro a g
  simp only [NonUnitalStarAlgHom.comp_apply, reducedCrossedMap_generator]

end BC4lean.KKTheory
