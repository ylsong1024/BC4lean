import BC4lean.EquivariantHilbertModule
import BC4lean.AdjointableComplete

/-! # The genuine action on the module endomorphism algebra

Conjugation by the actual semilinear module action defines a star
automorphism. Its inverse is conjugation by the inverse group element.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ B E : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  {α : CStarAlgebraAction Γ B}

/-- The actual conjugation maps, bundled as genuine star automorphisms. -/
def EquivariantHilbertModule.conjugateOperatorStarAlgEquiv
    (U : EquivariantHilbertModule α E) (g : Γ) : AdjointableMap B E E ≃⋆ₐ[ℂ] AdjointableMap B E E where
  toFun := U.conjugateOperator g
  invFun := U.conjugateOperator g⁻¹
  left_inv := fun T => by
    change U.conjugateMap U g⁻¹ (U.conjugateMap U g T) = T
    rw [← U.conjugateMap_mul U g⁻¹ g T, inv_mul_cancel, U.conjugateMap_one]
  right_inv := fun T => by
    change U.conjugateMap U g (U.conjugateMap U g⁻¹ T) = T
    rw [← U.conjugateMap_mul U g g⁻¹ T, mul_inv_cancel, U.conjugateMap_one]
  map_mul' := U.conjugateMap_comp U U g
  map_add' := U.conjugateMap_add U g
  map_star' := fun T => (U.conjugateMap_adjoint U g T).symm
  map_smul' := fun c T => U.conjugateMap_smul U g T c

end BC4lean.KKTheory
