import BC4lean.HilbertModuleEquiv

/-! # A genuine operator unitary as a whole Hilbert-module unitary

Both actual unitary equations give the inverse maps. The genuine coefficient
adjoint identity preserves the whole coefficient-valued inner product, hence
also the actual Hilbert-module norm.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

namespace HilbertModuleEquiv

/-- Both unitary equations supply a genuine coefficient-form unitary on whole vectors. -/
def ofAdjointableUnitary (U : unitary (AdjointableMap B E E)) : HilbertModuleEquiv B E E where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun := fun x => (U : AdjointableMap B E E) x
          invFun := fun x => (star (U : AdjointableMap B E E)) x
          left_inv x := by
            change (star (U : AdjointableMap B E E) * U) x = x
            rw [U.property.1, AdjointableMap.one_apply]
          right_inv x := by
            change ((U : AdjointableMap B E E) * star (U : AdjointableMap B E E)) x = x
            rw [U.property.2, AdjointableMap.one_apply]
          map_add' := (U : AdjointableMap B E E).toCLM.map_add
          map_smul' := (U : AdjointableMap B E E).toCLM.map_smul }
      norm_map' x := by
        change ‖(U : AdjointableMap B E E) x‖ = ‖x‖
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ)]
        rw [(U : AdjointableMap B E E).adjoint_identity]
        change Real.sqrt ‖⟪x, (star (U : AdjointableMap B E E) * U) x⟫_(Bᵐᵒᵖ)‖ = ‖x‖
        rw [U.property.1, AdjointableMap.one_apply]
        exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm }
  inner_map x y := by
    change ⟪(U : AdjointableMap B E E) x, (U : AdjointableMap B E E) y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ)
    rw [(U : AdjointableMap B E E).adjoint_identity]
    change ⟪x, (star (U : AdjointableMap B E E) * U) y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ)
    rw [U.property.1, AdjointableMap.one_apply]

@[simp] theorem ofAdjointableUnitary_apply (U : unitary (AdjointableMap B E E)) (x : E) :
    ofAdjointableUnitary U x = (U : AdjointableMap B E E) x := rfl

@[simp] theorem ofAdjointableUnitary_symm_apply (U : unitary (AdjointableMap B E E)) (x : E) :
    (ofAdjointableUnitary U).symm x = (star (U : AdjointableMap B E E)) x := rfl

end HilbertModuleEquiv
end BC4lean.KKTheory
