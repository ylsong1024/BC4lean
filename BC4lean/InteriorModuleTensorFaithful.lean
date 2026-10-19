import BC4lean.ModuleTensorOperator
import Mathlib.Analysis.CStarAlgebra.Hom

/-! Faithful amplification on the actual completed interior tensor.

If the coefficient representation is faithful, tensoring adjointable operators
with its module is faithful and isometric. The proof uses actual elementary
mixed inner products; no tensor norm equality or faithfulness conclusion is
assumed as input. This will detect reduced norms after regular amplification.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B C E F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

theorem interiorModuleTensorOperator_eq_zero_of_faithful
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (hφ : Function.Injective φ)
    (T : AdjointableMap B E E)
    (hT : interiorModuleTensorOperatorHom φ T = 0) : T = 0 := by
  have hmk (x : E) (y : F) : interiorModuleTensorMk φ (T x) y = 0 := by
    have h := congrArg (fun W : AdjointableMap C
      (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ) =>
        W (interiorModuleTensorMk φ x y)) hT
    simpa only [interiorModuleTensorOperatorHom_apply, interiorModuleTensorOperator_mk,
      AdjointableMap.coe_zero_apply] using h
  apply AdjointableMap.ext
  intro x
  change T x = 0
  apply (CStarModule.inner_self (A := Bᵐᵒᵖ)).mp
  have hrep : φ (MulOpposite.unop ⟪T x, T x⟫_(Bᵐᵒᵖ)) = 0 := by
    apply AdjointableMap.ext
    intro z
    change φ (MulOpposite.unop ⟪T x, T x⟫_(Bᵐᵒᵖ)) z = 0
    apply (CStarModule.inner_self (A := Cᵐᵒᵖ)).mp
    have h := congrArg
      (fun v : InteriorModuleTensor (E := E) φ =>
        ⟪interiorModuleTensorMk φ (T x)
          (φ (MulOpposite.unop ⟪T x, T x⟫_(Bᵐᵒᵖ)) z), v⟫_(Cᵐᵒᵖ)) (hmk x z)
    have hz : ⟪interiorModuleTensorMk φ (T x)
        (φ (MulOpposite.unop ⟪T x, T x⟫_(Bᵐᵒᵖ)) z),
        (0 : InteriorModuleTensor (E := E) φ)⟫_(Cᵐᵒᵖ) = 0 :=
      CStarModule.inner_zero_right (A := Cᵐᵒᵖ)
        (E := InteriorModuleTensor (E := E) φ)
    rw [hz] at h
    simpa only [interiorModuleTensorInner_mk_mk, moduleTensorPureInner] using h
  have ha : MulOpposite.unop ⟪T x, T x⟫_(Bᵐᵒᵖ) = 0 :=
    hφ (by simpa only [map_zero] using hrep)
  apply MulOpposite.unop_injective
  simpa only [MulOpposite.unop_zero] using ha

theorem interiorModuleTensorOperatorHom_injective
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (hφ : Function.Injective φ) :
    Function.Injective (interiorModuleTensorOperatorHom (E := E) φ) := by
  intro S T h
  have hz : interiorModuleTensorOperatorHom φ (S - T) = 0 := by
    rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp (interiorModuleTensorOperator_eq_zero_of_faithful φ hφ (S - T) hz)

theorem norm_interiorModuleTensorOperator_of_faithful
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (hφ : Function.Injective φ)
    (T : AdjointableMap B E E) : ‖interiorModuleTensorOperator φ T‖ = ‖T‖ :=
  NonUnitalStarAlgHom.norm_map (interiorModuleTensorOperatorHom φ)
    (interiorModuleTensorOperatorHom_injective φ hφ) T

end BC4lean.KKTheory
