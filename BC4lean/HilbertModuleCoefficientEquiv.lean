import BC4lean.OppositeStarAlgEquivBetween
import BC4lean.HilbertModuleCoefficientTransport
import BC4lean.HilbertModuleSum

/-! # Actual unitaries for invertible changes of Hilbert-module coefficients

Coefficient changes preserve genuine module unitaries. Applying a star
equivalence and its inverse gives an actual identity-on-vectors unitary;
the inner-product identity follows from cancellation of the coefficient maps.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B C E F : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

/-- A genuine module unitary, transported along the coefficient equivalence. -/
def HilbertModuleEquiv.coefficientChanged (u : HilbertModuleEquiv B E F)
    (e : B ≃⋆ₐ[ℂ] C) :
    HilbertModuleEquiv C (CoefficientChangedModule e E) (CoefficientChangedModule e F) where
  linearIsometryEquiv := u.linearIsometryEquiv
  inner_map x y := congrArg (opStarAlgEquivBetween e) (u.inner_map (x : E) (y : E))

@[simp] theorem HilbertModuleEquiv.coefficientChanged_apply
    (u : HilbertModuleEquiv B E F) (e : B ≃⋆ₐ[ℂ] C)
    (x : CoefficientChangedModule e E) : u.coefficientChanged e x = u (x : E) := rfl

/-- The inverse coefficient change restores the entire original module,
by an actual unitary rather than an equality of carriers alone. -/
def coefficientChangedInverseEquiv (e : B ≃⋆ₐ[ℂ] C) :
    HilbertModuleEquiv B
      (CoefficientChangedModule e.symm (CoefficientChangedModule e E)) E where
  linearIsometryEquiv :=
    { toFun := id
      invFun := id
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      norm_map' _ := rfl }
  inner_map x y := by
    change ⟪coefficientChangedToOriginal (M := E) e
        (coefficientChangedToOriginal (M := CoefficientChangedModule e E) e.symm x),
      coefficientChangedToOriginal (M := E) e
        (coefficientChangedToOriginal (M := CoefficientChangedModule e E) e.symm y)⟫_(Bᵐᵒᵖ) =
      opStarAlgEquivBetween e.symm (opStarAlgEquivBetween e
        ⟪coefficientChangedToOriginal (M := E) e
            (coefficientChangedToOriginal (M := CoefficientChangedModule e E) e.symm x),
          coefficientChangedToOriginal (M := E) e
            (coefficientChangedToOriginal (M := CoefficientChangedModule e E) e.symm y)⟫_(Bᵐᵒᵖ))
    rw [coefficientChanged_op_symm_apply_apply]

@[simp] theorem coefficientChangedInverseEquiv_apply (e : B ≃⋆ₐ[ℂ] C)
    (x : CoefficientChangedModule e.symm (CoefficientChangedModule e E)) :
    coefficientChangedInverseEquiv e x = (x : E) := rfl

/-- Coefficient transport commutes with the actual coefficient-Hilbert sum.
The changed inner product maps the sum of the original two inner products. -/
def coefficientChangedSumEquiv (e : B ≃⋆ₐ[ℂ] C) :
    HilbertModuleEquiv C (CoefficientChangedModule e (HilbertModuleSum B E F))
      (HilbertModuleSum C (CoefficientChangedModule e E) (CoefficientChangedModule e F)) := by
  let L : CoefficientChangedModule e (HilbertModuleSum B E F) →ₗ[ℂ]
      HilbertModuleSum C (CoefficientChangedModule e E) (CoefficientChangedModule e F) :=
    { toFun x := sumMk (x : HilbertModuleSum B E F).fst (x : HilbertModuleSum B E F).snd
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hinner (x y : CoefficientChangedModule e (HilbertModuleSum B E F)) :
      ⟪L x, L y⟫_(Cᵐᵒᵖ) = ⟪x, y⟫_(Cᵐᵒᵖ) := by
    change opStarAlgEquivBetween e
        ⟪(coefficientChangedToOriginal (M := HilbertModuleSum B E F) e x).fst,
          (coefficientChangedToOriginal (M := HilbertModuleSum B E F) e y).fst⟫_(Bᵐᵒᵖ) +
      opStarAlgEquivBetween e
        ⟪(coefficientChangedToOriginal (M := HilbertModuleSum B E F) e x).snd,
          (coefficientChangedToOriginal (M := HilbertModuleSum B E F) e y).snd⟫_(Bᵐᵒᵖ) =
      opStarAlgEquivBetween e
        ⟪coefficientChangedToOriginal (M := HilbertModuleSum B E F) e x,
          coefficientChangedToOriginal (M := HilbertModuleSum B E F) e y⟫_(Bᵐᵒᵖ)
    rw [inner_sum, map_add]
  exact
    { linearIsometryEquiv :=
        { toFun := L
          invFun y := sumMk (B := B) y.fst y.snd
          left_inv _ := rfl
          right_inv _ := rfl
          map_add' := L.map_add
          map_smul' := L.map_smul
          norm_map' x := by
            change ‖L x‖ = ‖x‖
            calc
              ‖L x‖ = Real.sqrt ‖⟪L x, L x⟫_(Cᵐᵒᵖ)‖ :=
                CStarModule.norm_eq_sqrt_norm_inner_self
                  (A := Cᵐᵒᵖ)
                  (E := HilbertModuleSum C (CoefficientChangedModule e E) (CoefficientChangedModule e F))
                  (L x)
              _ = Real.sqrt ‖⟪x, x⟫_(Cᵐᵒᵖ)‖ :=
                congrArg (fun a : Cᵐᵒᵖ => Real.sqrt ‖a‖) (hinner x x)
              _ = ‖x‖ :=
                (CStarModule.norm_eq_sqrt_norm_inner_self
                  (A := Cᵐᵒᵖ) (E := CoefficientChangedModule e (HilbertModuleSum B E F)) x).symm }
      inner_map := hinner }

@[simp] theorem coefficientChangedSumEquiv_apply (e : B ≃⋆ₐ[ℂ] C)
    (x : CoefficientChangedModule e (HilbertModuleSum B E F)) :
    coefficientChangedSumEquiv e x =
      sumMk (x : HilbertModuleSum B E F).fst (x : HilbertModuleSum B E F).snd := rfl

end BC4lean.KKTheory
