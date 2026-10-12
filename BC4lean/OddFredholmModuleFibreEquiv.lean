import BC4lean.RectangularModuleFibreOperator
import BC4lean.KasparovDirectSumIso
import BC4lean.OddFredholmAbsorptionIndependence

/-! # Actual evaluated module unitaries for the odd index

Rectangular fibre maps evaluate the genuine adjointable module isomorphism
and its inverse. The resulting inverse equations and coefficient adjoint
identity construct the whole Hilbert-module unitary, not an assumed fibre
identification or a finite-coordinate identification.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace CStarAlgebra

variable {B X M N : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, B)ᵐᵒᵖ M]
  [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]
  [NormedAddCommGroup N] [NormedSpace ℂ N] [SMul C(X, B)ᵐᵒᵖ N]
  [CStarModule C(X, B)ᵐᵒᵖ N] [CompleteSpace N]

def oddFredholmModuleFibreForward (u : HilbertModuleEquiv C(X, B) M N) (t : X) :
    AdjointableMap B (HilbertModuleFibre B M t) (HilbertModuleFibre B N t) :=
  hilbertModuleFibreRectangularMap t u.toAdjointable

theorem oddFredholmModuleFibreForward_inverse
    (u : HilbertModuleEquiv C(X, B) M N) (t : X) :
    (oddFredholmModuleFibreForward u.symm t).comp (oddFredholmModuleFibreForward u t) =
      AdjointableMap.id := by
  ext z
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := M) t z
  simp only [oddFredholmModuleFibreForward, AdjointableMap.comp_apply,
    hilbertModuleFibreRectangularMap_mk, HilbertModuleEquiv.toAdjointable_apply,
    HilbertModuleEquiv.symm_apply_apply, AdjointableMap.id_apply]

theorem oddFredholmModuleFibreForward_inner
    (u : HilbertModuleEquiv C(X, B) M N) (t : X)
    (x y : HilbertModuleFibre B M t) :
    ⟪oddFredholmModuleFibreForward u t x, oddFredholmModuleFibreForward u t y⟫_(Bᵐᵒᵖ) =
      ⟪x, y⟫_(Bᵐᵒᵖ) := by
  rw [(oddFredholmModuleFibreForward u t).adjoint_identity]
  have hs : (oddFredholmModuleFibreForward u t).adjoint = oddFredholmModuleFibreForward u.symm t := by
    simp only [oddFredholmModuleFibreForward, hilbertModuleFibreRectangularMap_adjoint,
      HilbertModuleEquiv.toAdjointable_adjoint]
  change ⟪x, (oddFredholmModuleFibreForward u t).adjoint
      (oddFredholmModuleFibreForward u t y)⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ)
  rw [hs, ← AdjointableMap.comp_apply, oddFredholmModuleFibreForward_inverse, AdjointableMap.id_apply]

/-- The whole actual unitary of the two evaluated completed modules. -/
def oddFredholmModuleFibreEquiv (u : HilbertModuleEquiv C(X, B) M N) (t : X) :
    HilbertModuleEquiv B (HilbertModuleFibre B M t) (HilbertModuleFibre B N t) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun := oddFredholmModuleFibreForward u t
          invFun := oddFredholmModuleFibreForward u.symm t
          left_inv x := by
            simpa only [AdjointableMap.comp_apply, AdjointableMap.id_apply] using
              congrArg (fun T => T x) (oddFredholmModuleFibreForward_inverse u t)
          right_inv x := by
            simpa only [AdjointableMap.comp_apply, AdjointableMap.id_apply, HilbertModuleEquiv.symm_symm] using
              congrArg (fun T => T x) (oddFredholmModuleFibreForward_inverse u.symm t)
          map_add' := (oddFredholmModuleFibreForward u t).toCLM.map_add
          map_smul' := (oddFredholmModuleFibreForward u t).toCLM.map_smul }
      norm_map' x := by
        change ‖oddFredholmModuleFibreForward u t x‖ = ‖x‖
        calc
          _ = Real.sqrt ‖⟪oddFredholmModuleFibreForward u t x,
              oddFredholmModuleFibreForward u t x⟫_(Bᵐᵒᵖ)‖ :=
            completion_norm_eq_sqrt_inner (B := B)
              (E := PositiveModuleQuotient B (EvaluatedModuleSpace B N t))
              (oddFredholmModuleFibreForward u t x)
          _ = Real.sqrt ‖⟪x, x⟫_(Bᵐᵒᵖ)‖ :=
            congrArg (fun b : Bᵐᵒᵖ => Real.sqrt ‖b‖)
              (oddFredholmModuleFibreForward_inner u t x x)
          _ = ‖x‖ := (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm }
  inner_map := oddFredholmModuleFibreForward_inner u t

@[simp] theorem oddFredholmModuleFibreEquiv_mk
    (u : HilbertModuleEquiv C(X, B) M N) (t : X) (x : M) :
    oddFredholmModuleFibreEquiv u t (hilbertModuleFibreMk (B := B) t x) =
      hilbertModuleFibreMk (B := B) t (u x) :=
  hilbertModuleFibreRectangularMap_mk t u.toAdjointable x

/-- Whole operator transport and genuine fibre evaluation commute. -/
theorem oddFredholmModuleFibreEquiv_transport
    (u : HilbertModuleEquiv C(X, B) M N) (t : X) (T : AdjointableMap C(X, B) M M) :
    (oddFredholmModuleFibreEquiv u t).transport (hilbertModuleFibreOperator (B := B) t T) =
      hilbertModuleFibreOperator (B := B) t (u.transport T) := by
  ext z
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := N) t z
  change oddFredholmModuleFibreForward u t
      (hilbertModuleFibreOperator (B := B) t T
        (oddFredholmModuleFibreForward u.symm t (hilbertModuleFibreMk (B := B) t x))) = _
  simp only [oddFredholmModuleFibreForward, hilbertModuleFibreRectangularMap_mk,
    HilbertModuleEquiv.toAdjointable_apply, hilbertModuleFibreOperator_mk,
    HilbertModuleEquiv.transport_apply]

end BC4lean.KKTheory
