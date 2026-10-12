import BC4lean.CoefficientImageIntervalModule
import BC4lean.IntervalModuleCompactFibre

/-! # Actual compact image multipliers on the right-module interval bridge

Constant left f(b) preserves the interval module and its adjoint preserves it
as well. The resulting star representation is compact because its actual
rank-one constant sections approximate left f(b) in operator norm. The two
completed endpoint unitaries intertwine this representation with the full
standard target action at zero and the true image-module action at one.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped InnerProductSpace Topology CStarAlgebra

variable {B C : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]

def coefficientImageIntervalCoefficientHom (f : B →⋆ₙₐ[ℂ] C) :
    B →⋆ₙₐ[ℂ] C(unitInterval, C) where
  toFun b := ContinuousMap.const unitInterval (f b)
  map_zero' := by apply ContinuousMap.ext; intro t; exact map_zero f
  map_add' a b := by apply ContinuousMap.ext; intro t; exact map_add f a b
  map_mul' a b := by apply ContinuousMap.ext; intro t; exact map_mul f a b
  map_smul' z b := by apply ContinuousMap.ext; intro t; exact map_smul f z b
  map_star' b := by apply ContinuousMap.ext; intro t; exact map_star f b

omit [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C] in
theorem coefficientImageIntervalSubmodule_left_mem (f : B →⋆ₙₐ[ℂ] C)
    (b : B) (s : C(unitInterval, C)ᵐᵒᵖ) (hs : s ∈ coefficientImageIntervalSubmodule f) :
    standardLeftMulCLM (coefficientImageIntervalCoefficientHom f b) s ∈
      coefficientImageIntervalSubmodule f := by
  exact coefficientImageClosedSubmodule_left_mem f b
    (MulOpposite.op (MulOpposite.unop s 1)) hs

def coefficientImageIntervalLeftMul (f : B →⋆ₙₐ[ℂ] C) :
    B →⋆ₙₐ[ℂ] AdjointableMap C(unitInterval, C)
      (CoefficientImageIntervalModule f) (CoefficientImageIntervalModule f) :=
  ClosedRightHilbertModule.representation (coefficientImageIntervalRightSubspace f)
    (coefficientImageIntervalCoefficientHom f) (coefficientImageIntervalSubmodule_left_mem f)

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem coefficientImageIntervalLeftMul_apply (f : B →⋆ₙₐ[ℂ] C)
    (b : B) (s : CoefficientImageIntervalModule f) (t : unitInterval) :
    MulOpposite.unop (coefficientImageIntervalLeftMul f b s : C(unitInterval, C)ᵐᵒᵖ) t =
      f b * MulOpposite.unop (s : C(unitInterval, C)ᵐᵒᵖ) t := rfl

def coefficientImageIntervalImageVector (f : B →⋆ₙₐ[ℂ] C) (b : B) :
    CoefficientImageIntervalModule f :=
  coefficientImageIntervalConstant f (coefficientImageVector f b)

omit [PartialOrder C] [StarOrderedRing C] in
@[simp] theorem coefficientImageIntervalImageVector_apply (f : B →⋆ₙₐ[ℂ] C)
    (b : B) (t : unitInterval) :
    MulOpposite.unop (coefficientImageIntervalImageVector f b : C(unitInterval, C)ᵐᵒᵖ) t =
      f b := rfl

/-- Every approximant is an actual J-rank one with both defining vectors in J. -/
theorem coefficientImageIntervalRankOne (f : B →⋆ₙₐ[ℂ] C) (a b : B) :
    moduleRankOne (B := C(unitInterval, C))
      (coefficientImageIntervalImageVector f a) (coefficientImageIntervalImageVector f (star b)) =
      coefficientImageIntervalLeftMul f (a * b) := by
  apply AdjointableMap.ext
  intro s
  apply Subtype.ext
  apply MulOpposite.unop_injective
  apply ContinuousMap.ext
  intro t
  change f a * (star (f (star b)) * MulOpposite.unop (s : C(unitInterval, C)ᵐᵒᵖ) t) =
    f (a * b) * MulOpposite.unop (s : C(unitInterval, C)ᵐᵒᵖ) t
  rw [map_star, star_star, map_mul, mul_assoc]

/-- The true coefficient approximate unit gives operator-norm compactness on J. -/
theorem coefficientImageIntervalLeftMul_isModuleCompact (f : B →⋆ₙₐ[ℂ] C) (b : B) :
    IsModuleCompact (coefficientImageIntervalLeftMul f b) := by
  have hlim : Tendsto (fun u : B => coefficientImageIntervalLeftMul f (b * u))
      (CStarAlgebra.approximateUnit B) (𝓝 (coefficientImageIntervalLeftMul f b)) :=
    (map_continuous (coefficientImageIntervalLeftMul f)).tendsto b |>.comp
      ((CStarAlgebra.increasingApproximateUnit B).tendsto_mul_left b)
  apply moduleCompact_isClosed.mem_of_tendsto hlim
  exact Eventually.of_forall fun u => by
    rw [← coefficientImageIntervalRankOne f b u]
    exact moduleRankOne_mem_moduleCompact _ _

omit [PartialOrder B] [StarOrderedRing B] in
theorem coefficientImageIntervalZeroFibreEquiv_leftMul (f : B →⋆ₙₐ[ℂ] C) (b : B)
    (z : HilbertModuleFibre C (CoefficientImageIntervalModule f) (0 : unitInterval)) :
    coefficientImageIntervalZeroFibreEquiv f
      (hilbertModuleFibreOperator (B := C) (0 : unitInterval) (coefficientImageIntervalLeftMul f b) z) =
    standardLeftMul (f b) (coefficientImageIntervalZeroFibreEquiv f z) := by
  obtain ⟨s, rfl⟩ := hilbertModuleFibreMk_surjective (B := C)
    (M := CoefficientImageIntervalModule f) (0 : unitInterval) z
  rw [hilbertModuleFibreOperator_mk, coefficientImageIntervalZeroFibreEquiv_mk,
    coefficientImageIntervalZeroFibreEquiv_mk]
  rfl

omit [PartialOrder B] [StarOrderedRing B] in
theorem coefficientImageIntervalOneFibreEquiv_leftMul (f : B →⋆ₙₐ[ℂ] C) (b : B)
    (z : HilbertModuleFibre C (CoefficientImageIntervalModule f) (1 : unitInterval)) :
    coefficientImageIntervalOneFibreEquiv f
      (hilbertModuleFibreOperator (B := C) (1 : unitInterval) (coefficientImageIntervalLeftMul f b) z) =
    coefficientImageLeftMul f b (coefficientImageIntervalOneFibreEquiv f z) := by
  obtain ⟨s, rfl⟩ := hilbertModuleFibreMk_surjective (B := C)
    (M := CoefficientImageIntervalModule f) (1 : unitInterval) z
  rw [hilbertModuleFibreOperator_mk, coefficientImageIntervalOneFibreEquiv_mk,
    coefficientImageIntervalOneFibreEquiv_mk]
  rfl

end BC4lean.KKTheory
