import BC4lean.OrdinaryScalarCoefficientTensor
import BC4lean.InteriorModuleTensorFirstFactorEquiv
import BC4lean.KasparovCycleIso

/-! # Whole ordinary coefficient tensors preserve raw cycle isomorphisms

The first-factor unitary preserves the actual entire coefficient form and
maps pure tensors to the tensors of the original unitary. Continuity and
dense pure tensors prove the grading intertwining. The representation and
Fredholm operator use their actual whole first-factor intertwinings.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B C E E' : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [SMul Bᵐᵒᵖ E'] [CStarModule Bᵐᵒᵖ E']
  [CompleteSpace E] [CompleteSpace E']
local notation "α₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
local notation "β₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B)

/-- Independent carrier universes are preserved by the genuine completed tensor unitary. -/
def KasparovCycleIso.scalarCoefficientTensor {c : KasparovCycle α₁ β₁ E}
    {d : KasparovCycle α₁ β₁ E'} (e : KasparovCycleIso c d) (f : B →⋆ₙₐ[ℂ] C) :
    KasparovCycleIso (c.scalarCoefficientTensor f) (d.scalarCoefficientTensor f) where
  moduleEquiv := InteriorModuleTensorFirstFactorEquiv.hilbertEquiv
    (standardCoefficientImageRepresentation f) e.moduleEquiv
  grading_intertwine z := by
    let φ : B →⋆ₙₐ[ℂ] AdjointableMap C Cᵐᵒᵖ Cᵐᵒᵖ := standardCoefficientImageRepresentation f
    let U : InteriorModuleTensor (E := E) φ →L[ℂ] InteriorModuleTensor (E := E') φ :=
      (InteriorModuleTensorFirstFactorEquiv.hilbertEquiv φ e.moduleEquiv).toAdjointable.toCLM
    have h : U.comp (c.grading.interiorTensor GradedHilbertModule.trivial
          (φ := φ) (fun _ _ => rfl)).grading.toContinuousLinearEquiv.toContinuousLinearMap =
        (d.grading.interiorTensor GradedHilbertModule.trivial
          (φ := φ) (fun _ _ => rfl)).grading.toContinuousLinearEquiv.toContinuousLinearMap.comp U := by
      apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      intro x y
      change InteriorModuleTensorFirstFactorEquiv.hilbertEquiv φ e.moduleEquiv
          ((c.grading.interiorTensor GradedHilbertModule.trivial
            (φ := φ) (fun _ _ => rfl)).grading (interiorModuleTensorMk (E := E) φ x y)) =
        (d.grading.interiorTensor GradedHilbertModule.trivial
          (φ := φ) (fun _ _ => rfl)).grading
          (InteriorModuleTensorFirstFactorEquiv.hilbertEquiv φ e.moduleEquiv
            (interiorModuleTensorMk (E := E) φ x y))
      rw [GradedHilbertModule.interiorTensor_grading_mk (φ := φ) c.grading
          GradedHilbertModule.trivial (fun _ _ => rfl) x y,
        InteriorModuleTensorFirstFactorEquiv.hilbertEquiv_mk,
        InteriorModuleTensorFirstFactorEquiv.hilbertEquiv_mk,
        GradedHilbertModule.interiorTensor_grading_mk (φ := φ) d.grading
          GradedHilbertModule.trivial (fun _ _ => rfl) (e.moduleEquiv x) y]
      exact congrArg (fun w : E' => interiorModuleTensorMk (E := E') φ w y)
        (e.grading_intertwine x)
    exact DFunLike.congr_fun h z
  action_intertwine _ _ := rfl
  representation_intertwine a z :=
    InteriorModuleTensorFirstFactorEquiv.hilbertEquiv_operator
      (standardCoefficientImageRepresentation f) e.moduleEquiv
      (c.representation a) (d.representation a) (e.representation_intertwine a) z
  operator_intertwine z :=
    InteriorModuleTensorFirstFactorEquiv.hilbertEquiv_operator
      (standardCoefficientImageRepresentation f) e.moduleEquiv
      c.operator d.operator e.operator_intertwine z

end BC4lean.KKTheory
