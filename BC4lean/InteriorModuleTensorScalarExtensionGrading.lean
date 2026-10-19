import BC4lean.InteriorModuleTensorScalarExtension
import BC4lean.StandardHilbertModuleActions

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Genuine grading compatibility of coefficient-extension composition

The same actual scalar
extension unitary intertwines the full semilinear gradings. Neither an even
unitary nor a grading on its conclusion is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory.InteriorModuleTensorScalarExtension

variable {B D C E H : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H]
  [CStarModule Cᵐᵒᵖ H] [CompleteSpace H]
  (i : B →⋆ₙₐ[ℂ] D) (ρ : D →⋆ₙₐ[ℂ] AdjointableMap C H H)
  (ψ : B →⋆ₙₐ[ℂ] AdjointableMap C H H) (hρ : ∀ b, ρ (i b) = ψ b)
  {δB : CStarGrading B} {δD : CStarGrading D} {δC : CStarGrading C}
  (hi : ∀ b, δD.automorphism (i b) = i (δB.automorphism b))
  (J : GradedHilbertModule δB E) (K : GradedHilbertModule δC H)
  (hρJ : ModuleTensorRepresentationGraded (δB := δD) ρ K)

omit [PartialOrder B] [StarOrderedRing B] in
include hi in
/-- The standard coefficient extension respects the two actual coefficient gradings. -/
theorem standardRepresentation_graded :
    ModuleTensorRepresentationGraded (δB := δB) (standardRepresentation i)
      (GradedHilbertModule.standard δD) := by
  intro b d
  change MulOpposite.op (δD.automorphism (i b * MulOpposite.unop d)) =
    MulOpposite.op (i (δB.automorphism b) * δD.automorphism (MulOpposite.unop d))
  rw [map_mul, hi]

omit [PartialOrder B] [StarOrderedRing B]
  [PartialOrder D] [StarOrderedRing D]
  [StarOrderedRing C] [CompleteSpace H] in
include hρ hi hρJ in
/-- The target representation inherits gradedness from the actual composition identity. -/
theorem targetRepresentation_graded : ModuleTensorRepresentationGraded (δB := δB) ψ K := by
  intro b y
  rw [← hρ, hρJ, hi, hρ]

/-- The entire completed comparison unitary intertwines the full genuine
semilinear tensor gradings, proved on triple pure tensors and extended by
completed tensor extensionality. -/
theorem hilbertEquiv_grading
    (u : SourceTensor (E := E) i ρ) :
    hilbertEquiv i ρ ψ hρ
      ((((J.interiorTensor (GradedHilbertModule.standard δD)
        (standardRepresentation_graded i hi)).interiorTensor K hρJ).grading) u) =
    (J.interiorTensor K (targetRepresentation_graded i ρ ψ hρ hi K hρJ)).grading
      (hilbertEquiv i ρ ψ hρ u) := by
  let W := (hilbertEquiv (E := E) i ρ ψ hρ).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  let JL := ((J.interiorTensor (GradedHilbertModule.standard δD)
    (standardRepresentation_graded i hi)).interiorTensor K hρJ).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let JR := (J.interiorTensor K (targetRepresentation_graded i ρ ψ hρ hi K hρJ)).grading.toContinuousLinearEquiv.toContinuousLinearMap
  have h : W.comp JL = JR.comp W := by
    apply InteriorModuleTensorAssociator.left_clm_ext (standardRepresentation i) ρ
    intro x d y
    change hilbertEquiv i ρ ψ hρ
      ((((J.interiorTensor (GradedHilbertModule.standard δD)
        (standardRepresentation_graded i hi)).interiorTensor K hρJ).grading)
          (interiorModuleTensorMk ρ (interiorModuleTensorMk (standardRepresentation i) x d) y)) =
      (J.interiorTensor K (targetRepresentation_graded i ρ ψ hρ hi K hρJ)).grading
        (hilbertEquiv i ρ ψ hρ
          (interiorModuleTensorMk ρ (interiorModuleTensorMk (standardRepresentation i) x d) y))
    rw [GradedHilbertModule.interiorTensor_grading_mk,
      GradedHilbertModule.interiorTensor_grading_mk, hilbertEquiv_triple,
      hilbertEquiv_triple, GradedHilbertModule.interiorTensor_grading_mk,
      GradedHilbertModule.standard_grading_apply, MulOpposite.unop_op, hρJ]
  exact DFunLike.congr_fun h u

end BC4lean.KKTheory.InteriorModuleTensorScalarExtension
