import BC4lean.GradedMatrixMoritaFibreTensorCompatibility
import BC4lean.GradedMatrixMoritaSecondFibreTensorCompatibility
import BC4lean.RectangularModuleFibreOperator

/-! # Genuine rectangular fibre creation intertwinings in both variables

This leaf consumes the separately constructed rectangular fibre map. The
whole-module identities use actual canonical fibre surjectivity and the
previously proved evaluation/creation and evaluation/adjoint formulas.
No compactness or multiplier extension is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory.GradedMatrixMoritaFibreCreationCompatibility
open scoped InnerProductSpace

section FirstVariable

variable {B C X E F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul C(X, B)ᵐᵒᵖ E]
  [CStarModule C(X, B)ᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (t : X) (x : E)

theorem first_creation
    (s : HilbertModuleFibre C C(X, F) t) :
    GradedMatrixMoritaFibreTensor.hilbertEquiv φ t
      (hilbertModuleFibreRectangularMap t
        (moduleCreationMap (GradedMatrixMoritaSectionRepresentation.leftAction φ) x) s) =
      moduleCreationMap φ (hilbertModuleFibreMk (B := B) t x)
        (continuousSectionHilbertModuleFibreEquiv (B := C) t s) := by
  obtain ⟨y, rfl⟩ := hilbertModuleFibreMk_surjective (B := C) (M := C(X, F)) t s
  rw [hilbertModuleFibreRectangularMap_mk, GradedMatrixMoritaFibreTensor.hilbertEquiv_mk,
    GradedMatrixMoritaFibreTensor.evaluation_creation, continuousSectionHilbertModuleFibreEquiv_mk]

theorem first_creation_adjoint
    (z : HilbertModuleFibre C (GradedMatrixMoritaFibreTensor.SectionsTensor (E := E) φ) t) :
    continuousSectionHilbertModuleFibreEquiv (B := C) t
      (hilbertModuleFibreRectangularMap t
        (moduleCreationMap (GradedMatrixMoritaSectionRepresentation.leftAction φ) x).adjoint z) =
      (moduleCreationMap φ (hilbertModuleFibreMk (B := B) t x)).adjoint
        (GradedMatrixMoritaFibreTensor.hilbertEquiv φ t z) := by
  obtain ⟨u, rfl⟩ := hilbertModuleFibreMk_surjective (B := C)
    (M := GradedMatrixMoritaFibreTensor.SectionsTensor (E := E) φ) t z
  rw [hilbertModuleFibreRectangularMap_mk, continuousSectionHilbertModuleFibreEquiv_mk,
    GradedMatrixMoritaFibreTensor.hilbertEquiv_mk]
  exact GradedMatrixMoritaFibreTensor.evaluation_creation_adjoint φ t x u

set_option maxHeartbeats 8000000 in
theorem first_creation_operator :
    (GradedMatrixMoritaFibreTensor.hilbertEquiv
      (B := B) (C := C) (X := X) (E := E) (F := F) φ t).toAdjointable.comp
      (hilbertModuleFibreRectangularMap (B := C) (X := X) (M := C(X, F))
        (N := GradedMatrixMoritaFibreTensor.SectionsTensor (E := E) φ) t
        (moduleCreationMap (B := C(X, B)) (C := C(X, C)) (E := E) (F := C(X, F))
          (GradedMatrixMoritaSectionRepresentation.leftAction (X := X) φ) x)) =
      (moduleCreationMap (B := B) (C := C)
        (E := HilbertModuleFibre B E t) (F := F) φ
        (hilbertModuleFibreMk (B := B) (X := X) (M := E) t x)).comp
          (continuousSectionHilbertModuleFibreEquiv (B := C) (X := X) (E := F) t).toAdjointable := by
  apply AdjointableMap.ext
  intro s
  exact first_creation φ t x s

end FirstVariable

section SecondVariable

variable {B C X E M : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, C)ᵐᵒᵖ M]
  [CStarModule C(X, C)ᵐᵒᵖ M] [CompleteSpace E] [CompleteSpace M]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C(X, C) M M) (t : X) (x : E)

theorem second_creation (y : HilbertModuleFibre C M t) :
    GradedMatrixMoritaSecondFibreTensor.hilbertEquiv φ t
      (hilbertModuleFibreRectangularMap t (moduleCreationMap φ x) y) =
      moduleCreationMap (GradedMatrixMoritaSecondFibreTensor.fibreRepresentation φ t) x y := by
  obtain ⟨z, rfl⟩ := hilbertModuleFibreMk_surjective (B := C) (M := M) t y
  rw [hilbertModuleFibreRectangularMap_mk, GradedMatrixMoritaSecondFibreTensor.hilbertEquiv_mk,
    GradedMatrixMoritaSecondFibreTensor.evaluation_creation]

theorem second_creation_adjoint
    (z : HilbertModuleFibre C (InteriorModuleTensor (E := E) φ) t) :
    hilbertModuleFibreRectangularMap t (moduleCreationMap φ x).adjoint z =
      (moduleCreationMap (GradedMatrixMoritaSecondFibreTensor.fibreRepresentation φ t) x).adjoint
        (GradedMatrixMoritaSecondFibreTensor.hilbertEquiv φ t z) := by
  obtain ⟨u, rfl⟩ := hilbertModuleFibreMk_surjective (B := C)
    (M := InteriorModuleTensor (E := E) φ) t z
  rw [hilbertModuleFibreRectangularMap_mk, GradedMatrixMoritaSecondFibreTensor.hilbertEquiv_mk]
  exact GradedMatrixMoritaSecondFibreTensor.evaluation_creation_adjoint φ t x u

theorem second_creation_operator :
    (GradedMatrixMoritaSecondFibreTensor.hilbertEquiv (E := E) φ t).toAdjointable.comp
      (hilbertModuleFibreRectangularMap t (moduleCreationMap φ x)) =
      moduleCreationMap (GradedMatrixMoritaSecondFibreTensor.fibreRepresentation φ t) x := by
  apply AdjointableMap.ext
  intro y
  exact second_creation φ t x y

end SecondVariable
end BC4lean.KKTheory.GradedMatrixMoritaFibreCreationCompatibility
