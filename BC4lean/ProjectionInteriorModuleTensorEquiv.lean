import BC4lean.RectangularInteriorModuleTensorOperator
import BC4lean.OddFredholmProjectionFibreEquiv

/-! # Actual projection ranges commute with the completed interior tensor

The rectangular tensor of the genuine range inclusion is an adjointable
isometry whose range projection is exactly the tensor of the ambient
projection. Its true isometric-range unitary gives the whole equivalence,
including zero and nonessential representations.
-/

noncomputable section
namespace BC4lean.KKTheory
open RectangularInteriorModuleTensorOperator

variable {B C E F : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)

def projectionInteriorModuleTensorInclusion (P : AdjointableMap B E E) (hP : IsStarProjection P) :
    AdjointableMap C (InteriorModuleTensor (E := ProjectionModule P) φ)
      (InteriorModuleTensor (E := E) φ) := tensor φ (projectionInclusion P hP)

theorem projectionInteriorModuleTensorInclusion_adjoint_comp
    (P : AdjointableMap B E E) (hP : IsStarProjection P) :
    (projectionInteriorModuleTensorInclusion φ P hP).adjoint.comp
      (projectionInteriorModuleTensorInclusion φ P hP) = AdjointableMap.id := by
  rw [projectionInteriorModuleTensorInclusion, tensor_adjoint, ← tensor_comp]
  change tensor φ ((projectionCorestrict P hP).comp (projectionInclusion P hP)) = _
  rw [projectionCorestrict_comp_inclusion, tensor_endo]
  change interiorModuleTensorOperatorHom φ 1 = 1
  exact map_one _

theorem projectionInteriorModuleTensorInclusion_comp_adjoint
    (P : AdjointableMap B E E) (hP : IsStarProjection P) :
    (projectionInteriorModuleTensorInclusion φ P hP).comp
      (projectionInteriorModuleTensorInclusion φ P hP).adjoint = interiorModuleTensorOperator φ P := by
  rw [projectionInteriorModuleTensorInclusion, tensor_adjoint, ← tensor_comp]
  change tensor φ ((projectionInclusion P hP).comp (projectionCorestrict P hP)) = _
  rw [projectionInclusion_comp_corestrict, tensor_endo]

def projectionInteriorModuleTensorEquiv (P : AdjointableMap B E E) (hP : IsStarProjection P) :
    HilbertModuleEquiv C (InteriorModuleTensor (E := ProjectionModule P) φ)
      (ProjectionModule (interiorModuleTensorOperator φ P)) :=
  oddFredholmIsometricRangeEquiv (projectionInteriorModuleTensorInclusion φ P hP)
    (interiorModuleTensorOperator φ P)
    (projectionInteriorModuleTensorInclusion_adjoint_comp φ P hP)
    (projectionInteriorModuleTensorInclusion_comp_adjoint φ P hP)

@[simp] theorem projectionInteriorModuleTensorEquiv_mk_coe
    (P : AdjointableMap B E E) (hP : IsStarProjection P) (x : ProjectionModule P) (y : F) :
    ((projectionInteriorModuleTensorEquiv φ P hP (interiorModuleTensorMk φ x y) :
      ProjectionModule (interiorModuleTensorOperator φ P)) : InteriorModuleTensor (E := E) φ) =
        interiorModuleTensorMk φ (x : E) y :=
  tensor_mk φ (projectionInclusion P hP) x y

end BC4lean.KKTheory
