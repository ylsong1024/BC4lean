import BC4lean.AdjointableComplete
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # The genuine nonunital operator corner of an adjointable isometry

J*J=1 makes A↦JAJ* an actual nonunital star homomorphism. It preserves the
positive square root through the nonunital continuous functional calculus,
without a unit, an essentiality assumption, or an assumed compact identity.
-/

noncomputable section
open scoped CStarAlgebra
namespace BC4lean.KKTheory

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

def adjointableIsometricCornerHom (J : AdjointableMap B E F)
    (hJ : J.adjoint.comp J = AdjointableMap.id) :
    AdjointableMap B E E →⋆ₙₐ[ℂ] AdjointableMap B F F where
  toFun A := (J.comp A).comp J.adjoint
  map_zero' := by ext x; simp only [AdjointableMap.comp_apply, AdjointableMap.coe_zero_apply, map_zero]
  map_add' A D := by
    ext x
    simp only [AdjointableMap.comp_apply, AdjointableMap.coe_add_apply, J.toCLM.map_add]
  map_smul' c A := by
    ext x
    change J (c • A (J.adjoint x)) = c • J (A (J.adjoint x))
    exact J.toCLM.map_smul c _
  map_mul' A D := by
    ext x
    have hj (z : E) : J.adjoint (J z) = z := congrArg (fun T => T z) hJ
    change J (A (D (J.adjoint x))) = J (A (J.adjoint (J (D (J.adjoint x)))))
    rw [hj]
  map_star' A := by ext x; rfl

omit [StarOrderedRing B] in
@[simp] theorem adjointableIsometricCornerHom_apply (J : AdjointableMap B E F)
    (hJ : J.adjoint.comp J = AdjointableMap.id) (A : AdjointableMap B E E) :
    adjointableIsometricCornerHom J hJ A = (J.comp A).comp J.adjoint := rfl

variable [CompleteSpace E] [CompleteSpace F]
local instance standardAdjointableIsometricCornerHomLocalInstance01 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance standardAdjointableIsometricCornerHomLocalInstance02 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _
local instance standardAdjointableIsometricCornerHomLocalInstance03 : PartialOrder (AdjointableMap B F F) := CStarAlgebra.spectralOrder _
local instance standardAdjointableIsometricCornerHomLocalInstance04 : StarOrderedRing (AdjointableMap B F F) := CStarAlgebra.spectralOrderedRing _

theorem adjointableIsometricCornerHom_sqrt (J : AdjointableMap B E F)
    (hJ : J.adjoint.comp J = AdjointableMap.id) (A : AdjointableMap B E E) (hA : 0 ≤ A) :
    CFC.sqrt (adjointableIsometricCornerHom J hJ A) =
      adjointableIsometricCornerHom J hJ (CFC.sqrt A) := by
  have hφ : Continuous (adjointableIsometricCornerHom J hJ) :=
    AddMonoidHomClass.continuous_of_bound (adjointableIsometricCornerHom J hJ) 1
      (by
        intro T
        simpa only [one_mul] using
          NonUnitalStarAlgHom.norm_apply_le (adjointableIsometricCornerHom J hJ) T)
  unfold CFC.sqrt
  exact ((adjointableIsometricCornerHom J hJ).map_cfcₙ NNReal.sqrt A
    NNReal.continuous_sqrt.continuousOn NNReal.sqrt_zero
    hφ hA
    (map_nonneg (adjointableIsometricCornerHom J hJ) hA)).symm

end BC4lean.KKTheory
