import BC4lean.GlobalFredholmNormalization
import BC4lean.FredholmJuliaProjection
import BC4lean.KasparovDirectSumIso

/-! # Normalization and Julia projections under actual module unitaries

Unitary transport preserves the two rectangular adjoint squares. The actual
functional calculus therefore transports the normalization weight and the
positive source defect square root. The whole Julia column and projection,
including their off-diagonal entries, transport by the sum unitary.
-/

noncomputable section
open scoped CStarAlgebra
namespace BC4lean.KKTheory

section Composition
variable {B E F G E' F' G' : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [SMul Bᵐᵒᵖ E'] [CStarModule Bᵐᵒᵖ E']
  [NormedAddCommGroup F'] [NormedSpace ℂ F'] [SMul Bᵐᵒᵖ F'] [CStarModule Bᵐᵒᵖ F']
  [NormedAddCommGroup G'] [NormedSpace ℂ G'] [SMul Bᵐᵒᵖ G'] [CStarModule Bᵐᵒᵖ G']

theorem HilbertModuleEquiv.transportMap_comp (u : HilbertModuleEquiv B E E')
    (v : HilbertModuleEquiv B F F') (w : HilbertModuleEquiv B G G')
    (S : AdjointableMap B F G) (T : AdjointableMap B E F) :
    (v.transportMap w S).comp (u.transportMap v T) = u.transportMap w (S.comp T) := by
  apply AdjointableMap.ext
  intro x
  simp only [AdjointableMap.comp_apply, HilbertModuleEquiv.transportMap_apply,
    HilbertModuleEquiv.symm_apply_apply]

theorem HilbertModuleEquiv.transportMap_source_square (u : HilbertModuleEquiv B E E')
    (v : HilbertModuleEquiv B F F') (T : AdjointableMap B E F) :
    (u.transportMap v T).adjoint.comp (u.transportMap v T) = u.transport (T.adjoint.comp T) := by
  rw [HilbertModuleEquiv.transportMap_adjoint, HilbertModuleEquiv.transportMap_comp]
  rfl

theorem HilbertModuleEquiv.transportMap_target_square (u : HilbertModuleEquiv B E E')
    (v : HilbertModuleEquiv B F F') (T : AdjointableMap B E F) :
    (u.transportMap v T).comp (u.transportMap v T).adjoint = v.transport (T.comp T.adjoint) := by
  rw [HilbertModuleEquiv.transportMap_adjoint, HilbertModuleEquiv.transportMap_comp]
  rfl

end Composition

variable {B E F E' F' : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [SMul Bᵐᵒᵖ E'] [CStarModule Bᵐᵒᵖ E']
  [NormedAddCommGroup F'] [NormedSpace ℂ F'] [SMul Bᵐᵒᵖ F'] [CStarModule Bᵐᵒᵖ F']
  [completeE : CompleteSpace E] [completeF : CompleteSpace F]
  [completeE' : CompleteSpace E'] [completeF' : CompleteSpace F']

local instance standardRectangularFredholmNormalizationNaturalityLocalInstance01 : PartialOrder (AdjointableMap B E E) := CStarAlgebra.spectralOrder _
local instance standardRectangularFredholmNormalizationNaturalityLocalInstance02 : StarOrderedRing (AdjointableMap B E E) := CStarAlgebra.spectralOrderedRing _
local instance standardRectangularFredholmNormalizationNaturalityLocalInstance03 : PartialOrder (AdjointableMap B E' E') := CStarAlgebra.spectralOrder _
local instance standardRectangularFredholmNormalizationNaturalityLocalInstance04 : StarOrderedRing (AdjointableMap B E' E') := CStarAlgebra.spectralOrderedRing _

/-- The actual normalization weight is natural under rectangular unitary transport. -/
theorem globalFredholmNormalizer_transport (u : HilbertModuleEquiv B E E')
    (v : HilbertModuleEquiv B F F') (T : AdjointableMap B E F) :
    globalFredholmNormalizer (u.transportMap v T) = u.transport (globalFredholmNormalizer T) := by
  unfold globalFredholmNormalizer
  rw [HilbertModuleEquiv.transportMap_source_square]
  exact (u.transportStarAlgEquiv.toStarAlgHom.map_cfc fredholmNormWeight (T.adjoint.comp T)
    continuous_fredholmNormWeight.continuousOn
    (StarAlgEquiv.isometry u.transportStarAlgEquiv).continuous
    (rectangular_adjoint_squares_nonneg T).2.isSelfAdjoint
    (by
      change IsSelfAdjoint (u.transport (T.adjoint.comp T))
      rw [← HilbertModuleEquiv.transportMap_source_square u v T]
      exact (rectangular_adjoint_squares_nonneg (u.transportMap v T)).2.isSelfAdjoint)).symm

/-- No normalization choices are made: the defined contraction transports exactly. -/
theorem globalFredholmNormalization_transport (u : HilbertModuleEquiv B E E')
    (v : HilbertModuleEquiv B F F') (T : AdjointableMap B E F) :
    globalFredholmNormalization (u.transportMap v T) = u.transportMap v (globalFredholmNormalization T) := by
  unfold globalFredholmNormalization
  rw [globalFredholmNormalizer_transport]
  exact HilbertModuleEquiv.transportMap_comp u u v T (globalFredholmNormalizer T)

/-- The actual positive defect root transports by the source unitary. -/
theorem juliaSourceDefect_transport (u : HilbertModuleEquiv B E E')
    (v : HilbertModuleEquiv B F F') (T : AdjointableMap B E F) (hT : ‖T‖ ≤ 1) :
    juliaSourceDefect (u.transportMap v T) = u.transport (juliaSourceDefect T) := by
  have hEq : 1 - (u.transportMap v T).adjoint.comp (u.transportMap v T) =
      u.transport (1 - T.adjoint.comp T) := by
    rw [HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_one,
      HilbertModuleEquiv.transportMap_source_square]
  unfold juliaSourceDefect
  rw [hEq, CFC.sqrt_eq_cfc, CFC.sqrt_eq_cfc]
  exact (u.transportStarAlgEquiv.toStarAlgHom.map_cfc NNReal.sqrt (1 - T.adjoint.comp T)
    NNReal.continuous_sqrt.continuousOn
    (StarAlgEquiv.isometry u.transportStarAlgEquiv).continuous
    (one_sub_adjoint_comp_self_nonneg T hT)
    (by
      change 0 ≤ u.transport (1 - T.adjoint.comp T)
      rw [← hEq]
      exact one_sub_adjoint_comp_self_nonneg (u.transportMap v T)
        (by rw [HilbertModuleEquiv.transportMap_norm]; exact hT))).symm

/-- Naturality holds for the whole Julia column, not just its diagonal blocks. -/
theorem juliaFredholmColumn_transport (u : HilbertModuleEquiv B E E')
    (v : HilbertModuleEquiv B F F') (T : AdjointableMap B E F) (hT : ‖T‖ ≤ 1) :
    juliaFredholmColumn (u.transportMap v T) = u.transportMap (u.sum v) (juliaFredholmColumn T) := by
  apply AdjointableMap.ext
  intro x
  simp only [juliaFredholmColumn_apply, juliaSourceDefect_transport u v T hT,
    HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.transportMap_apply,
    HilbertModuleEquiv.sum_apply, sumMk_fst, sumMk_snd]

/-- The actual Julia projection conjugates by the whole sum unitary. -/
theorem juliaFredholmProjection_transport (u : HilbertModuleEquiv B E E')
    (v : HilbertModuleEquiv B F F') (T : AdjointableMap B E F) (hT : ‖T‖ ≤ 1) :
    juliaFredholmProjection (u.transportMap v T) = (u.sum v).transport (juliaFredholmProjection T) := by
  unfold juliaFredholmProjection
  rw [juliaFredholmColumn_transport u v T hT, HilbertModuleEquiv.transportMap_adjoint,
    HilbertModuleEquiv.transportMap_comp]
  rfl

include completeE completeF completeE' completeF' in
/-- The negative reference projection is preserved by each actual block unitary. -/
theorem juliaReferenceProjection_transport (u : HilbertModuleEquiv B E E')
    (v : HilbertModuleEquiv B F F') :
    (u.sum v).transport (juliaReferenceProjection (B := B) (E := E) (F := F)) =
      juliaReferenceProjection (B := B) (E := E') (F := F') := by
  apply (StarAlgEquiv.isometry (u.sum v).symm.transportStarAlgEquiv).injective
  change (u.sum v).symm.transport
      ((u.sum v).transport (juliaReferenceProjection (B := B) (E := E) (F := F))) =
    (u.sum v).symm.transport (juliaReferenceProjection (B := B) (E := E') (F := F'))
  rw [HilbertModuleEquiv.transport_symm]
  apply AdjointableMap.ext
  intro x
  change sumMk (0 : E) x.snd = sumMk (u.symm (0 : E')) (v.symm (v x.snd))
  rw [HilbertModuleEquiv.map_zero, HilbertModuleEquiv.symm_apply_apply]

end BC4lean.KKTheory
