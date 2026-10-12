import BC4lean.CompactFirstModuleConnection
import BC4lean.KasparovTechnicalProductApplication

/-! # Genuine weighted third connections from a technical partition

The first weight is compact on each actual creation range by the partition's
first ideal. The square partition makes the second weight minus one compact
on the same range. Compact weight commutators then preserve the signed
connection of a weighted first operator and an actual connection. Its
independent adjoint law follows from the actual global selfadjointness error
and the selfadjoint second operator. No product or homotopy is assumed.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B C E F : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  {δB : CStarGrading B}
  (J : GradedHilbertModule δB E) (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)

local instance standardSignedConnectionWeightedPartitionLocalInstance01 : PartialOrder (AdjointableMap C (InteriorModuleTensor (E := E) φ)
    (InteriorModuleTensor (E := E) φ)) := CStarAlgebra.spectralOrder _
local instance standardSignedConnectionWeightedPartitionLocalInstance02 : StarOrderedRing (AdjointableMap C (InteriorModuleTensor (E := E) φ)
    (InteriorModuleTensor (E := E) φ)) := CStarAlgebra.spectralOrderedRing _

theorem weighted_partition_isSignedModuleConnection
    (S : AdjointableMap C F F)
    (O R m n : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ))
    (hR : IsSignedModuleConnection J φ S R) (hSsa : IsSelfAdjoint S)
    (hOsa : IsSelfAdjoint O) (hRsa : IsSelfAdjoint R)
    (hmsa : IsSelfAdjoint m) (hn : 0 ≤ n) (hpart : m * m + n * n = 1)
    (hmO : IsModuleCompact (m * O - O * m))
    (hnR : IsModuleCompact (n * R - R * n))
    (hmcreation : ∀ x : E, IsModuleCompact (m.comp (moduleCreationMap φ x))) :
    IsSignedModuleConnection J φ S (m * O + n * R) := by
  let P := m * O + n * R
  have hcreation (x : E) : IsModuleCompact (P.comp (moduleCreationMap φ x) -
      (moduleCreationMap φ (J.grading x)).comp S) := by
    have hfirst := ((hmcreation x).comp_left O).add
      (hmO.comp_right (moduleCreationMap φ x))
    have hsecond := (hR.creation x).comp_left n
    have hthird := (shiftedWeight_creation_isModuleCompact φ m n hn hpart (J.grading x)
      (hmcreation (J.grading x))).comp_right S
    have h := (hfirst.add hsecond).add hthird
    convert h using 1
    apply AdjointableMap.ext
    intro y
    simp only [P, AdjointableMap.comp_apply, AdjointableMap.mul_apply,
      AdjointableMap.coe_add_apply, AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, map_sub]
    abel
  have hPstar : IsModuleCompact (star P - P) := by
    have heq : star P - P = -((m * O - O * m) + (n * R - R * n)) := by
      dsimp only [P]
      rw [star_add, star_mul, star_mul, hOsa.star_eq, hRsa.star_eq,
        hmsa.star_eq, hn.isSelfAdjoint.star_eq]
      noncomm_ring
    rw [heq]
    exact (hmO.add hnR).neg
  constructor
  · exact hcreation
  · intro x
    have h := (hcreation x).add (hPstar.comp_right (moduleCreationMap φ x))
    rw [hSsa.star_eq]
    convert h using 1
    apply AdjointableMap.ext
    intro y
    simp only [AdjointableMap.comp_apply, AdjointableMap.coe_add_apply,
      AdjointableMap.coe_sub_apply]
    abel

end BC4lean.KKTheory
