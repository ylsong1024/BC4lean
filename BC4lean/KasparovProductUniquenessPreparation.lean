import BC4lean.KasparovProductNormalization

/-! # Actual creation-local defects for comparing product operators

Two genuine connections differ by an element of the closed creation-local
algebra, using both actual adjoint connection laws. Every connection
normalizes this containing algebra on both sides. Consequently comparison
anticommutator defects can be added to the separable technical algebra
without assuming a product homotopy or separability of all endomorphisms.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ A B C E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}

namespace GradedKasparovConnection

variable {c : GradedKasparovCycle α β δA δB E} {d : GradedKasparovCycle β γ δB δC F}
  {R G T : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation)}

/-- Both genuine arbitrary-vector connection defects cancel. This needs
no selfadjointness of either connection or of the second operator. -/
theorem sub_creationLocallyCompact
    (hR : GradedKasparovConnection c d R) (hG : GradedKasparovConnection c d G) :
    IsCreationLocallyCompact d.representation (R - G) := by
  intro x
  constructor
  · have heq : (R - G).comp (moduleCreationMap d.representation x) =
        (R.comp (moduleCreationMap d.representation x) -
          (moduleCreationMap d.representation (c.grading.grading x)).comp d.operator) -
        (G.comp (moduleCreationMap d.representation x) -
          (moduleCreationMap d.representation (c.grading.grading x)).comp d.operator) := by
      ext y
      simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply]
      abel
    rw [heq]
    exact (hR.creation_defect x).sub (hG.creation_defect x)
  · change IsModuleCompact ((star (R - G)).comp (moduleCreationMap d.representation x))
    have heq : (star (R - G)).comp (moduleCreationMap d.representation x) =
        ((star R).comp (moduleCreationMap d.representation x) -
          (moduleCreationMap d.representation (c.grading.grading x)).comp (star d.operator)) -
        ((star G).comp (moduleCreationMap d.representation x) -
          (moduleCreationMap d.representation (c.grading.grading x)).comp (star d.operator)) := by
      rw [star_sub]
      ext y
      simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply]
      abel
    rw [heq]
    exact (hR.creation_adjoint_defect x).sub (hG.creation_adjoint_defect x)

/-- A genuine connection preserves creation-local compactness by left
multiplication. Its adjoint connection law controls the adjoint product. -/
theorem mul_creationLocallyCompact (hG : GradedKasparovConnection c d G)
    (hT : IsCreationLocallyCompact d.representation T) :
    IsCreationLocallyCompact d.representation (G * T) := by
  intro x
  constructor
  · change IsModuleCompact (G.comp (T.comp (moduleCreationMap d.representation x)))
    exact ((hT x).1).comp_left G
  · change IsModuleCompact ((star (G * T)).comp (moduleCreationMap d.representation x))
    have heq : (star (G * T)).comp (moduleCreationMap d.representation x) =
        T.adjoint.comp ((star G).comp (moduleCreationMap d.representation x) -
          (moduleCreationMap d.representation (c.grading.grading x)).comp (star d.operator)) +
        (T.adjoint.comp (moduleCreationMap d.representation (c.grading.grading x))).comp
          (star d.operator) := by
      rw [star_mul]
      ext y
      simp only [AdjointableMap.comp_apply, AdjointableMap.mul_apply,
        AdjointableMap.coe_add_apply, AdjointableMap.coe_sub_apply,
        AdjointableMap.star_eq_adjoint, map_sub]
      abel
    rw [heq]
    exact ((hG.creation_adjoint_defect x).comp_left T.adjoint).add
      (((hT (c.grading.grading x)).2).comp_right (star d.operator))

/-- A genuine connection also preserves the containing algebra by right
multiplication; the actual signed creation law supplies its first part. -/
theorem creationLocallyCompact_mul (hG : GradedKasparovConnection c d G)
    (hT : IsCreationLocallyCompact d.representation T) :
    IsCreationLocallyCompact d.representation (T * G) := by
  intro x
  constructor
  · have heq : (T * G).comp (moduleCreationMap d.representation x) =
        T.comp (G.comp (moduleCreationMap d.representation x) -
          (moduleCreationMap d.representation (c.grading.grading x)).comp d.operator) +
        (T.comp (moduleCreationMap d.representation (c.grading.grading x))).comp d.operator := by
      ext y
      simp only [AdjointableMap.comp_apply, AdjointableMap.mul_apply,
        AdjointableMap.coe_add_apply, AdjointableMap.coe_sub_apply, map_sub]
      abel
    rw [heq]
    exact ((hG.creation_defect x).comp_left T).add
      (((hT (c.grading.grading x)).1).comp_right d.operator)
  · change IsModuleCompact (G.adjoint.comp
      (T.adjoint.comp (moduleCreationMap d.representation x)))
    exact ((hT x).2).comp_left G.adjoint

/-- The comparison anticommutator differs from two by an actual element
of the creation-local algebra. Only the second cycle's localized square
defect is used in the genuine connection square theorem. -/
theorem comparison_anticommutator_creationLocallyCompact
    (hR : GradedKasparovConnection c d R) (hG : GradedKasparovConnection c d G)
    (hGsa : IsSelfAdjoint G) (hdsa : IsSelfAdjoint d.operator) :
    IsCreationLocallyCompact d.representation (R * G + G * R - 2) := by
  have hdiff := hR.sub_creationLocallyCompact hG
  have hsquare := hG.square_creation_locallyCompact hGsa hdsa
  have heq : R * G + G * R - 2 =
      (R - G) * G + G * (R - G) + (G * G - 1) + (G * G - 1) := by
    have htwo : (2 : AdjointableMap C
        (InteriorModuleTensor (E := E) d.representation)
        (InteriorModuleTensor (E := E) d.representation)) = 1 + 1 :=
      one_add_one_eq_two.symm
    rw [htwo]
    noncomm_ring
  rw [heq]
  exact (((hG.creationLocallyCompact_mul hdiff).add
    (hG.mul_creationLocallyCompact hdiff)).add hsquare).add hsquare

end GradedKasparovConnection
end BC4lean.KKTheory
