import BC4lean.GradedMatrixMoritaCycle
import BC4lean.GradedKasparovCompactSecondProduct
import BC4lean.GradedKasparovCycleIso

/-! # Genuine graded cycles from compact correspondences

A complete countably generated graded equivariant correspondence with a
compact left action has an actual Kasparov cycle with zero operator. Its
square defect is minus the given compact left action. Tensoring a first
cycle with this correspondence satisfies the full genuine product criterion.
-/

noncomputable section
namespace BC4lean.KKTheory.GradedCompactCorrespondenceCycle

variable {Γ B C F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace F]
  (β : CStarAlgebraAction Γ B) (γ : CStarAlgebraAction Γ C)
  (δB : CStarGrading B) (δC : CStarGrading C)
  (K : GradedHilbertModule δC F) (V : EquivariantHilbertModule γ F)
  (hβ : β.PreservesGrading δB) (hγ : γ.PreservesGrading δC)
  (hV : V.PreservesGrading K)
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
  (hφJ : ModuleTensorRepresentationGraded (δB := δB) φ K)
  (hφU : ModuleTensorRepresentationEquivariant φ β V)
  (hφcompact : ∀ b, IsModuleCompact (φ b)) (hF : IsCountablyGeneratedModule C F)

def cycle : GradedKasparovCycle β γ δB δC F where
  sourceAction_preservesGrading := hβ
  coefficientAction_preservesGrading := hγ
  countablyGenerated := hF
  grading := K
  groupAction := V
  grading_preserved := hV
  representation := φ
  representation_graded := hφJ
  representation_equivariant g b := by
    ext x
    change V.action g (φ b (V.action g⁻¹ x)) = φ (β.automorphism g b) x
    rw [hφU, V.apply_inv_apply]
  operator := 0
  operator_odd x := by
    simp only [AdjointableMap.coe_zero_apply, map_zero, neg_zero]
  selfadjoint_mod_compact b := by
    simpa only [star_zero, sub_self, zero_mul] using
      (IsModuleCompact.zero : IsModuleCompact (0 : AdjointableMap C F F))
  square_mod_compact b := by
    simpa only [zero_mul, zero_sub, neg_one_mul] using (hφcompact b).neg
  commutator_compact b := by
    simpa only [zero_mul, mul_zero, sub_self] using
      (IsModuleCompact.zero : IsModuleCompact (0 : AdjointableMap C F F))
  equivariance_mod_compact g b := by
    have hz : V.conjugateOperator g (0 : AdjointableMap C F F) = 0 := by
      ext x
      change V.action g (0 : F) = 0
      exact map_zero _
    rw [hz, sub_self, zero_mul]
    exact IsModuleCompact.zero

variable {A E : Type*} [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E] {α : CStarAlgebraAction Γ A} {δA : CStarGrading A}
  (c : GradedKasparovCycle α β δA δB E)

/-- The induced first operator has all four connection laws and genuine
localized positive lifts for this actual correspondence cycle. -/
theorem isProduct : IsGradedKasparovProductOperator c
    (cycle β γ δB δC K V hβ hγ hV φ hφJ hφU hφcompact hF)
    (interiorModuleTensorOperator φ c.operator) :=
  isGradedKasparovProductOperator_of_zero_compact_second c
    (cycle β γ δB δC K V hβ hγ hV φ hφJ hφU hφcompact hF) rfl hφcompact

/-- The actual correspondence product cycle is the existing full tensor
cycle construction; proof fields differ only by proof irrelevance. -/
def tensorCycleIso : GradedKasparovCycleIso
    (GradedMatrixMoritaCycle.tensorWithCompactLeftAction c γ δC K V hγ hV
      φ hφJ hφU hφcompact hF)
    (gradedKasparovTensorCycleOfConditions c
      (cycle β γ δB δC K V hβ hγ hV φ hφJ hφU hφcompact hF)
      (interiorModuleTensorOperator φ c.operator)
      (isProduct β γ δB δC K V hβ hγ hV φ hφJ hφU hφcompact hF c).cycleConditions) where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

end BC4lean.KKTheory.GradedCompactCorrespondenceCycle
