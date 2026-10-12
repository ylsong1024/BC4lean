import BC4lean.CliffordPairStandardTensor
import BC4lean.GradedKasparovCompactSecondProduct
import BC4lean.GradedStandardModuleHomCycle
import BC4lean.CliffordParityCycle

/-! # The whole ordinary odd coefficient-extension cycle

The four Fredholm defects of F ⊗ 1 are genuinely compact because the
standard target representation of every f(b) is compact. The completed
Clifford pair tensor unitary identifies the actual graded compact-second
product with the Clifford expansion of this ordinary odd tensor cycle,
including its grading, action, representation and operator.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {B C E : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

local notation "α₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
local notation "β₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B)
local notation "γ₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit C)

/-- Genuine extension on the completed ordinary interior tensor. -/
def OddKasparovCycle.coefficientTensor (c : OddKasparovCycle α₁ β₁ E)
    (f : B →⋆ₙₐ[ℂ] C) :
    OddKasparovCycle α₁ γ₁
      (InteriorModuleTensor (E := E) (standardCoefficientImageRepresentation f)) where
  countablyGenerated := c.countablyGenerated.interiorTensor
    standard_module_isCountablyGenerated (standardCoefficientImageRepresentation f)
  groupAction := EquivariantHilbertModule.trivial
  representation :=
    (interiorModuleTensorOperatorHom (standardCoefficientImageRepresentation f)).toNonUnitalStarAlgHom.comp
      c.representation
  representation_equivariant g a := by
    have hg : g = 1 := Subsingleton.elim _ _
    subst g
    rw [EquivariantHilbertModule.conjugateOperator, EquivariantHilbertModule.conjugateMap_one]
    rfl
  operator := interiorModuleTensorOperator (standardCoefficientImageRepresentation f) c.operator
  selfadjoint_mod_compact a := by
    have h := (c.selfadjoint_mod_compact a).interiorModuleTensorOperator
      (standardCoefficientImageRepresentation f) (fun b => standardLeftMul_mem_moduleCompact (f b))
    change IsModuleCompact ((interiorModuleTensorOperatorHom (standardCoefficientImageRepresentation f))
      ((c.operator - star c.operator) * c.representation a)) at h
    simpa only [NonUnitalStarAlgHom.comp_apply, StarAlgHom.coe_toNonUnitalStarAlgHom,
      map_mul, map_sub, map_star, interiorModuleTensorOperatorHom_apply] using h
  square_mod_compact a := by
    have h := (c.square_mod_compact a).interiorModuleTensorOperator
      (standardCoefficientImageRepresentation f) (fun b => standardLeftMul_mem_moduleCompact (f b))
    change IsModuleCompact ((interiorModuleTensorOperatorHom (standardCoefficientImageRepresentation f))
      ((c.operator * c.operator - 1) * c.representation a)) at h
    simpa only [NonUnitalStarAlgHom.comp_apply, StarAlgHom.coe_toNonUnitalStarAlgHom,
      map_mul, map_sub, map_one, interiorModuleTensorOperatorHom_apply] using h
  commutator_compact a := by
    have h := (c.commutator_compact a).interiorModuleTensorOperator
      (standardCoefficientImageRepresentation f) (fun b => standardLeftMul_mem_moduleCompact (f b))
    change IsModuleCompact ((interiorModuleTensorOperatorHom (standardCoefficientImageRepresentation f))
      (c.operator * c.representation a - c.representation a * c.operator)) at h
    simpa only [NonUnitalStarAlgHom.comp_apply, StarAlgHom.coe_toNonUnitalStarAlgHom,
      map_mul, map_sub, interiorModuleTensorOperatorHom_apply] using h
  equivariance_mod_compact g a := by
    have hg : g = 1 := Subsingleton.elim _ _
    subst g
    rw [EquivariantHilbertModule.conjugateOperator, EquivariantHilbertModule.conjugateMap_one,
      sub_self, zero_mul]
    exact IsModuleCompact.zero

namespace OrdinaryOddCoefficientTensor
open CliffordPairStandardTensor

def coordinateHomCycle (f : B →⋆ₙₐ[ℂ] C) :=
  gradedStandardModuleHomCycle (cliffordCoefficientAction β₁) (cliffordCoefficientAction γ₁)
    cliffordCoefficientGrading cliffordCoefficientGrading
    (cliffordCoefficientAction_preservesGrading β₁) (cliffordCoefficientAction_preservesGrading γ₁)
    (cliffordCoordinateHom f) (fun _ _ => rfl) (fun _ => rfl)

def coordinateProduct (c : OddKasparovCycle α₁ β₁ E) (f : B →⋆ₙₐ[ℂ] C) :=
  gradedKasparovCompactSecondProduct c.cliffordExpansion (coordinateHomCycle f)
    (fun b => standardLeftMul_mem_moduleCompact (cliffordCoordinateHom f b))

/-- Whole-cycle identification, on every completion vector. -/
def coordinateProductIso (c : OddKasparovCycle α₁ β₁ E) (f : B →⋆ₙₐ[ℂ] C) :
    GradedKasparovCycleIso (coordinateProduct c f) (c.coefficientTensor f).cliffordExpansion where
  moduleEquiv := hilbertEquiv f
  grading_intertwine z := by
    let W : Source (H := E) f →L[ℂ] Target (H := E) f :=
      (hilbertEquiv (H := E) f).toAdjointable.toCLM
    let J : Source (H := E) f →L[ℂ] Source (H := E) f :=
      (coordinateProduct c f).grading.grading.toContinuousLinearEquiv.toContinuousLinearMap
    let K : Target (H := E) f →L[ℂ] Target (H := E) f :=
      (cliffordPairGrading (B := C) (H := InteriorModuleTensor (E := E)
        (standardCoefficientImageRepresentation f))).grading.toContinuousLinearEquiv.toContinuousLinearMap
    have hφ : ModuleTensorRepresentationGraded (δB := cliffordCoefficientGrading)
        (representation f) (GradedHilbertModule.standard cliffordCoefficientGrading) := by
      intro b y
      change MulOpposite.op (cliffordCoefficientGrading.automorphism
          (cliffordCoordinateHom f b * MulOpposite.unop y)) =
        MulOpposite.op (cliffordCoordinateHom f (cliffordCoefficientGrading.automorphism b) *
          cliffordCoefficientGrading.automorphism (MulOpposite.unop y))
      rw [map_mul]
      rfl
    have h : W.comp J = K.comp W := by
      apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      intro x y
      change hilbertEquiv f ((c.cliffordExpansion.grading.interiorTensor
        (GradedHilbertModule.standard cliffordCoefficientGrading) hφ).grading
          (interiorModuleTensorMk (representation f) x y)) =
        cliffordPairMk (hilbertEquiv f (interiorModuleTensorMk (representation f) x y)).2
          (hilbertEquiv f (interiorModuleTensorMk (representation f) x y)).1
      rw [GradedHilbertModule.interiorTensor_grading_mk,
        hilbertEquiv_mk, hilbertEquiv_mk]
      rfl
    change W (J z) = K (W z)
    exact DFunLike.congr_fun h z
  action_intertwine g z := by
    have hg : g = 1 := Subsingleton.elim _ _
    subst g
    rw [EquivariantHilbertModule.one_apply, EquivariantHilbertModule.one_apply]
  representation_intertwine a z := by
    change hilbertEquiv f
      (interiorModuleTensorOperator (representation f)
        (cliffordPairMap (c.representation a) (c.representation a)) z) =
      cliffordPairMap
        (interiorModuleTensorOperator (standardCoefficientImageRepresentation f) (c.representation a))
        (interiorModuleTensorOperator (standardCoefficientImageRepresentation f) (c.representation a))
        (hilbertEquiv f z)
    exact hilbertEquiv_operator f (c.representation a) (c.representation a) z
  operator_intertwine z := by
    change hilbertEquiv f
      (interiorModuleTensorOperator (representation f) (cliffordPairMap c.operator (-c.operator)) z) =
      cliffordPairMap
        (interiorModuleTensorOperator (standardCoefficientImageRepresentation f) c.operator)
        (-(interiorModuleTensorOperator (standardCoefficientImageRepresentation f) c.operator))
        (hilbertEquiv f z)
    have h := hilbertEquiv_operator f c.operator (-c.operator) z
    simpa only [← interiorModuleTensorOperatorHom_apply, map_neg] using h

end OrdinaryOddCoefficientTensor
end BC4lean.KKTheory
