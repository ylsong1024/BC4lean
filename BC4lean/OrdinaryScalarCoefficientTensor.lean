import BC4lean.StandardCoefficientImageTensor
import BC4lean.GradedEquivariantInteriorModuleTensor
import BC4lean.InteriorModuleTensorCountableGeneration
import BC4lean.ModuleTensorCompact
import BC4lean.KasparovCycle

/-! # Actual ordinary scalar coefficient extension

The genuine completed tensor carries the original grading tensored with the
trivial standard target grading. The original representation and operator
act through the true first-factor operator homomorphism. Every compact
defect remains compact because each represented f(b) is an actual compact
standard-module multiplier. Coefficient and carrier universes are independent.
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

def KasparovCycle.scalarCoefficientTensor (c : KasparovCycle α₁ β₁ E)
    (f : B →⋆ₙₐ[ℂ] C) :
    KasparovCycle α₁ γ₁
      (InteriorModuleTensor (E := E) (standardCoefficientImageRepresentation f)) where
  countablyGenerated := c.countablyGenerated.interiorTensor
    standard_module_isCountablyGenerated (standardCoefficientImageRepresentation f)
  grading := c.grading.interiorTensor GradedHilbertModule.trivial (fun _ _ => rfl)
  groupAction := EquivariantHilbertModule.trivial
  grading_preserved _ _ := rfl
  representation :=
    (interiorModuleTensorOperatorHom (standardCoefficientImageRepresentation f)).toNonUnitalStarAlgHom.comp
      c.representation
  representation_even a := (c.representation_even a).interiorModuleTensorOperator
    GradedHilbertModule.trivial (fun _ _ => rfl)
  representation_equivariant g a := by
    have hg : g = 1 := Subsingleton.elim _ _
    subst g
    rw [EquivariantHilbertModule.conjugateOperator, EquivariantHilbertModule.conjugateMap_one]
    rfl
  operator := interiorModuleTensorOperator (standardCoefficientImageRepresentation f) c.operator
  operator_odd := c.operator_odd.interiorModuleTensorOperator
    GradedHilbertModule.trivial (fun _ _ => rfl)
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

end BC4lean.KKTheory
