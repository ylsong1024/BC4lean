import BC4lean.KasparovDescentOperatorDefects

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Actual raw-cycle defects at the concrete covariant generators

This uses the completed balanced group operators from KasparovDescentAction.
The source generator is the actual coefficient representation multiplied by
the actual group unitary. Its three compact defects follow from the source
cycle conditions and the proved operator intertwining law, with no assumed
descended-cycle fields. No completed source representation is declared here.


-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent

variable {Γ A B : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]

variable (β : CStarAlgebraAction Γ B) (E : Type*)
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

variable {α : CStarAlgebraAction Γ A}

theorem even_sourceGenerator_selfadjoint_compact
    (c : KasparovCycle α β E) (a : A) (g : Γ) :
    IsModuleCompact ((operatorHom β E c.operator - star (operatorHom β E c.operator)) *
      sourceGenerator β E c.groupAction c.representation a g) := by
  change IsModuleCompact
    ((operatorHom β E c.operator - star (operatorHom β E c.operator)) *
      (sourceRepresentation β E c.representation a * groupOperator β E c.groupAction g))
  rw [← mul_assoc]
  exact mul_mem_moduleCompact_right (even_coefficient_selfadjoint_compact β c a)
    (groupOperator β E c.groupAction g)

theorem even_sourceGenerator_square_compact
    (c : KasparovCycle α β E) (a : A) (g : Γ) :
    IsModuleCompact ((operatorHom β E c.operator * operatorHom β E c.operator - 1) *
      sourceGenerator β E c.groupAction c.representation a g) := by
  change IsModuleCompact
    ((operatorHom β E c.operator * operatorHom β E c.operator - 1) *
      (sourceRepresentation β E c.representation a * groupOperator β E c.groupAction g))
  rw [← mul_assoc]
  exact mul_mem_moduleCompact_right (even_coefficient_square_compact β c a)
    (groupOperator β E c.groupAction g)

theorem even_sourceGenerator_commutator_compact
    (c : KasparovCycle α β E) (a : A) (g : Γ) :
    IsModuleCompact (operatorHom β E c.operator *
        sourceGenerator β E c.groupAction c.representation a g -
      sourceGenerator β E c.groupAction c.representation a g * operatorHom β E c.operator) := by
  simp only [sourceGenerator_group_first β E α c.groupAction c.representation
    c.representation_equivariant a g]
  exact even_generator_commutator_compact β c g (α.automorphism g⁻¹ a)
    (groupOperator β E c.groupAction g)
    (operatorHom_mul_groupOperator β E c.groupAction g c.operator)

theorem odd_sourceGenerator_selfadjoint_compact
    (c : OddKasparovCycle α β E) (a : A) (g : Γ) :
    IsModuleCompact ((operatorHom β E c.operator - star (operatorHom β E c.operator)) *
      sourceGenerator β E c.groupAction c.representation a g) := by
  change IsModuleCompact
    ((operatorHom β E c.operator - star (operatorHom β E c.operator)) *
      (sourceRepresentation β E c.representation a * groupOperator β E c.groupAction g))
  rw [← mul_assoc]
  exact mul_mem_moduleCompact_right (odd_coefficient_selfadjoint_compact β c a)
    (groupOperator β E c.groupAction g)

theorem odd_sourceGenerator_square_compact
    (c : OddKasparovCycle α β E) (a : A) (g : Γ) :
    IsModuleCompact ((operatorHom β E c.operator * operatorHom β E c.operator - 1) *
      sourceGenerator β E c.groupAction c.representation a g) := by
  change IsModuleCompact
    ((operatorHom β E c.operator * operatorHom β E c.operator - 1) *
      (sourceRepresentation β E c.representation a * groupOperator β E c.groupAction g))
  rw [← mul_assoc]
  exact mul_mem_moduleCompact_right (odd_coefficient_square_compact β c a)
    (groupOperator β E c.groupAction g)

theorem odd_sourceGenerator_commutator_compact
    (c : OddKasparovCycle α β E) (a : A) (g : Γ) :
    IsModuleCompact (operatorHom β E c.operator *
        sourceGenerator β E c.groupAction c.representation a g -
      sourceGenerator β E c.groupAction c.representation a g * operatorHom β E c.operator) := by
  simp only [sourceGenerator_group_first β E α c.groupAction c.representation
    c.representation_equivariant a g]
  exact odd_generator_commutator_compact β c g (α.automorphism g⁻¹ a)
    (groupOperator β E c.groupAction g)
    (operatorHom_mul_groupOperator β E c.groupAction g c.operator)

end BC4lean.KKTheory.KasparovDescent
