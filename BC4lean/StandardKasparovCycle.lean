import BC4lean.KasparovCycle
import BC4lean.StandardModuleOperator
import BC4lean.StandardHilbertModuleActions

/-! # The standard identity-cycle data

For a separable possibly nonunital Γ-C⋆-algebra B, the standard right Hilbert
module B_B with even grading, left-multiplication representation and F = 0 is
an even equivariant Kasparov cycle. Compactness of the representation is proved
by the full identification K(B_B) = B, rather than being an assumed hypothesis.
Its future class is the usual candidate for the KK identity; this file does not
claim the product unit laws before a Kasparov product has been constructed.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ B : Type*} [Group Γ] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]

/-- The genuine standard even Kasparov cycle representing the identity data. -/
def standardIdentityCycle (β : CStarAlgebraAction Γ B) : KasparovCycle β β Bᵐᵒᵖ where
  countablyGenerated := standard_module_isCountablyGenerated
  grading := GradedHilbertModule.standard CStarGrading.trivial
  groupAction := EquivariantHilbertModule.standard β
  grading_preserved := EquivariantHilbertModule.standard_preservesGrading β CStarGrading.trivial
    (CStarAlgebraAction.preservesGrading_trivial β)
  representation := standardLeftMul
  representation_even := by
    intro a x
    simp
  representation_equivariant := by
    intro g a
    ext x
    change MulOpposite.op (β.automorphism g
      (a * β.automorphism g⁻¹ (MulOpposite.unop x))) =
        MulOpposite.op (β.automorphism g a * MulOpposite.unop x)
    simp only [map_mul, CStarAlgebraAction.apply_inv_apply]
  operator := 0
  operator_odd := by
    intro x
    simp
  selfadjoint_mod_compact := by
    intro a
    simpa using IsModuleCompact.zero (B := B) (E := Bᵐᵒᵖ) (F := Bᵐᵒᵖ)
  square_mod_compact := by
    intro a
    simpa using (IsModuleCompact.neg (T := standardLeftMul a)
      (standardLeftMul_mem_moduleCompact a))
  commutator_compact := by
    intro a
    simpa using IsModuleCompact.zero (B := B) (E := Bᵐᵒᵖ) (F := Bᵐᵒᵖ)
  equivariance_mod_compact := by
    intro g a
    have hzero : (EquivariantHilbertModule.standard β).conjugateOperator g
        (0 : AdjointableMap B Bᵐᵒᵖ Bᵐᵒᵖ) = 0 :=
      EquivariantHilbertModule.conjugateOperator_zero
        (EquivariantHilbertModule.standard β) g
    rw [hzero]
    simpa using IsModuleCompact.zero (B := B) (E := Bᵐᵒᵖ) (F := Bᵐᵒᵖ)

@[simp] theorem standardIdentityCycle_operator (β : CStarAlgebraAction Γ B) :
    (standardIdentityCycle β).operator = 0 := rfl

@[simp] theorem standardIdentityCycle_representation (β : CStarAlgebraAction Γ B) (b : B) :
    (standardIdentityCycle β).representation b = standardLeftMul b := rfl

end BC4lean.KKTheory
