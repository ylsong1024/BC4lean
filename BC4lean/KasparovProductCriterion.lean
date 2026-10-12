import BC4lean.KasparovConnection
import BC4lean.GradedEquivariantInteriorModuleTensor
import BC4lean.InteriorModuleTensorCountableGeneration
import BC4lean.EssentialModulePositivity
import BC4lean.KasparovLocalCompactPerturbation

/-! # The exact Kasparov product criterion on the constructed interior tensor

The tensor module, grading, representation and group action are constructed
from the two input cycles. A product operator must satisfy all four genuine
cycle defects, the two homogeneous connection identities and their adjoint
identities, and the localized graded positivity condition for every source
algebra element. Positivity is the concrete positive-lift formulation modulo
the closed module-compact ideal.

The definition does not assume that product operators exist. Its globally
compact perturbation theorem constructs a new admissible product operator
and an actual affine operator homotopy from an existing one. Product existence,
general uniqueness, associativity and descent to KK remain separate theorems.
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

variable (c : KasparovCycle α β E) (d : KasparovCycle β γ F)

/-- The actual tensor grading `J_E ⊗ J_F`. -/
def kasparovTensorGrading :
    GradedHilbertModule (CStarGrading.trivial : CStarGrading C)
      (InteriorModuleTensor (E := E) d.representation) :=
  c.grading.interiorTensor d.grading d.representation_even

/-- The actual tensor action `U_g ⊗ V_g`. -/
def kasparovTensorAction :
    EquivariantHilbertModule γ (InteriorModuleTensor (E := E) d.representation) :=
  c.groupAction.interiorTensor d.groupAction
    (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)

/-- The actual left representation `a ↦ φ(a) ⊗ 1`. -/
def kasparovTensorRepresentation :
    A →⋆ₙₐ[ℂ] AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation) :=
  (interiorModuleTensorOperatorHom d.representation).toNonUnitalStarAlgHom.comp c.representation

@[simp] theorem kasparovTensorRepresentation_apply (a : A) :
    kasparovTensorRepresentation c d a =
      interiorModuleTensorOperator d.representation (c.representation a) := rfl

theorem kasparovTensorRepresentation_even (a : A) :
    (kasparovTensorGrading c d).IsEven (kasparovTensorGrading c d)
      (kasparovTensorRepresentation c d a) :=
  GradedHilbertModule.IsEven.interiorModuleTensorOperator
    (φ := d.representation) (J := c.grading)
    d.grading d.representation_even (c.representation_even a)

theorem kasparovTensorAction_preservesGrading :
    (kasparovTensorAction c d).PreservesGrading (kasparovTensorGrading c d) :=
  c.groupAction.interiorTensor_preservesGrading d.groupAction c.grading d.grading
    c.grading_preserved d.grading_preserved
    (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)
    d.representation_even

theorem kasparovTensorRepresentation_equivariant (g : Γ) (a : A) :
    (kasparovTensorAction c d).conjugateOperator g (kasparovTensorRepresentation c d a) =
      kasparovTensorRepresentation c d (α.automorphism g a) := by
  change (c.groupAction.interiorTensor d.groupAction _).conjugateOperator g
      (interiorModuleTensorOperator d.representation (c.representation a)) = _
  rw [EquivariantHilbertModule.interiorTensor_conjugateOperator,
    c.representation_equivariant]
  rfl

/-- The full operator conditions on the actual tensor module with its
constructed data. This proposition contains no product existence assumption. -/
structure KasparovTensorOperatorConditions
    (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) : Prop where
  operator_odd : (kasparovTensorGrading c d).IsOdd (kasparovTensorGrading c d) R
  selfadjoint_mod_compact : ∀ a,
    IsModuleCompact ((R - star R) * kasparovTensorRepresentation c d a)
  square_mod_compact : ∀ a,
    IsModuleCompact ((R * R - 1) * kasparovTensorRepresentation c d a)
  commutator_compact : ∀ a,
    IsModuleCompact (R * kasparovTensorRepresentation c d a -
      kasparovTensorRepresentation c d a * R)
  equivariance_mod_compact : ∀ g a,
    IsModuleCompact (((kasparovTensorAction c d).conjugateOperator g R - R) *
      kasparovTensorRepresentation c d a)

/-- Construct a genuine tensor cycle once its exact operator conditions are proved. -/
def kasparovTensorCycleOfConditions
    (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation))
    (hR : KasparovTensorOperatorConditions c d R) :
    KasparovCycle α γ (InteriorModuleTensor (E := E) d.representation) where
  countablyGenerated := c.countablyGenerated.interiorTensor d.countablyGenerated d.representation
  grading := kasparovTensorGrading c d
  groupAction := kasparovTensorAction c d
  grading_preserved := kasparovTensorAction_preservesGrading c d
  representation := kasparovTensorRepresentation c d
  representation_even := kasparovTensorRepresentation_even c d
  representation_equivariant := kasparovTensorRepresentation_equivariant c d
  operator := R
  operator_odd := hR.operator_odd
  selfadjoint_mod_compact := hR.selfadjoint_mod_compact
  square_mod_compact := hR.square_mod_compact
  commutator_compact := hR.commutator_compact
  equivariance_mod_compact := hR.equivariance_mod_compact

/-- Localized graded bracket of the two odd operators. Both operators have
odd degree, so the graded bracket is the anticommutator. -/
def kasparovProductPositivityOperator
    (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) (a : A) :
    AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation) :=
  kasparovTensorRepresentation c d a *
    (interiorModuleTensorOperator d.representation c.operator * R +
      R * interiorModuleTensorOperator d.representation c.operator) *
    star (kasparovTensorRepresentation c d a)

/-- The exact analytic criterion for an operator representing the Kasparov
product of the two specified input cycles. -/
structure IsKasparovProductOperator
    (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) : Prop where
  cycleConditions : KasparovTensorOperatorConditions c d R
  connection : KasparovConnection c d R
  positivity : ∀ a, IsPositiveModuloModuleCompact (kasparovProductPositivityOperator c d R a)

namespace KasparovTensorOperatorConditions

variable {c d}

/-- A globally compact odd perturbation satisfies all genuine cycle conditions. -/
theorem add_compact
    {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)}
    (hR : KasparovTensorOperatorConditions c d R)
    (K : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation))
    (hK : IsModuleCompact K)
    (hodd : (kasparovTensorGrading c d).IsOdd (kasparovTensorGrading c d) K) :
    KasparovTensorOperatorConditions c d (R + K) := by
  let q := kasparovTensorCycleOfConditions c d R hR
  have h := q.operatorConditions_add_locallyCompact K hodd
    (fun a => mul_mem_moduleCompact_right hK (q.representation a))
    (fun a => mul_mem_moduleCompact_right hK.adjoint (q.representation a))
  exact ⟨h.operator_odd, h.selfadjoint_mod_compact, h.square_mod_compact,
    h.commutator_compact, h.equivariance_mod_compact⟩

end KasparovTensorOperatorConditions

namespace IsKasparovProductOperator

variable {c d}

/-- Globally compact perturbations preserve the full product criterion,
including every connection adjoint condition and every localized positivity condition. -/
theorem add_compact
    {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)}
    (hR : IsKasparovProductOperator c d R)
    (K : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation))
    (hK : IsModuleCompact K)
    (hodd : (kasparovTensorGrading c d).IsOdd (kasparovTensorGrading c d) K) :
    IsKasparovProductOperator c d (R + K) where
  cycleConditions := hR.cycleConditions.add_compact K hK hodd
  connection := hR.connection.add_compact K hK
  positivity a := by
    apply (hR.positivity a).of_sub_compact
    have heq : kasparovProductPositivityOperator c d (R + K) a -
        kasparovProductPositivityOperator c d R a =
        kasparovTensorRepresentation c d a *
          (interiorModuleTensorOperator d.representation c.operator * K +
            K * interiorModuleTensorOperator d.representation c.operator) *
          star (kasparovTensorRepresentation c d a) := by
      dsimp only [kasparovProductPositivityOperator]
      noncomm_ring
    rw [heq]
    change kasparovTensorRepresentation c d a *
        (interiorModuleTensorOperator d.representation c.operator * K +
          K * interiorModuleTensorOperator d.representation c.operator) *
        star (kasparovTensorRepresentation c d a) ∈
      moduleCompact C (InteriorModuleTensor (E := E) d.representation)
        (InteriorModuleTensor (E := E) d.representation)
    apply mul_mem_moduleCompact_right
    apply mul_mem_moduleCompact_left
    apply (moduleCompact C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)).add_mem
    · exact mul_mem_moduleCompact_left _ hK
    · exact mul_mem_moduleCompact_right hK _

/-- A compact odd perturbation has an actual affine cycle homotopy on the
constructed tensor module. This is the compact-perturbation special case,
not the general uniqueness theorem for product operators. -/
def compactPerturbationHomotopy
    {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)}
    (hR : IsKasparovProductOperator c d R)
    (K : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation))
    (hK : IsModuleCompact K)
    (hodd : (kasparovTensorGrading c d).IsOdd (kasparovTensorGrading c d) K) :
    KasparovOperatorHomotopy (kasparovTensorCycleOfConditions c d R hR.cycleConditions)
      R (R + K) := by
  let q := kasparovTensorCycleOfConditions c d R hR.cycleConditions
  apply KasparovOperatorHomotopy.compactPerturbation q (R + K)
    (q.operatorConditions_add_locallyCompact K hodd
      (fun a => mul_mem_moduleCompact_right hK (q.representation a))
      (fun a => mul_mem_moduleCompact_right hK.adjoint (q.representation a)))
  intro a
  simpa only [q, kasparovTensorCycleOfConditions, add_sub_cancel_left, IsModuleCompact] using
    mul_mem_moduleCompact_right hK (kasparovTensorRepresentation c d a)

end IsKasparovProductOperator
end BC4lean.KKTheory
