import BC4lean.GradedKasparovConnectionExistence
import BC4lean.ModuleCreationLocalCompact
import BC4lean.EquivariantCompactOperator

/-! # Genuine connection defects in the creation-local compact algebra

The four homogeneous connection laws give the exact compact creation
defect for every module vector by its actual even/odd decomposition.
For an actual selfadjoint connection to a selfadjoint second operator,
the square defect, source graded commutators and first-factor graded
anticommutator lie in the concrete creation-local compact algebra.
The second square calculation uses only localized cycle defects and the
proved coefficient approximate unit, never a global Fredholm defect.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace

section HomogeneousCreation

variable {B C E F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F] {δB : CStarGrading B}

/-- Homogeneous compact connection laws imply the true signed connection
identity on every vector, using the actual semilinear module grading. -/
theorem creationConnection_compact_of_homogeneous
    (J : GradedHilbertModule δB E) (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (S : AdjointableMap C F F)
    (R : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ))
    (heven : ∀ x : E, J.grading x = x →
      IsModuleCompact ((moduleCreationMap φ x).comp S - R.comp (moduleCreationMap φ x)))
    (hodd : ∀ x : E, J.grading x = -x →
      IsModuleCompact ((moduleCreationMap φ x).comp S + R.comp (moduleCreationMap φ x)))
    (x : E) :
    IsModuleCompact (R.comp (moduleCreationMap φ x) -
      (moduleCreationMap φ (J.grading x)).comp S) := by
  let V := moduleCreationContinuousLinearMap (E := E) φ
  let L : E →L[ℂ] AdjointableMap C F (InteriorModuleTensor (E := E) φ) :=
    (AdjointableMap.compLeftContinuousLinearMap R).comp V -
      (AdjointableMap.compRightContinuousLinearMap S).comp
        (V.comp J.grading.toContinuousLinearEquiv.toContinuousLinearMap)
  have he : IsModuleCompact (L (J.evenPart x)) := by
    change IsModuleCompact (R.comp (moduleCreationMap φ (J.evenPart x)) -
      (moduleCreationMap φ (J.grading (J.evenPart x))).comp S)
    rw [J.grading_evenPart]
    simpa only [neg_sub] using (heven _ (J.grading_evenPart x)).neg
  have ho : IsModuleCompact (L (J.oddPart x)) := by
    change IsModuleCompact (R.comp (moduleCreationMap φ (J.oddPart x)) -
      (moduleCreationMap φ (J.grading (J.oddPart x))).comp S)
    rw [J.grading_oddPart, moduleCreationMap_neg]
    have heq : R.comp (moduleCreationMap φ (J.oddPart x)) -
        (-moduleCreationMap φ (J.oddPart x)).comp S =
        (moduleCreationMap φ (J.oddPart x)).comp S +
          R.comp (moduleCreationMap φ (J.oddPart x)) := by
      ext y
      simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
        AdjointableMap.coe_add_apply, AdjointableMap.coe_neg_apply]
      abel
    rw [heq]
    exact hodd _ (J.grading_oddPart x)
  have h := he.add ho
  rw [← map_add, J.evenPart_add_oddPart] at h
  exact h

theorem tensorOperator_creation_apply
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (T : AdjointableMap B E E) (x : E) (y : F) :
    interiorModuleTensorOperator φ T (moduleCreationMap φ x y) =
      moduleCreationMap φ (T x) y :=
  congrArg (fun R => R y) (moduleCreationMap_tensorOperator φ T x)

/-- An actual odd first-factor operator has a compact anticommutator
on every creation range whenever the genuine signed connection defects
are compact. No first-operator selfadjointness is required. -/
theorem oddTensorAnticommutator_comp_creation
    (J : GradedHilbertModule δB E) (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (S : AdjointableMap C F F)
    (G : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ))
    (hD : ∀ x, IsModuleCompact (G.comp (moduleCreationMap φ x) -
      (moduleCreationMap φ (J.grading x)).comp S))
    (T : AdjointableMap B E E) (hT : J.IsOdd J T) (x : E) :
    IsModuleCompact ((interiorModuleTensorOperator φ T * G +
      G * interiorModuleTensorOperator φ T).comp (moduleCreationMap φ x)) := by
  let D := fun y : E => G.comp (moduleCreationMap φ y) -
    (moduleCreationMap φ (J.grading y)).comp S
  have heq : (interiorModuleTensorOperator φ T * G +
      G * interiorModuleTensorOperator φ T).comp (moduleCreationMap φ x) =
      (interiorModuleTensorOperator φ T).comp (D x) + D (T x) := by
    ext y
    simp only [D, AdjointableMap.comp_apply, AdjointableMap.coe_add_apply,
      AdjointableMap.coe_sub_apply, AdjointableMap.mul_apply, map_sub,
      tensorOperator_creation_apply, hT x, moduleCreationMap_neg,
      AdjointableMap.coe_neg_apply]
    abel
  rw [heq]
  exact ((hD x).comp_left _).add (hD (T x))

end HomogeneousCreation

section EquivariantCreation

variable {Γ B C E F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

/-- The actual group action transports a creation map by transporting its
first vector. The source and target actions are retained separately. -/
theorem conjugateMap_moduleCreationMap
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (U : EquivariantHilbertModule β E) (V : EquivariantHilbertModule γ F)
    (hφ : ModuleTensorRepresentationEquivariant φ β V) (g : Γ) (x : E) :
    V.conjugateMap (U.interiorTensor V hφ) g (moduleCreationMap φ x) =
      moduleCreationMap φ (U.action g x) := by
  have hMk (a : E) (b : F) :
      moduleCreationMap φ a b = interiorModuleTensorMk φ a b := rfl
  ext y
  simp only [EquivariantHilbertModule.conjugateMap_apply, hMk,
    EquivariantHilbertModule.interiorTensor_action_mk, V.apply_inv_apply]

end EquivariantCreation

section CycleDefects

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
  {G : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation)} (hG : GradedKasparovConnection c d G)

include hG

/-- The exact compact signed creation defect for an arbitrary vector. -/
theorem creation_defect (x : E) :
    IsModuleCompact (G.comp (moduleCreationMap d.representation x) -
      (moduleCreationMap d.representation (c.grading.grading x)).comp d.operator) :=
  creationConnection_compact_of_homogeneous c.grading d.representation d.operator G
    hG.even hG.odd x

/-- The arbitrary-vector adjoint connection law is likewise derived from
both actual homogeneous adjoint laws. -/
theorem creation_adjoint_defect (x : E) :
    IsModuleCompact ((star G).comp (moduleCreationMap d.representation x) -
      (moduleCreationMap d.representation (c.grading.grading x)).comp (star d.operator)) :=
  creationConnection_compact_of_homogeneous c.grading d.representation (star d.operator) (star G)
    hG.even_adjoint hG.odd_adjoint x

/-- The actual connection square is creation-locally compact modulo one.
Only the localized square defect of the second cycle is used. -/
theorem square_creation_locallyCompact (hGsa : IsSelfAdjoint G)
    (hdsa : IsSelfAdjoint d.operator) :
    IsCreationLocallyCompact d.representation (G * G - 1) := by
  have hSstar : star (d.operator * d.operator - 1) = d.operator * d.operator - 1 := by
    simp only [star_sub, star_mul, star_one, hdsa.star_eq]
  have hRsa : IsSelfAdjoint (G * G - 1) := by
    change star (G * G - 1) = G * G - 1
    simp only [star_sub, star_mul, star_one, hGsa.star_eq]
  apply IsCreationLocallyCompact.of_selfadjoint hRsa
  intro x
  let D := fun y : E => G.comp (moduleCreationMap d.representation y) -
    (moduleCreationMap d.representation (c.grading.grading y)).comp d.operator
  have heq : (G * G - 1).comp (moduleCreationMap d.representation x) =
      G.comp (D x) + (D (c.grading.grading x)).comp d.operator +
        (moduleCreationMap d.representation x).comp (d.operator * d.operator - 1) := by
    ext y
    simp only [D, AdjointableMap.comp_apply, AdjointableMap.coe_add_apply,
      AdjointableMap.coe_sub_apply, AdjointableMap.mul_apply, AdjointableMap.one_apply,
      c.grading.grading_sq, map_sub]
    abel
  rw [heq]
  exact (((hG.creation_defect x).comp_left G).add
    ((hG.creation_defect (c.grading.grading x)).comp_right d.operator)).add
      (moduleCreationMap_comp_isModuleCompact_of_local d.representation x
        (d.operator * d.operator - 1) d.square_mod_compact
          (fun b => by simpa only [hSstar] using d.square_mod_compact b))

/-- Oddness of the genuine first-factor operator makes its actual
anticommutator with the connection compact on every creation range. -/
theorem first_anticommutator_comp_creation (x : E) :
    IsModuleCompact ((interiorModuleTensorOperator d.representation c.operator * G +
      G * interiorModuleTensorOperator d.representation c.operator).comp
        (moduleCreationMap d.representation x)) := by
  exact oddTensorAnticommutator_comp_creation c.grading d.representation d.operator G
    hG.creation_defect c.operator c.operator_odd x

/-- The anticommutator lies in the genuine closed creation-local algebra
when the two actual odd operators are selfadjoint. -/
theorem first_anticommutator_creation_locallyCompact (hcsa : IsSelfAdjoint c.operator)
    (hGsa : IsSelfAdjoint G) :
    IsCreationLocallyCompact d.representation
      (interiorModuleTensorOperator d.representation c.operator * G +
        G * interiorModuleTensorOperator d.representation c.operator) := by
  have hTsa : IsSelfAdjoint (interiorModuleTensorOperator d.representation c.operator) := by
    change star (interiorModuleTensorOperatorHom d.representation c.operator) = _
    rw [← map_star, hcsa.star_eq]
    rfl
  apply IsCreationLocallyCompact.of_selfadjoint
  · change star (_ + _) = _
    simp only [star_add, star_mul, hTsa.star_eq, hGsa.star_eq]
    exact add_comm _ _
  · exact hG.first_anticommutator_comp_creation

/-- Selfadjointness of the connection suffices for creation-locality
of the first anticommutator. Its adjoint uses the genuine oddness of the
first adjoint operator, so the first cycle may be unnormalized. -/
theorem first_anticommutator_creation_locallyCompact_of_selfadjoint_connection
    (hGsa : IsSelfAdjoint G) :
    IsCreationLocallyCompact d.representation
      (interiorModuleTensorOperator d.representation c.operator * G +
        G * interiorModuleTensorOperator d.representation c.operator) := by
  intro x
  refine ⟨hG.first_anticommutator_comp_creation x, ?_⟩
  have heq : (interiorModuleTensorOperator d.representation c.operator * G +
      G * interiorModuleTensorOperator d.representation c.operator).adjoint =
      interiorModuleTensorOperator d.representation c.operator.adjoint * G +
        G * interiorModuleTensorOperator d.representation c.operator.adjoint := by
    change star (_ + _) = _
    simp only [star_add, star_mul, AdjointableMap.star_eq_adjoint,
      interiorModuleTensorOperator_adjoint, show G.adjoint = G from hGsa.star_eq]
    exact add_comm _ _
  rw [heq]
  exact oddTensorAnticommutator_comp_creation c.grading d.representation d.operator G
    hG.creation_defect c.operator.adjoint c.operator_odd.adjoint x

/-- The actual source graded commutator is compact on every creation
range, directly from the genuine representation grading identity. -/
theorem source_commutator_comp_creation (a : A) (x : E) :
    IsModuleCompact ((G * interiorModuleTensorOperator d.representation (c.representation a) -
      interiorModuleTensorOperator d.representation (c.representation (δA.automorphism a)) * G).comp
        (moduleCreationMap d.representation x)) := by
  let D := fun y : E => G.comp (moduleCreationMap d.representation y) -
    (moduleCreationMap d.representation (c.grading.grading y)).comp d.operator
  let Q := interiorModuleTensorOperator d.representation (c.representation (δA.automorphism a))
  have heq : (G * interiorModuleTensorOperator d.representation (c.representation a) - Q * G).comp
      (moduleCreationMap d.representation x) = D (c.representation a x) - Q.comp (D x) := by
    ext y
    simp only [D, Q, AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
      AdjointableMap.mul_apply, map_sub, tensorOperator_creation_apply,
      c.representation_graded]
    abel
  rw [heq]
  exact (hG.creation_defect (c.representation a x)).sub ((hG.creation_defect x).comp_left Q)

/-- Taking the companion commutator at the actual graded star element
proves the adjoint condition, rather than assuming it. -/
theorem source_commutator_creation_locallyCompact (hGsa : IsSelfAdjoint G) (a : A) :
    IsCreationLocallyCompact d.representation
      (G * interiorModuleTensorOperator d.representation (c.representation a) -
        interiorModuleTensorOperator d.representation (c.representation (δA.automorphism a)) * G) := by
  intro x
  refine ⟨hG.source_commutator_comp_creation a x, ?_⟩
  let ρ := (interiorModuleTensorOperatorHom d.representation).toNonUnitalStarAlgHom.comp c.representation
  have heq : (G * ρ a - ρ (δA.automorphism a) * G).adjoint =
      -(G * ρ (δA.automorphism (star a)) - ρ (star a) * G) := by
    change star (G * ρ a - ρ (δA.automorphism a) * G) = _
    simp only [star_sub, star_mul, hGsa.star_eq, ← map_star ρ,
      ← map_star δA.automorphism, neg_sub]
  change IsModuleCompact ((G * ρ a - ρ (δA.automorphism a) * G).adjoint.comp
    (moduleCreationMap d.representation x))
  rw [heq]
  let L := AdjointableMap.compRightContinuousLinearMap
    (G := InteriorModuleTensor (E := E) d.representation) (moduleCreationMap d.representation x)
  change IsModuleCompact (L (-(G * ρ (δA.automorphism (star a)) - ρ (star a) * G)))
  rw [map_neg]
  have h := (hG.source_commutator_comp_creation (δA.automorphism (star a)) x).neg
  change IsModuleCompact (-((G * interiorModuleTensorOperator d.representation
    (c.representation (δA.automorphism (star a))) -
      interiorModuleTensorOperator d.representation (c.representation (star a)) * G).comp
        (moduleCreationMap d.representation x)))
  simpa only [CStarGrading.automorphism_sq] using h

/-- Transporting the genuine signed connection identity proves the group
defect compact on every creation range. Only localized equivariance of
the second cycle is needed. -/
theorem action_defect_comp_creation (hdsa : IsSelfAdjoint d.operator)
    (g : Γ) (x : E) :
    IsModuleCompact (((c.groupAction.interiorTensor d.groupAction
      (d.groupAction.representationEquivariant_of_conjugate
        d.representation_equivariant)).conjugateOperator g G - G).comp
          (moduleCreationMap d.representation x)) := by
  have hMk (a : E) (b : F) :
      moduleCreationMap d.representation a b =
        interiorModuleTensorMk d.representation a b := rfl
  let U := c.groupAction.interiorTensor d.groupAction
    (d.groupAction.representationEquivariant_of_conjugate d.representation_equivariant)
  let D := fun y : E => G.comp (moduleCreationMap d.representation y) -
    (moduleCreationMap d.representation (c.grading.grading y)).comp d.operator
  let Sg := d.groupAction.conjugateOperator g d.operator - d.operator
  have hSgsa : IsSelfAdjoint Sg := by
    change star (d.groupAction.conjugateOperator g d.operator - d.operator) = _
    simp only [star_sub, AdjointableMap.star_eq_adjoint,
      EquivariantHilbertModule.conjugateMap_adjoint]
    change d.groupAction.conjugateOperator g (star d.operator) - star d.operator = _
    rw [hdsa.star_eq]
  have hSg : IsModuleCompact
      ((moduleCreationMap d.representation (c.grading.grading x)).comp Sg) :=
    moduleCreationMap_comp_isModuleCompact_of_local d.representation _ Sg
      (d.equivariance_mod_compact g)
      (fun b => by simpa only [← AdjointableMap.star_eq_adjoint, hSgsa.star_eq]
        using d.equivariance_mod_compact g b)
  have heq : (U.conjugateOperator g G - G).comp (moduleCreationMap d.representation x) =
      d.groupAction.conjugateMap U g (D (c.groupAction.action g⁻¹ x)) +
        (moduleCreationMap d.representation (c.grading.grading x)).comp Sg - D x := by
    ext y
    simp only [U, D, Sg, EquivariantHilbertModule.conjugateMap_apply,
      AdjointableMap.comp_apply, AdjointableMap.coe_add_apply,
      AdjointableMap.coe_sub_apply, hMk, map_sub,
      EquivariantHilbertModule.interiorTensor_action_mk,
      c.grading_preserved g (c.groupAction.action g⁻¹ x), c.groupAction.apply_inv_apply]
    abel
  rw [heq]
  exact (((hG.creation_defect (c.groupAction.action g⁻¹ x)).conjugateMap
    d.groupAction U g).add hSg).sub (hG.creation_defect x)

/-- A selfadjoint genuine connection has an actual creation-local group
defect, including its adjoint companion. -/
theorem action_defect_creation_locallyCompact (hGsa : IsSelfAdjoint G)
    (hdsa : IsSelfAdjoint d.operator) (g : Γ) :
    IsCreationLocallyCompact d.representation
      ((c.groupAction.interiorTensor d.groupAction
        (d.groupAction.representationEquivariant_of_conjugate
          d.representation_equivariant)).conjugateOperator g G - G) := by
  apply IsCreationLocallyCompact.of_selfadjoint
  · change star (_ - G) = _
    simp only [star_sub, AdjointableMap.star_eq_adjoint,
      EquivariantHilbertModule.conjugateMap_adjoint]
    change (c.groupAction.interiorTensor d.groupAction _).conjugateOperator g (star G) -
      star G = _
    rw [hGsa.star_eq]
  · exact hG.action_defect_comp_creation hdsa g

end GradedKasparovConnection
end CycleDefects
end BC4lean.KKTheory
