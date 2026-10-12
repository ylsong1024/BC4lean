import BC4lean.CliffordPairSecondTensorCompatibility
import BC4lean.CliffordPairFirstCorner
import BC4lean.GradedConnectionDefectAlgebra
import BC4lean.GradedKasparovProductCriterion

/-! # Actual first-corner connections and positivity for even-by-odd tensors

The genuine second-pair unitary carries each creator to its entire
diagonal pair. Actual rectangular coefficient-range restriction then gives
the signed all-vector creator laws on the base tensor. The first operator
has no extra second-factor grading, so localized positive lifts restrict
to the true anticommutator with the original even first operator.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordPairSecondTensor

variable {B C E F : Type*}
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)

@[simp] theorem transport_firstFactor (T : AdjointableMap B E E) :
    (hilbertEquiv (E := E) φ).transport (interiorModuleTensorOperator (representation φ) T) =
      cliffordPairMap (interiorModuleTensorOperator φ T) (interiorModuleTensorOperator φ T) := by
  ext z
  change hilbertEquiv φ (interiorModuleTensorOperator (representation φ) T
    ((hilbertEquiv φ).symm z)) = _
  rw [hilbertEquiv_firstFactor, HilbertModuleEquiv.apply_symm_apply]

@[simp] theorem transport_creation (x : E) :
    (hilbertEquiv (E := E) φ).toAdjointable.comp (moduleCreationMap (representation φ) x) =
      cliffordPairMap (moduleCreationMap φ x) (moduleCreationMap φ x) := by
  ext y
  exact hilbertEquiv_mk φ x y

theorem transport_creation_defect
    (R : AdjointableMap (C × C) (Source (E := E) φ) (Source (E := E) φ))
    (D : AdjointableMap C F F) (x x' : E) :
    (hilbertEquiv φ).toAdjointable.comp
      (R.comp (moduleCreationMap (representation φ) x) -
        (moduleCreationMap (representation φ) x').comp (cliffordPairMap D (-D))) =
    ((hilbertEquiv φ).transport R).comp
      (cliffordPairMap (moduleCreationMap φ x) (moduleCreationMap φ x)) -
    (cliffordPairMap (moduleCreationMap φ x') (moduleCreationMap φ x')).comp
      (cliffordPairMap D (-D)) := by
  ext y
  simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
    HilbertModuleEquiv.toAdjointable_apply, HilbertModuleEquiv.map_sub,
    HilbertModuleEquiv.transport_apply, ← transport_creation φ x,
    ← transport_creation φ x', AdjointableMap.comp_apply,
    HilbertModuleEquiv.toAdjointable_apply, HilbertModuleEquiv.symm_apply_apply]

theorem firstCorner_creation_defect
    (R : AdjointableMap (C × C) (Source (E := E) φ) (Source (E := E) φ))
    (D : AdjointableMap C F F) (x x' : E)
    (h : IsModuleCompact (R.comp (moduleCreationMap (representation φ) x) -
      (moduleCreationMap (representation φ) x').comp (cliffordPairMap D (-D)))) :
    IsModuleCompact ((cliffordPairFirstCorner ((hilbertEquiv φ).transport R)).comp
      (moduleCreationMap φ x) - (moduleCreationMap φ x').comp D) := by
  have ht := h.comp_left (hilbertEquiv φ).toAdjointable
  rw [transport_creation_defect] at ht
  have hc := cliffordPairFirstCorner_isModuleCompact ht
  simpa only [cliffordPairFirstCorner_sub, cliffordPairFirstCorner_comp,
    cliffordPairFirstCorner_pair] using hc

variable {Γ A : Type*} [Group Γ] [NonUnitalCStarAlgebra A]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  (c : GradedKasparovCycle α β CStarGrading.trivial CStarGrading.trivial E)
  (d : OddKasparovCycle β γ F)
  (R : AdjointableMap (C × C) (Source (E := E) d.representation)
    (Source (E := E) d.representation))
  (hR : IsGradedKasparovProductOperator c d.cliffordExpansion R)

include hR in
theorem extracted_creation_defect (x : E) :
    IsModuleCompact ((cliffordPairFirstCorner ((hilbertEquiv d.representation).transport R)).comp
      (moduleCreationMap d.representation x) -
    (moduleCreationMap d.representation (c.grading.grading x)).comp d.operator) :=
  firstCorner_creation_defect d.representation R d.operator x (c.grading.grading x)
    (hR.connection.creation_defect x)

include hR in
theorem extracted_adjoint_creation_defect (x : E) :
    IsModuleCompact ((star (cliffordPairFirstCorner ((hilbertEquiv d.representation).transport R))).comp
      (moduleCreationMap d.representation x) -
    (moduleCreationMap d.representation (c.grading.grading x)).comp (star d.operator)) := by
  have hc := hR.connection.creation_adjoint_defect x
  change IsModuleCompact ((star R).comp
    (moduleCreationMap (B := B) (C := C × C) (E := E) (F := CliffordPairModule C F)
      (representation d.representation) x) -
    (moduleCreationMap (B := B) (C := C × C) (E := E) (F := CliffordPairModule C F)
      (representation d.representation) (c.grading.grading x)).comp
      (star (cliffordPairMap d.operator (-d.operator)))) at hc
  rw [← cliffordPairMap_star, star_neg] at hc
  simpa only [HilbertModuleEquiv.transport_star, cliffordPairFirstCorner_star] using
    firstCorner_creation_defect d.representation (star R) (star d.operator)
      x (c.grading.grading x) hc

include hR in
theorem extracted_positivity (a : A) :
    let p := interiorModuleTensorOperator d.representation (c.representation a)
    let A := interiorModuleTensorOperator d.representation c.operator
    let G := cliffordPairFirstCorner ((hilbertEquiv d.representation).transport R)
    IsPositiveModuloModuleCompact (p * (A * G + G * A) * star p) := by
  have ht := (hR.positivity a).transport (hilbertEquiv d.representation)
  have hc := ht.cliffordPairFirstCorner
  change IsPositiveModuloModuleCompact (cliffordPairFirstCornerHom
    ((hilbertEquiv d.representation).transport
      (interiorModuleTensorOperator (E := E) (F := CliffordPairModule C F)
          (representation d.representation) (c.representation a) *
        (interiorModuleTensorOperator (E := E) (F := CliffordPairModule C F)
            (representation d.representation) c.operator * R +
          R * interiorModuleTensorOperator (E := E) (F := CliffordPairModule C F)
            (representation d.representation) c.operator) *
        star (interiorModuleTensorOperator (E := E) (F := CliffordPairModule C F)
          (representation d.representation) (c.representation a))))) at hc
  simp only [HilbertModuleEquiv.transport_mul, HilbertModuleEquiv.transport_add,
    HilbertModuleEquiv.transport_star, transport_firstFactor] at hc
  simpa only [map_mul, map_add, map_star, cliffordPairFirstCornerHom_apply,
    cliffordPairFirstCorner_pair] using hc

end BC4lean.KKTheory.CliffordPairSecondTensor
