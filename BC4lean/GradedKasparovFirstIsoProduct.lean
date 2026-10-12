import BC4lean.GradedKasparovTensorCycleTransport
import BC4lean.EssentialModulePositivityFibre
import BC4lean.InteriorModuleTensorFirstFactorEquiv

/-! # Transport of a genuine product through a first-cycle isomorphism

The actual tensor unitary sends x tensor y to u(x) tensor y. All four
rectangular connection defects are transported using this unitary and
the identity on the second module. Homogeneous test vectors are pulled
back by the genuine grading intertwining. The localized positivity
operator is conjugated using both the representation and original
first Fredholm operator intertwinings.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {Γ A B C E E' F : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [SMul Bᵐᵒᵖ E'] [CStarModule Bᵐᵒᵖ E']
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C}
  {δA : CStarGrading A} {δB : CStarGrading B} {δC : CStarGrading C}

variable (c : GradedKasparovCycle α β δA δB E)
  (c' : GradedKasparovCycle α β δA δB E')
  (d : GradedKasparovCycle β γ δB δC F) (e : GradedKasparovCycleIso c c')

def gradedKasparovFirstIsoTensorEquiv : HilbertModuleEquiv C
    (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E') d.representation) :=
  InteriorModuleTensorFirstFactorEquiv.hilbertEquiv d.representation e.moduleEquiv

@[simp] theorem gradedKasparovFirstIsoTensorEquiv_mk (x : E) (y : F) :
    gradedKasparovFirstIsoTensorEquiv c c' d e
      (interiorModuleTensorMk d.representation x y) =
        interiorModuleTensorMk d.representation (e.moduleEquiv x) y :=
  InteriorModuleTensorFirstFactorEquiv.hilbertEquiv_mk _ _ x y

theorem gradedKasparovFirstIsoTensorEquiv_grading
    (z : InteriorModuleTensor (E := E) d.representation) :
    gradedKasparovFirstIsoTensorEquiv c c' d e
      ((gradedKasparovTensorGrading c d).grading z) =
        (gradedKasparovTensorGrading c' d).grading
          (gradedKasparovFirstIsoTensorEquiv c c' d e z) := by
  let L := (gradedKasparovFirstIsoTensorEquiv c c' d e).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have h : L.comp (gradedKasparovTensorGrading c d).grading.toContinuousLinearEquiv.toContinuousLinearMap =
      (gradedKasparovTensorGrading c' d).grading.toContinuousLinearEquiv.toContinuousLinearMap.comp L := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change gradedKasparovFirstIsoTensorEquiv c c' d e
        ((gradedKasparovTensorGrading c d).grading
          (interiorModuleTensorMk d.representation x y)) =
      (gradedKasparovTensorGrading c' d).grading
        (gradedKasparovFirstIsoTensorEquiv c c' d e
          (interiorModuleTensorMk d.representation x y))
    change gradedKasparovFirstIsoTensorEquiv c c' d e
        ((c.grading.interiorTensor d.grading d.representation_graded).grading
          (interiorModuleTensorMk d.representation x y)) =
      (c'.grading.interiorTensor d.grading d.representation_graded).grading
        (gradedKasparovFirstIsoTensorEquiv c c' d e
          (interiorModuleTensorMk d.representation x y))
    rw [GradedHilbertModule.interiorTensor_grading_mk
      (φ := d.representation) c.grading d.grading d.representation_graded x y]
    rw [gradedKasparovFirstIsoTensorEquiv_mk, gradedKasparovFirstIsoTensorEquiv_mk]
    rw [GradedHilbertModule.interiorTensor_grading_mk
      (φ := d.representation) c'.grading d.grading d.representation_graded
      (e.moduleEquiv x) y]
    rw [e.grading_intertwine]
  exact DFunLike.congr_fun h z

theorem gradedKasparovFirstIsoTensorEquiv_action (g : Γ)
    (z : InteriorModuleTensor (E := E) d.representation) :
    gradedKasparovFirstIsoTensorEquiv c c' d e
      ((gradedKasparovTensorAction c d).action g z) =
        (gradedKasparovTensorAction c' d).action g
          (gradedKasparovFirstIsoTensorEquiv c c' d e z) := by
  let L := (gradedKasparovFirstIsoTensorEquiv c c' d e).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have h : L.comp ((gradedKasparovTensorAction c d).action g).toContinuousLinearEquiv.toContinuousLinearMap =
      ((gradedKasparovTensorAction c' d).action g).toContinuousLinearEquiv.toContinuousLinearMap.comp L := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    change gradedKasparovFirstIsoTensorEquiv c c' d e
        ((gradedKasparovTensorAction c d).action g
          (interiorModuleTensorMk d.representation x y)) =
      (gradedKasparovTensorAction c' d).action g
        (gradedKasparovFirstIsoTensorEquiv c c' d e
          (interiorModuleTensorMk d.representation x y))
    simp only [gradedKasparovTensorAction,
      EquivariantHilbertModule.interiorTensor_action_mk, gradedKasparovFirstIsoTensorEquiv_mk,
      e.action_intertwine]
  exact DFunLike.congr_fun h z

theorem gradedKasparovFirstIsoTensorEquiv_representation (a : A)
    (z : InteriorModuleTensor (E := E) d.representation) :
    gradedKasparovFirstIsoTensorEquiv c c' d e
      (gradedKasparovTensorRepresentation c d a z) =
        gradedKasparovTensorRepresentation c' d a
          (gradedKasparovFirstIsoTensorEquiv c c' d e z) :=
  InteriorModuleTensorFirstFactorEquiv.hilbertEquiv_operator d.representation e.moduleEquiv
    (c.representation a) (c'.representation a) (e.representation_intertwine a) z

theorem gradedKasparovFirstIsoTensorEquiv_firstOperator
    (z : InteriorModuleTensor (E := E) d.representation) :
    gradedKasparovFirstIsoTensorEquiv c c' d e
      (interiorModuleTensorOperator d.representation c.operator z) =
        interiorModuleTensorOperator d.representation c'.operator
          (gradedKasparovFirstIsoTensorEquiv c c' d e z) :=
  InteriorModuleTensorFirstFactorEquiv.hilbertEquiv_operator d.representation e.moduleEquiv
    c.operator c'.operator e.operator_intertwine z

theorem gradedKasparovFirstIsoTensorEquiv_transportRepresentation (a : A) :
    (gradedKasparovFirstIsoTensorEquiv c c' d e).transport
      (gradedKasparovTensorRepresentation c d a) = gradedKasparovTensorRepresentation c' d a := by
  ext y
  rw [HilbertModuleEquiv.transport_apply, gradedKasparovFirstIsoTensorEquiv_representation,
    HilbertModuleEquiv.apply_symm_apply]

theorem gradedKasparovFirstIsoTensorEquiv_transportFirstOperator :
    (gradedKasparovFirstIsoTensorEquiv c c' d e).transport
      (interiorModuleTensorOperator d.representation c.operator) =
        interiorModuleTensorOperator d.representation c'.operator := by
  ext y
  rw [HilbertModuleEquiv.transport_apply, gradedKasparovFirstIsoTensorEquiv_firstOperator,
    HilbertModuleEquiv.apply_symm_apply]

@[simp] theorem gradedKasparovFirstIsoTensorEquiv_creation (x : E) (y : F) :
    gradedKasparovFirstIsoTensorEquiv c c' d e (moduleCreationMap d.representation x y) =
      moduleCreationMap d.representation (e.moduleEquiv x) y :=
  gradedKasparovFirstIsoTensorEquiv_mk c c' d e x y

def gradedKasparovFirstIsoProductOperator
    (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) :
    AdjointableMap C (InteriorModuleTensor (E := E') d.representation)
      (InteriorModuleTensor (E := E') d.representation) :=
  (gradedKasparovFirstIsoTensorEquiv c c' d e).transport R

theorem gradedKasparovFirstIsoProduct_conditions
    {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)}
    (hR : GradedKasparovTensorOperatorConditions c d R) :
    GradedKasparovTensorOperatorConditions c' d (gradedKasparovFirstIsoProductOperator c c' d e R) :=
  transportedCycle_tensorConditions c' d (gradedKasparovTensorCycleOfConditions c d R hR)
    (gradedKasparovFirstIsoTensorEquiv c c' d e)
    (gradedKasparovFirstIsoTensorEquiv_grading c c' d e)
    (gradedKasparovFirstIsoTensorEquiv_action c c' d e)
    (gradedKasparovFirstIsoTensorEquiv_representation c c' d e)

section Defects
variable (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
    (InteriorModuleTensor (E := E) d.representation)) (S : AdjointableMap C F F) (x : E)

theorem gradedKasparovFirstIsoProduct_creation_defect_sub :
    (HilbertModuleEquiv.refl (B := C) (E := F)).transportMap
      (gradedKasparovFirstIsoTensorEquiv c c' d e)
      ((moduleCreationMap d.representation x).comp S - R.comp (moduleCreationMap d.representation x)) =
      (moduleCreationMap d.representation (e.moduleEquiv x)).comp S -
        (gradedKasparovFirstIsoProductOperator c c' d e R).comp
          (moduleCreationMap d.representation (e.moduleEquiv x)) := by
  have htransport (z : InteriorModuleTensor (E := E) d.representation) :
      gradedKasparovFirstIsoTensorEquiv c c' d e (R z) =
        gradedKasparovFirstIsoProductOperator c c' d e R
          (gradedKasparovFirstIsoTensorEquiv c c' d e z) := by
    simp only [gradedKasparovFirstIsoProductOperator, HilbertModuleEquiv.transport_apply,
      HilbertModuleEquiv.symm_apply_apply]
  ext y
  rw [HilbertModuleEquiv.transportMap_apply]
  simp only [AdjointableMap.coe_sub_apply, AdjointableMap.comp_apply]
  change gradedKasparovFirstIsoTensorEquiv c c' d e
      (moduleCreationMap d.representation x (S y) -
        R (moduleCreationMap d.representation x y)) =
    moduleCreationMap d.representation (e.moduleEquiv x) (S y) -
      gradedKasparovFirstIsoProductOperator c c' d e R
        (moduleCreationMap d.representation (e.moduleEquiv x) y)
  rw [HilbertModuleEquiv.map_sub, htransport, gradedKasparovFirstIsoTensorEquiv_creation,
    gradedKasparovFirstIsoTensorEquiv_creation]

theorem gradedKasparovFirstIsoProduct_creation_defect_add :
    (HilbertModuleEquiv.refl (B := C) (E := F)).transportMap
      (gradedKasparovFirstIsoTensorEquiv c c' d e)
      ((moduleCreationMap d.representation x).comp S + R.comp (moduleCreationMap d.representation x)) =
      (moduleCreationMap d.representation (e.moduleEquiv x)).comp S +
        (gradedKasparovFirstIsoProductOperator c c' d e R).comp
          (moduleCreationMap d.representation (e.moduleEquiv x)) := by
  have htransport (z : InteriorModuleTensor (E := E) d.representation) :
      gradedKasparovFirstIsoTensorEquiv c c' d e (R z) =
        gradedKasparovFirstIsoProductOperator c c' d e R
          (gradedKasparovFirstIsoTensorEquiv c c' d e z) := by
    simp only [gradedKasparovFirstIsoProductOperator, HilbertModuleEquiv.transport_apply,
      HilbertModuleEquiv.symm_apply_apply]
  ext y
  rw [HilbertModuleEquiv.transportMap_apply]
  simp only [AdjointableMap.coe_add_apply, AdjointableMap.comp_apply]
  change gradedKasparovFirstIsoTensorEquiv c c' d e
      (moduleCreationMap d.representation x (S y) +
        R (moduleCreationMap d.representation x y)) =
    moduleCreationMap d.representation (e.moduleEquiv x) (S y) +
      gradedKasparovFirstIsoProductOperator c c' d e R
        (moduleCreationMap d.representation (e.moduleEquiv x) y)
  rw [HilbertModuleEquiv.map_add, htransport, gradedKasparovFirstIsoTensorEquiv_creation,
    gradedKasparovFirstIsoTensorEquiv_creation]

end Defects

theorem gradedKasparovFirstIsoProduct_connection
    {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)} (hR : GradedKasparovConnection c d R) :
    GradedKasparovConnection c' d (gradedKasparovFirstIsoProductOperator c c' d e R) := by
  have heven (x : E') (hx : c'.grading.grading x = x) :
      c.grading.grading (e.moduleEquiv.symm x) = e.moduleEquiv.symm x := by
    apply e.moduleEquiv.injective
    rw [e.grading_intertwine, HilbertModuleEquiv.apply_symm_apply, hx]
  have hodd (x : E') (hx : c'.grading.grading x = -x) :
      c.grading.grading (e.moduleEquiv.symm x) = -(e.moduleEquiv.symm x) := by
    apply e.moduleEquiv.injective
    rw [e.grading_intertwine, HilbertModuleEquiv.apply_symm_apply, hx, HilbertModuleEquiv.map_neg,
      HilbertModuleEquiv.apply_symm_apply]
  constructor
  · intro x hx
    have h := (HilbertModuleEquiv.refl (B := C) (E := F)).transportMap_isModuleCompact
      (gradedKasparovFirstIsoTensorEquiv c c' d e) (hR.even _ (heven x hx))
    simpa only [gradedKasparovFirstIsoProduct_creation_defect_sub,
      HilbertModuleEquiv.apply_symm_apply] using h
  · intro x hx
    have h := (HilbertModuleEquiv.refl (B := C) (E := F)).transportMap_isModuleCompact
      (gradedKasparovFirstIsoTensorEquiv c c' d e) (hR.even_adjoint _ (heven x hx))
    simpa only [gradedKasparovFirstIsoProduct_creation_defect_sub,
      HilbertModuleEquiv.apply_symm_apply, HilbertModuleEquiv.transport_star,
      gradedKasparovFirstIsoProductOperator] using h
  · intro x hx
    have h := (HilbertModuleEquiv.refl (B := C) (E := F)).transportMap_isModuleCompact
      (gradedKasparovFirstIsoTensorEquiv c c' d e) (hR.odd _ (hodd x hx))
    simpa only [gradedKasparovFirstIsoProduct_creation_defect_add,
      HilbertModuleEquiv.apply_symm_apply] using h
  · intro x hx
    have h := (HilbertModuleEquiv.refl (B := C) (E := F)).transportMap_isModuleCompact
      (gradedKasparovFirstIsoTensorEquiv c c' d e) (hR.odd_adjoint _ (hodd x hx))
    simpa only [gradedKasparovFirstIsoProduct_creation_defect_add,
      HilbertModuleEquiv.apply_symm_apply, HilbertModuleEquiv.transport_star,
      gradedKasparovFirstIsoProductOperator] using h

theorem gradedKasparovFirstIsoProduct_positivityOperator
    (R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)) (a : A) :
    (gradedKasparovFirstIsoTensorEquiv c c' d e).transport
      (gradedKasparovProductPositivityOperator c d R a) =
      gradedKasparovProductPositivityOperator c' d
        (gradedKasparovFirstIsoProductOperator c c' d e R) a := by
  simp only [gradedKasparovProductPositivityOperator, HilbertModuleEquiv.transport_mul,
    HilbertModuleEquiv.transport_add, HilbertModuleEquiv.transport_star,
    gradedKasparovFirstIsoTensorEquiv_transportRepresentation,
    gradedKasparovFirstIsoTensorEquiv_transportFirstOperator, gradedKasparovFirstIsoProductOperator]

theorem gradedKasparovFirstIsoProduct_isProduct
    {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)} (hR : IsGradedKasparovProductOperator c d R) :
    IsGradedKasparovProductOperator c' d (gradedKasparovFirstIsoProductOperator c c' d e R) where
  cycleConditions := gradedKasparovFirstIsoProduct_conditions c c' d e hR.cycleConditions
  connection := gradedKasparovFirstIsoProduct_connection c c' d e hR.connection
  positivity a := by
    have h := (hR.positivity a).transport (gradedKasparovFirstIsoTensorEquiv c c' d e)
    rwa [gradedKasparovFirstIsoProduct_positivityOperator] at h

def gradedKasparovFirstIsoProduct_cycleIso
    {R : AdjointableMap C (InteriorModuleTensor (E := E) d.representation)
      (InteriorModuleTensor (E := E) d.representation)} (hR : IsGradedKasparovProductOperator c d R) :
    GradedKasparovCycleIso (gradedKasparovTensorCycleOfConditions c d R hR.cycleConditions)
      (gradedKasparovTensorCycleOfConditions c' d (gradedKasparovFirstIsoProductOperator c c' d e R)
        (gradedKasparovFirstIsoProduct_isProduct c c' d e hR).cycleConditions) where
  moduleEquiv := gradedKasparovFirstIsoTensorEquiv c c' d e
  grading_intertwine := gradedKasparovFirstIsoTensorEquiv_grading c c' d e
  action_intertwine := gradedKasparovFirstIsoTensorEquiv_action c c' d e
  representation_intertwine := gradedKasparovFirstIsoTensorEquiv_representation c c' d e
  operator_intertwine z := by
    change (gradedKasparovFirstIsoTensorEquiv c c' d e) (R z) =
      (gradedKasparovFirstIsoTensorEquiv c c' d e).transport R
        ((gradedKasparovFirstIsoTensorEquiv c c' d e) z)
    rw [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply]

end BC4lean.KKTheory
