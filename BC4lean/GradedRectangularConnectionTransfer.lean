import BC4lean.RectangularInteriorModuleTensorOperator
import BC4lean.CompactFirstModuleConnection

/-! # Genuine compact rectangular transfer between signed connections

This is the compact-map step of Skandalis's Prop.9(e). Tensoring an actual
compact rectangular first-factor map need not produce a compact map. Its
graded intertwining error between two actual connections is nevertheless
compact: the exact rank-one creation formula proves the statement first,
and the closed rectangular compact ideal proves the full norm-limit result.
The independent adjoint connection laws are retained.
-/

noncomputable section
namespace BC4lean.KKTheory.GradedRectangularConnectionTransfer
open scoped InnerProductSpace
open RectangularInteriorModuleTensorOperator

variable {B C E E' F : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [hStarB : StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [SMul Bᵐᵒᵖ E'] [CStarModule Bᵐᵒᵖ E']
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [hCompleteE : CompleteSpace E] [hCompleteEprime : CompleteSpace E'] [CompleteSpace F]
  {δB : CStarGrading B}
  (J : GradedHilbertModule δB E) (J' : GradedHilbertModule δB E')

/-- Semilinear grading conjugation is coefficient-linear on rectangular maps. -/
def conjugate (K : AdjointableMap B E E') : AdjointableMap B E E' where
  toCLM := J'.grading.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (K.toCLM.comp J.grading.toContinuousLinearEquiv.toContinuousLinearMap)
  adjointCLM := J.grading.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (K.adjointCLM.comp J'.grading.toContinuousLinearEquiv.toContinuousLinearMap)
  adjoint_identity x y := by
    change ⟪J'.grading (K (J.grading x)), y⟫_(Bᵐᵒᵖ) =
      ⟪x, J.grading (K.adjointCLM (J'.grading y))⟫_(Bᵐᵒᵖ)
    rw [J'.inner_grading_left, K.adjoint_identity, J.inner_grading_left,
      CStarGrading.op_automorphism_sq]

@[simp] theorem conjugate_apply
  {B E E' : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [SMul Bᵐᵒᵖ E'] [CStarModule Bᵐᵒᵖ E']
  [CompleteSpace E] [CompleteSpace E']
  {δB : CStarGrading B}
  (J : GradedHilbertModule δB E) (J' : GradedHilbertModule δB E')
  (K : AdjointableMap B E E') (x : E) :
    conjugate J J' K x = J'.grading (K (J.grading x)) := rfl

theorem conjugate_add
  {B E E' : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [SMul Bᵐᵒᵖ E'] [CStarModule Bᵐᵒᵖ E']
  [CompleteSpace E] [CompleteSpace E']
  {δB : CStarGrading B}
  (J : GradedHilbertModule δB E) (J' : GradedHilbertModule δB E')
  (K L : AdjointableMap B E E') :
    conjugate J J' (K + L) = conjugate J J' K + conjugate J J' L := by
  apply AdjointableMap.ext
  intro x
  simp only [conjugate_apply, AdjointableMap.coe_add_apply, map_add]

theorem conjugate_smul
  {B E E' : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [SMul Bᵐᵒᵖ E'] [CStarModule Bᵐᵒᵖ E']
  [CompleteSpace E] [CompleteSpace E']
  {δB : CStarGrading B}
  (J : GradedHilbertModule δB E) (J' : GradedHilbertModule δB E')
  (a : ℂ) (K : AdjointableMap B E E') :
    conjugate J J' (a • K) = a • conjugate J J' K := by
  apply AdjointableMap.ext
  intro x
  simp only [conjugate_apply, AdjointableMap.coe_smul_apply, map_smul]

theorem conjugate_norm_le
  {B E E' : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [SMul Bᵐᵒᵖ E'] [CStarModule Bᵐᵒᵖ E']
  [CompleteSpace E] [CompleteSpace E']
  {δB : CStarGrading B}
  (J : GradedHilbertModule δB E) (J' : GradedHilbertModule δB E')
  (K : AdjointableMap B E E') : ‖conjugate J J' K‖ ≤ ‖K‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖J'.grading (K (J.grading x))‖ ≤ ‖K‖ * ‖x‖
  rw [J'.grading.norm_map]
  simpa only [AdjointableMap.norm_def, J.grading.norm_map] using
    K.toCLM.le_opNorm (J.grading x)

def conjugateCLM : AdjointableMap B E E' →L[ℂ] AdjointableMap B E E' :=
  LinearMap.mkContinuous
    { toFun := conjugate J J'
      map_add' := conjugate_add J J'
      map_smul' := conjugate_smul J J' }
    1 (fun K => by
      change ‖conjugate J J' K‖ ≤ (1 : ℝ) * ‖K‖
      rw [one_mul]
      exact conjugate_norm_le J J' K)

@[simp] theorem conjugateCLM_apply (K : AdjointableMap B E E') :
    conjugateCLM J J' K = conjugate J J' K := rfl

theorem conjugate_rankOne
  {B E E' : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [SMul Bᵐᵒᵖ E'] [CStarModule Bᵐᵒᵖ E']
  [CompleteSpace E] [CompleteSpace E']
  {δB : CStarGrading B}
  (J : GradedHilbertModule δB E) (J' : GradedHilbertModule δB E')
  (x : E') (y : E) :
    conjugate J J' (moduleRankOne (B := B) x y) =
      moduleRankOne (J'.grading x) (J.grading y) := by
  apply AdjointableMap.ext
  intro z
  simp only [conjugate_apply, moduleRankOne_apply, J'.map_op_smul]
  rw [← J.inner_grading_left]

variable (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (S : AdjointableMap C F F)
  (R : AdjointableMap C (InteriorModuleTensor (E := E') φ) (InteriorModuleTensor (E := E') φ))
  (T : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ))

def defectCLM : AdjointableMap B E E' →L[ℂ]
    AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E') φ) :=
  (AdjointableMap.compLeftContinuousLinearMap R).comp (tensorCLM φ) -
    (AdjointableMap.compRightContinuousLinearMap T).comp
      ((tensorCLM φ).comp (conjugateCLM J J'))

@[simp] theorem defectCLM_apply (K : AdjointableMap B E E') :
    defectCLM J J' φ R T K = R.comp (tensor φ K) - (tensor φ (conjugate J J' K)).comp T := rfl

/-- Both true connection laws give the compact rank-one transfer. -/
theorem rankOne_defect_compact
    (hR : IsSignedModuleConnection J' φ S R) (hT : IsSignedModuleConnection J φ S T)
    (x : E') (y : E) :
    IsModuleCompact (R.comp (tensor φ (moduleRankOne (B := B) x y)) -
      (tensor φ (conjugate J J' (moduleRankOne (B := B) x y))).comp T) := by
  rw [conjugate_rankOne, tensor_rankOne, tensor_rankOne]
  have h := ((hR.creation x).comp_right (moduleCreationMap φ y).adjoint).add
    ((hT.adjoint_creation y).comp_left (moduleCreationMap φ (J'.grading x)))
  convert h using 1
  apply AdjointableMap.ext
  intro z
  simp only [AdjointableMap.comp_apply, AdjointableMap.coe_add_apply,
    AdjointableMap.coe_sub_apply, map_sub]
  abel

/-- Prop.9(e) on the actual norm-closed rectangular compact ideal. -/
theorem defect_compact
    (hR : IsSignedModuleConnection J' φ S R) (hT : IsSignedModuleConnection J φ S T)
    {K : AdjointableMap B E E'} (hK : IsModuleCompact K) :
    IsModuleCompact (R.comp (tensor φ K) - (tensor φ (conjugate J J' K)).comp T) := by
  let L := defectCLM J J' φ R T
  let P := (moduleCompact C (InteriorModuleTensor (E := E) φ)
    (InteriorModuleTensor (E := E') φ)).comap L.toLinearMap
  have hP : IsClosed (P : Set (AdjointableMap B E E')) := moduleCompact_isClosed.preimage L.continuous
  have hθ (x : E') (y : E) : moduleRankOne (B := B) x y ∈ P :=
    rankOne_defect_compact J J' φ S R T hR hT x y
  exact moduleCompact_le_of_isClosed P hP hθ hK

/-- The independent adjoint law yields the adjoint transfer, without any
selfadjointness hypothesis on the original connections or second operator. -/
theorem adjoint_defect_compact
    (hR : IsSignedModuleConnection J' φ S R) (hT : IsSignedModuleConnection J φ S T)
    {K : AdjointableMap B E E'} (hK : IsModuleCompact K) :
    IsModuleCompact ((star R).comp (tensor φ K) -
      (tensor φ (conjugate J J' K)).comp (star T)) := by
  apply defect_compact J J' φ (star S) (star R) (star T) _ _ hK
  · exact ⟨hR.creation_adjoint, by simpa only [star_star] using hR.creation⟩
  · exact ⟨hT.creation_adjoint, by simpa only [star_star] using hT.creation⟩

end BC4lean.KKTheory.GradedRectangularConnectionTransfer
