import BC4lean.AdjointableOperator

/-! # Rank-one operators on right Hilbert C⋆-modules

For x in F and y in E, θ(x,y) maps z to x⟨y,z⟩. We prove boundedness,
adjointability and the composition identities used to construct compact module
operators. Operator-norm closure and the compact-operator ideal are later work.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace
open CStarModule

variable {B E F G : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]

/-- The rank-one map as a bounded complex-linear map. -/
def moduleRankOneCLM (x : F) (y : E) : E →L[ℂ] F :=
  LinearMap.mkContinuous
    { toFun := fun z => ⟪y, z⟫_(Bᵐᵒᵖ) • x
      map_add' := fun z w => by rw [CStarModule.inner_add_right, module_add_smul]
      map_smul' := fun c z => by
        simp only [inner_smul_right_complex, module_complex_smul, RingHom.id_apply] }
    (‖x‖ * ‖y‖) (fun z => by
      calc
        ‖⟪y, z⟫_(Bᵐᵒᵖ) • x‖ ≤ ‖⟪y, z⟫_(Bᵐᵒᵖ)‖ * ‖x‖ := module_norm_smul_le _ _
        _ ≤ (‖y‖ * ‖z‖) * ‖x‖ := mul_le_mul_of_nonneg_right (CStarModule.norm_inner_le E) (_root_.norm_nonneg _)
        _ = (‖x‖ * ‖y‖) * ‖z‖ := by ring)

@[simp] theorem moduleRankOneCLM_apply (x : F) (y z : E) :
    moduleRankOneCLM (B := B) x y z = ⟪y, z⟫_(Bᵐᵒᵖ) • x := rfl

/-- A rank-one map is adjointable, with θ(x,y)* = θ(y,x). -/
def moduleRankOne (x : F) (y : E) : AdjointableMap B E F where
  toCLM := moduleRankOneCLM (B := B) x y
  adjointCLM := moduleRankOneCLM (B := B) y x
  adjoint_identity z w := by
    change ⟪⟪y, z⟫_(Bᵐᵒᵖ) • x, w⟫_(Bᵐᵒᵖ) = ⟪z, ⟪x, w⟫_(Bᵐᵒᵖ) • y⟫_(Bᵐᵒᵖ)
    simp only [inner_op_smul_left, inner_op_smul_right, CStarModule.star_inner]

@[simp] theorem moduleRankOne_apply (x : F) (y z : E) :
    moduleRankOne (B := B) x y z = ⟪y, z⟫_(Bᵐᵒᵖ) • x := rfl

@[simp] theorem moduleRankOne_adjoint (x : F) (y : E) :
    (moduleRankOne (B := B) x y).adjoint = moduleRankOne y x := rfl

/-- The usual rank-one operator-norm bound. -/
theorem moduleRankOne_norm_le (x : F) (y : E) :
    ‖(moduleRankOne (B := B) x y).toCLM‖ ≤ ‖x‖ * ‖y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  change ‖⟪y, z⟫_(Bᵐᵒᵖ) • x‖ ≤ _
  calc
    _ ≤ ‖⟪y, z⟫_(Bᵐᵒᵖ)‖ * ‖x‖ := module_norm_smul_le _ _
    _ ≤ (‖y‖ * ‖z‖) * ‖x‖ := mul_le_mul_of_nonneg_right (CStarModule.norm_inner_le E) (_root_.norm_nonneg _)
    _ = (‖x‖ * ‖y‖) * ‖z‖ := by ring

/-- Left composition by an adjointable map preserves rank-one operators. -/
theorem comp_moduleRankOne (T : AdjointableMap B F G) (x : F) (y : E) :
    T.comp (moduleRankOne x y) = moduleRankOne (T x) y := by
  ext z
  exact T.map_op_smul _ _

/-- Right composition by an adjointable map preserves rank-one operators. -/
theorem moduleRankOne_comp (x : G) (y : F) (T : AdjointableMap B E F) :
    (moduleRankOne x y).comp T = moduleRankOne x (T.adjoint y) := by
  ext z
  change ⟪y, T z⟫_(Bᵐᵒᵖ) • x = ⟪T.adjoint y, z⟫_(Bᵐᵒᵖ) • x
  rw [T.adjoint.adjoint_identity]
  rfl

/-- Product of two rank-one operators. -/
theorem moduleRankOne_comp_moduleRankOne (x : G) (y u : F) (v : E) :
    (moduleRankOne (B := B) x y).comp (moduleRankOne u v) =
      moduleRankOne (⟪y, u⟫_(Bᵐᵒᵖ) • x) v :=
  comp_moduleRankOne _ _ _

/-- On the standard right module, θ(x,y) is left multiplication by x y*. -/
theorem standard_moduleRankOne (x y z : B) :
    MulOpposite.unop (moduleRankOne (B := B) (MulOpposite.op x)
      (MulOpposite.op y) (MulOpposite.op z)) = x * star y * z := by
  change x * (star y * z) = x * star y * z
  rw [mul_assoc]

end BC4lean.KKTheory
