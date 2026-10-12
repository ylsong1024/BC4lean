import BC4lean.CliffordPairModule
import BC4lean.CliffordAlgebraTensor

/-! # The actual external Cl₁ tensor of an evenly coefficient-graded module

The algebraic complex tensor is identified with its two coordinate copies
using tensor distributivity and the scalar tensor unit. The image is the
genuine product-coefficient Hilbert module, whose inner product, max norm
and completeness were proved independently. Thus the completed external
tensor is obtained from a proved surjective coordinate map. Its grading is
the tensor grading, including the original module grading.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped TensorProduct InnerProductSpace

variable {C F : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]

/-- The actual algebraic external tensor coordinate equivalence. -/
def cliffordExternalEvenCoordinates :
    F ⊗[ℂ] CliffordOne ≃ₗ[ℂ] CliffordPairModule C F :=
  (TensorProduct.prodRight ℂ ℂ F ℂ ℂ).trans
    ((TensorProduct.rid ℂ F).prodCongr (TensorProduct.rid ℂ F))

omit [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F] in
@[simp] theorem cliffordExternalEvenCoordinates_tmul (x : F) (z : CliffordOne) :
    cliffordExternalEvenCoordinates (C := C) (x ⊗ₜ[ℂ] z) =
      cliffordPairMk (z.1 • x) (z.2 • x) := by
  change ((TensorProduct.rid ℂ F)
      ((TensorProduct.prodRight ℂ ℂ F ℂ ℂ) (x ⊗ₜ[ℂ] z)).1,
    (TensorProduct.rid ℂ F)
      ((TensorProduct.prodRight ℂ ℂ F ℂ ℂ) (x ⊗ₜ[ℂ] z)).2) = (z.1 • x, z.2 • x)
  rw [TensorProduct.prodRight_tmul]
  simp only [TensorProduct.rid_tmul]

omit [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F] in
/-- The inverse is a genuine finite tensor sum. -/
theorem cliffordExternalEvenCoordinates_symm (x : CliffordPairModule C F) :
    (cliffordExternalEvenCoordinates (C := C)).symm x =
      x.1 ⊗ₜ[ℂ] (1, 0) + x.2 ⊗ₜ[ℂ] (0, 1) := by
  apply (cliffordExternalEvenCoordinates (C := C)).injective
  simp only [LinearEquiv.apply_symm_apply, map_add,
    cliffordExternalEvenCoordinates_tmul, one_smul, zero_smul]
  change (x.1, x.2) = (x.1, (0 : F)) + (0, x.2)
  exact Prod.ext (add_zero _).symm (zero_add _).symm

omit [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F] in
/-- No completion elements are missing from the actual coordinate image. -/
theorem cliffordExternalEvenCoordinates_surjective :
    Function.Surjective (cliffordExternalEvenCoordinates (C := C) (F := F)) :=
  cliffordExternalEvenCoordinates.surjective

/-- The external tensor norm is the genuine C × C Hilbert-module norm. -/
def cliffordExternalEvenNorm (x : F ⊗[ℂ] CliffordOne) : ℝ :=
  ‖cliffordExternalEvenCoordinates (C := C) x‖

omit [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F] in
theorem cliffordExternalEvenNorm_eq_zero_iff (x : F ⊗[ℂ] CliffordOne) :
    cliffordExternalEvenNorm (C := C) x = 0 ↔ x = 0 := by
  rw [cliffordExternalEvenNorm, norm_eq_zero,
    ← map_zero (cliffordExternalEvenCoordinates (C := C)),
    (cliffordExternalEvenCoordinates (C := C)).injective.eq_iff]

omit [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F] in
/-- The completed target is complete for the proved external tensor norm. -/
theorem cliffordExternalEven_complete [CompleteSpace F] :
    CompleteSpace (CliffordPairModule C F) := inferInstance

/-- The elementary vector tensor in the complete external module. -/
def cliffordExternalEvenMk (x : F) (z : CliffordOne) : CliffordPairModule C F :=
  cliffordExternalEvenCoordinates (x ⊗ₜ[ℂ] z)

omit [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F] in
@[simp] theorem cliffordExternalEvenMk_apply (x : F) (z : CliffordOne) :
    cliffordExternalEvenMk (C := C) x z = cliffordPairMk (z.1 • x) (z.2 • x) :=
  cliffordExternalEvenCoordinates_tmul x z

omit [StarOrderedRing C] in
/-- The actual coefficient inner product on elementary external tensors. -/
theorem cliffordExternalEvenMk_inner (x y : F) (z w : CliffordOne) :
    MulOpposite.unop ⟪cliffordExternalEvenMk (C := C) x z,
      cliffordExternalEvenMk y w⟫_((C × C)ᵐᵒᵖ) =
      ((star z.1 * w.1) • MulOpposite.unop ⟪x, y⟫_(Cᵐᵒᵖ),
        (star z.2 * w.2) • MulOpposite.unop ⟪x, y⟫_(Cᵐᵒᵖ)) := by
  change (MulOpposite.unop ⟪z.1 • x, w.1 • y⟫_(Cᵐᵒᵖ),
    MulOpposite.unop ⟪z.2 • x, w.2 • y⟫_(Cᵐᵒᵖ)) = _
  apply Prod.ext <;>
    simp only [CStarModule.inner_smul_left_complex,
      CStarModule.inner_smul_right_complex, smul_smul, MulOpposite.unop_smul, mul_comm]

omit [StarOrderedRing C] in
private theorem cliffordExternalEven_coefficient_complex_comm
    (c : Cᵐᵒᵖ) (a : ℂ) (x : F) : c • (a • x) = a • (c • x) := by
  apply module_inner_ext_right (B := C)
  intro y
  simp only [CStarModule.inner_op_smul_right,
    CStarModule.inner_smul_right_complex, mul_smul_comm]

omit [StarOrderedRing C] in
/-- Right multiplication is the actual external coefficient tensor action. -/
theorem cliffordExternalEvenMk_op_smul (x : F) (z w : CliffordOne) (c : Cᵐᵒᵖ) :
    MulOpposite.op
      (w.1 • MulOpposite.unop c, w.2 • MulOpposite.unop c) •
        cliffordExternalEvenMk (C := C) x z =
      cliffordExternalEvenMk (c • x) (z * w) := by
  change (MulOpposite.op (w.1 • MulOpposite.unop c) • (z.1 • x),
    MulOpposite.op (w.2 • MulOpposite.unop c) • (z.2 • x)) =
      ((z.1 * w.1) • (c • x), (z.2 * w.2) • (c • x))
  apply Prod.ext
  · change MulOpposite.op (w.1 • MulOpposite.unop c) • (z.1 • x) =
      (z.1 * w.1) • (c • x)
    rw [MulOpposite.op_smul, module_complex_smul,
      cliffordExternalEven_coefficient_complex_comm, smul_smul, mul_comm,
      MulOpposite.op_unop]
  · change MulOpposite.op (w.2 • MulOpposite.unop c) • (z.2 • x) =
      (z.2 * w.2) • (c • x)
    rw [MulOpposite.op_smul, module_complex_smul,
      cliffordExternalEven_coefficient_complex_comm, smul_smul, mul_comm,
      MulOpposite.op_unop]

/-- The tensor grading uses both the original vector grading and Cl₁ swap. -/
def cliffordExternalEvenGrading
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading C) F) :
    GradedHilbertModule (cliffordCoefficientGrading : CStarGrading (C × C))
      (CliffordPairModule C F) where
  grading :=
    { toFun x := cliffordPairMk (J.grading x.2) (J.grading x.1)
      invFun x := cliffordPairMk (J.grading x.2) (J.grading x.1)
      left_inv x := by apply Prod.ext <;> exact J.grading_sq _
      right_inv x := by apply Prod.ext <;> exact J.grading_sq _
      map_add' x y := by apply Prod.ext <;> exact J.grading.map_add _ _
      map_smul' c x := by apply Prod.ext <;> exact J.grading.map_smul _ _
      norm_map' x := by
        change max ‖J.grading x.2‖ ‖J.grading x.1‖ = max ‖x.1‖ ‖x.2‖
        rw [J.grading.norm_map, J.grading.norm_map, max_comm] }
  involutive x := by apply Prod.ext <;> exact J.grading_sq _
  inner_grading x y := by
    change MulOpposite.op
        (MulOpposite.unop ⟪J.grading x.2, J.grading y.2⟫_(Cᵐᵒᵖ),
         MulOpposite.unop ⟪J.grading x.1, J.grading y.1⟫_(Cᵐᵒᵖ)) =
      MulOpposite.op (MulOpposite.unop ⟪x.2, y.2⟫_(Cᵐᵒᵖ),
        MulOpposite.unop ⟪x.1, y.1⟫_(Cᵐᵒᵖ))
    simp only [J.inner_grading, CStarGrading.op_trivial_apply]

omit [StarOrderedRing C] in
@[simp] theorem cliffordExternalEvenGrading_mk
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading C) F)
    (x : F) (z : CliffordOne) :
    (cliffordExternalEvenGrading J).grading (cliffordExternalEvenMk x z) =
      cliffordExternalEvenMk (J.grading x) (CliffordOne.grading.automorphism z) := by
  apply Prod.ext <;> exact J.grading.map_smul _ _

end BC4lean.KKTheory
