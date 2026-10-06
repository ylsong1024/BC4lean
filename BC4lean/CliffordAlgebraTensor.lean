import BC4lean.CliffordOne
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.Algebra.Star.TensorProduct

/-! # The actual algebraic tensor with the one-generator Clifford algebra

The map `b ⊗ (z₊,z₋) ↦ (z₊b,z₋b)` is constructed on Mathlib's complex
algebraic tensor and proved bijective. Its inverse is the sum of tensors with
the two genuine coordinate projections. Multiplication is transported through
this proved bijection, and its elementary-tensor formula is proved. The actual
tensor star is respected. The explicit C⋆ tensor norm is the max norm of the
coordinate image. Its equality with the universal commuting-representation
maximal tensor norm is proved using an actual faithful unitization representation.
-/

noncomputable section
universe u
namespace BC4lean.KKTheory

open scoped TensorProduct

variable {B : Type*} [NonUnitalCStarAlgebra B]

/-- The genuine complex algebraic tensor, including nonunital B. -/
abbrev CliffordAlgebraicTensor (B : Type*) [NonUnitalCStarAlgebra B] :=
  B ⊗[ℂ] CliffordOne

/-- The genuine tensor-coordinate bijection, obtained from tensor distributivity
and the scalar tensor unit, rather than postulated as an algebra isomorphism. -/
def cliffordTensorCoordinates : CliffordAlgebraicTensor B ≃ₗ[ℂ] B × B :=
  (TensorProduct.prodRight ℂ ℂ B ℂ ℂ).trans
    ((TensorProduct.rid ℂ B).prodCongr (TensorProduct.rid ℂ B))

@[simp] theorem cliffordTensorCoordinates_tmul (b : B) (z : CliffordOne) :
    cliffordTensorCoordinates (b ⊗ₜ[ℂ] z) = (z.1 • b, z.2 • b) := by
  simp [cliffordTensorCoordinates]

/-- The inverse is an actual sum of elementary tensors with the two
Clifford spectral projections, with no unit inserted into B. -/
theorem cliffordTensorCoordinates_symm (b : B × B) :
    cliffordTensorCoordinates.symm b =
      b.1 ⊗ₜ[ℂ] (1, 0) + b.2 ⊗ₜ[ℂ] (0, 1) := by
  apply cliffordTensorCoordinates.injective
  simp only [LinearEquiv.apply_symm_apply, map_add, cliffordTensorCoordinates_tmul,
    one_smul, zero_smul, Prod.mk_add_mk, add_zero, zero_add]

/-- The actual complex-conjugate tensor star maps to the coordinatewise star. -/
theorem cliffordTensorCoordinates_star (x : CliffordAlgebraicTensor B) :
    cliffordTensorCoordinates (star x) = star (cliffordTensorCoordinates x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b z =>
      simp only [TensorProduct.star_tmul, cliffordTensorCoordinates_tmul]
      apply Prod.ext
      · change star z.1 • star b = star (z.1 • b)
        rw [star_smul]
      · change star z.2 • star b = star (z.2 • b)
        rw [star_smul]
  | add x y hx hy => simp only [star_add, map_add, hx, hy]

/-- The tensor multiplication constructed from the proved coordinate bijection. -/
def cliffordTensorMul (x y : CliffordAlgebraicTensor B) : CliffordAlgebraicTensor B :=
  cliffordTensorCoordinates.symm (cliffordTensorCoordinates x * cliffordTensorCoordinates y)

@[simp] theorem cliffordTensorCoordinates_mul (x y : CliffordAlgebraicTensor B) :
    cliffordTensorCoordinates (cliffordTensorMul x y) =
      cliffordTensorCoordinates x * cliffordTensorCoordinates y :=
  cliffordTensorCoordinates.apply_symm_apply _

/-- The constructed multiplication is exactly the intended algebraic
tensor multiplication on elementary tensors. -/
theorem cliffordTensorMul_tmul (b c : B) (z w : CliffordOne) :
    cliffordTensorMul (b ⊗ₜ[ℂ] z) (c ⊗ₜ[ℂ] w) = (b * c) ⊗ₜ[ℂ] (z * w) := by
  apply cliffordTensorCoordinates.injective
  simp only [cliffordTensorCoordinates_mul, cliffordTensorCoordinates_tmul]
  apply Prod.ext
  · change (z.1 • b) * (w.1 • c) = (z.1 * w.1) • (b * c)
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm]
  · change (z.2 • b) * (w.2 • c) = (z.2 * w.2) • (b * c)
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm]

theorem cliffordTensorMul_assoc (x y z : CliffordAlgebraicTensor B) :
    cliffordTensorMul (cliffordTensorMul x y) z = cliffordTensorMul x (cliffordTensorMul y z) := by
  apply cliffordTensorCoordinates.injective
  simp only [cliffordTensorCoordinates_mul, mul_assoc]

theorem cliffordTensorMul_add_left (x y z : CliffordAlgebraicTensor B) :
    cliffordTensorMul (x + y) z = cliffordTensorMul x z + cliffordTensorMul y z := by
  apply cliffordTensorCoordinates.injective
  simp only [cliffordTensorCoordinates_mul, map_add, add_mul]

theorem cliffordTensorMul_add_right (x y z : CliffordAlgebraicTensor B) :
    cliffordTensorMul x (y + z) = cliffordTensorMul x y + cliffordTensorMul x z := by
  apply cliffordTensorCoordinates.injective
  simp only [cliffordTensorCoordinates_mul, map_add, mul_add]

theorem cliffordTensorMul_star (x y : CliffordAlgebraicTensor B) :
    star (cliffordTensorMul x y) = cliffordTensorMul (star y) (star x) := by
  apply cliffordTensorCoordinates.injective
  simp only [cliffordTensorCoordinates_star, cliffordTensorCoordinates_mul, star_mul]

/-- The concrete C⋆ tensor norm, with the coefficient product's max norm. -/
def cliffordTensorNorm (x : CliffordAlgebraicTensor B) : ℝ := ‖cliffordTensorCoordinates x‖

theorem cliffordTensorNorm_eq_max (x : CliffordAlgebraicTensor B) :
    cliffordTensorNorm x =
      max ‖(cliffordTensorCoordinates x).1‖ ‖(cliffordTensorCoordinates x).2‖ :=
  Prod.norm_def _

theorem cliffordTensorNorm_eq_zero_iff (x : CliffordAlgebraicTensor B) :
    cliffordTensorNorm x = 0 ↔ x = 0 := by
  rw [cliffordTensorNorm, norm_eq_zero, ← map_zero cliffordTensorCoordinates,
    cliffordTensorCoordinates.injective.eq_iff]

theorem cliffordTensorNorm_add_le (x y : CliffordAlgebraicTensor B) :
    cliffordTensorNorm (x + y) ≤ cliffordTensorNorm x + cliffordTensorNorm y := by
  simpa only [cliffordTensorNorm, map_add] using
    norm_add_le (cliffordTensorCoordinates x) (cliffordTensorCoordinates y)

theorem cliffordTensorNorm_smul (c : ℂ) (x : CliffordAlgebraicTensor B) :
    cliffordTensorNorm (c • x) = ‖c‖ * cliffordTensorNorm x := by
  simp only [cliffordTensorNorm, map_smul, norm_smul]

theorem cliffordTensorNorm_mul_le (x y : CliffordAlgebraicTensor B) :
    cliffordTensorNorm (cliffordTensorMul x y) ≤ cliffordTensorNorm x * cliffordTensorNorm y := by
  simpa only [cliffordTensorNorm, cliffordTensorCoordinates_mul] using
    norm_mul_le (cliffordTensorCoordinates x) (cliffordTensorCoordinates y)

theorem cliffordTensorNorm_cstar (x : CliffordAlgebraicTensor B) :
    cliffordTensorNorm (cliffordTensorMul (star x) x) = cliffordTensorNorm x * cliffordTensorNorm x := by
  simp only [cliffordTensorNorm, cliffordTensorCoordinates_mul,
    cliffordTensorCoordinates_star, CStarRing.norm_star_mul_self]

/-- The algebraic tensor already maps onto the whole complete coefficient
product. Thus completion in the constructed norm adds no coordinate elements. -/
theorem cliffordTensorCoordinates_surjective :
    Function.Surjective (cliffordTensorCoordinates (B := B)) :=
  cliffordTensorCoordinates.surjective

section CommutingRepresentations

variable {D : Type*} [NonUnitalCStarAlgebra D]
  (φ : B →⋆ₙₐ[ℂ] D) (ψ : CliffordOne →⋆ₙₐ[ℂ] D)
  (hcomm : ∀ b z, φ b * ψ z = ψ z * φ b)

include hcomm

private theorem commutingCliffordProduct (b c : B) (z w : CliffordOne) :
    (φ b * ψ z) * (φ c * ψ w) = φ (b * c) * ψ (z * w) := by
  calc
    (φ b * ψ z) * (φ c * ψ w) = φ b * ((ψ z * φ c) * ψ w) := by
      simp only [mul_assoc]
    _ = φ b * ((φ c * ψ z) * ψ w) := by rw [← hcomm c z]
    _ = (φ b * φ c) * (ψ z * ψ w) := by simp only [mul_assoc]
    _ = φ (b * c) * ψ (z * w) := by rw [map_mul, map_mul]

private theorem commutingCliffordStar (b : B) (z : CliffordOne) :
    star (φ b * ψ z) = φ (star b) * ψ (star z) := by
  rw [star_mul, ← map_star, ← map_star, ← hcomm]

/-- An actual nonunital star homomorphism on the coordinate product for any
commuting B and Clifford representations, including degenerate representations. -/
def commutingCliffordLift : (B × B) →⋆ₙₐ[ℂ] D where
  toFun b := φ b.1 * ψ (1, 0) + φ b.2 * ψ (0, 1)
  map_zero' := by simp
  map_add' b c := by
    change φ (b.1 + c.1) * ψ (1, 0) + φ (b.2 + c.2) * ψ (0, 1) = _
    simp only [map_add, add_mul]
    abel
  map_smul' c b := by
    change φ (c • b.1) * ψ (1, 0) + φ (c • b.2) * ψ (0, 1) = _
    simp only [map_smul, smul_mul_assoc, smul_add, MonoidHom.id_apply]
  map_mul' b c := by
    change φ (b.1 * c.1) * ψ (1, 0) + φ (b.2 * c.2) * ψ (0, 1) = _
    rw [add_mul, mul_add, mul_add]
    rw [commutingCliffordProduct φ ψ hcomm, commutingCliffordProduct φ ψ hcomm,
      commutingCliffordProduct φ ψ hcomm, commutingCliffordProduct φ ψ hcomm]
    simp [show ψ (0, 0) = 0 from map_zero ψ]
  map_star' b := by
    change φ (star b.1) * ψ (1, 0) + φ (star b.2) * ψ (0, 1) = _
    rw [star_add, commutingCliffordStar φ ψ hcomm, commutingCliffordStar φ ψ hcomm]
    have hP : star ((1, 0) : CliffordOne) = (1, 0) := by
      apply Prod.ext
      · exact star_one ℂ
      · exact star_zero ℂ
    have hQ : star ((0, 1) : CliffordOne) = (0, 1) := by
      apply Prod.ext
      · exact star_zero ℂ
      · exact star_one ℂ
    rw [hP, hQ]

@[simp] theorem commutingCliffordLift_apply (b : B × B) :
    commutingCliffordLift φ ψ hcomm b = φ b.1 * ψ (1, 0) + φ b.2 * ψ (0, 1) := rfl

/-- On a genuine elementary tensor the lift is the product of the two
specified commuting representations. -/
theorem commutingCliffordLift_tmul (b : B) (z : CliffordOne) :
    commutingCliffordLift φ ψ hcomm (cliffordTensorCoordinates (b ⊗ₜ[ℂ] z)) = φ b * ψ z := by
  rw [cliffordTensorCoordinates_tmul, commutingCliffordLift_apply]
  rw [map_smul, map_smul, smul_mul_assoc, smul_mul_assoc]
  have hz : ψ z = z.1 • ψ (1, 0) + z.2 • ψ (0, 1) := by
    calc
      ψ z = ψ (z.1 • CliffordOne.plusProjection CliffordOne.epsilon +
        z.2 • CliffordOne.minusProjection CliffordOne.epsilon) := congrArg ψ (CliffordOne.decompose z)
      _ = z.1 • ψ (1, 0) + z.2 • ψ (0, 1) := by
        rw [map_add, map_smul, map_smul, CliffordOne.plusProjection_epsilon,
          CliffordOne.minusProjection_epsilon]
  rw [hz, mul_add, mul_smul_comm, mul_smul_comm]

/-- Every commuting representation is contractive for the explicit tensor
norm, by the proved C⋆ contractivity of the actual coordinate-product lift. -/
theorem commutingCliffordLift_norm_le (x : CliffordAlgebraicTensor B) :
    ‖commutingCliffordLift φ ψ hcomm (cliffordTensorCoordinates x)‖ ≤ cliffordTensorNorm x :=
  NonUnitalStarAlgHom.norm_apply_le (commutingCliffordLift φ ψ hcomm) _

end CommutingRepresentations

/-- The faithful nonunital B representation in the two unitizations. -/
def faithfulCliffordCoefficientRepresentation :
    B →⋆ₙₐ[ℂ] Unitization ℂ B × Unitization ℂ B where
  toFun b := (b, b)
  map_zero' := by apply Prod.ext <;> exact map_zero (Unitization.inrNonUnitalStarAlgHom ℂ B)
  map_add' b c := by apply Prod.ext <;> exact map_add (Unitization.inrNonUnitalStarAlgHom ℂ B) b c
  map_mul' b c := by apply Prod.ext <;> exact map_mul (Unitization.inrNonUnitalStarAlgHom ℂ B) b c
  map_smul' c b := by
    apply Prod.ext <;>
      change (Unitization.inrNonUnitalStarAlgHom ℂ B) (c • b) =
        c • (Unitization.inrNonUnitalStarAlgHom ℂ B) b
    all_goals exact map_smul (Unitization.inrNonUnitalStarAlgHom ℂ B) c b
  map_star' b := by apply Prod.ext <;> exact map_star (Unitization.inrNonUnitalStarAlgHom ℂ B) b

/-- The faithful Clifford representation acts by scalars in each unitization. -/
def faithfulCliffordRepresentation :
    CliffordOne →⋆ₐ[ℂ] Unitization ℂ B × Unitization ℂ B where
  toFun z := (algebraMap ℂ (Unitization ℂ B) z.1, algebraMap ℂ (Unitization ℂ B) z.2)
  map_zero' := by apply Prod.ext <;> exact map_zero _
  map_add' z w := by apply Prod.ext <;> exact map_add _ _ _
  map_mul' z w := by apply Prod.ext <;> exact map_mul _ _ _
  map_one' := by apply Prod.ext <;> exact map_one _
  commutes' c := rfl
  map_star' z := by
    apply Prod.ext
    · exact algebraMap_star_comm z.1
    · exact algebraMap_star_comm z.2

theorem faithfulCliffordRepresentations_commute (b : B) (z : CliffordOne) :
    faithfulCliffordCoefficientRepresentation b * faithfulCliffordRepresentation z =
      faithfulCliffordRepresentation z * faithfulCliffordCoefficientRepresentation b := by
  apply Prod.ext
  · change (b : Unitization ℂ B) * algebraMap ℂ (Unitization ℂ B) z.1 =
      algebraMap ℂ (Unitization ℂ B) z.1 * (b : Unitization ℂ B)
    exact (Algebra.commutes z.1 (b : Unitization ℂ B)).symm
  · change (b : Unitization ℂ B) * algebraMap ℂ (Unitization ℂ B) z.2 =
      algebraMap ℂ (Unitization ℂ B) z.2 * (b : Unitization ℂ B)
    exact (Algebra.commutes z.2 (b : Unitization ℂ B)).symm

/-- The faithful commuting lift has exactly the tensor-coordinate norm.
Together with the universal upper bound, this supplies the reverse bound
for the commuting-representation definition of the maximal tensor norm. -/
theorem faithfulCliffordLift_norm (x : CliffordAlgebraicTensor B) :
    ‖commutingCliffordLift faithfulCliffordCoefficientRepresentation faithfulCliffordRepresentation.toNonUnitalStarAlgHom
      faithfulCliffordRepresentations_commute (cliffordTensorCoordinates x)‖ = cliffordTensorNorm x := by
  change ‖(((cliffordTensorCoordinates x).1 : Unitization ℂ B) * algebraMap ℂ (Unitization ℂ B) 1 +
      ((cliffordTensorCoordinates x).2 : Unitization ℂ B) * algebraMap ℂ (Unitization ℂ B) 0,
    ((cliffordTensorCoordinates x).1 : Unitization ℂ B) * algebraMap ℂ (Unitization ℂ B) 0 +
      ((cliffordTensorCoordinates x).2 : Unitization ℂ B) * algebraMap ℂ (Unitization ℂ B) 1)‖ =
    ‖cliffordTensorCoordinates x‖
  simp only [map_zero, map_one, mul_one, mul_zero, add_zero, zero_add,
    Prod.norm_def, Unitization.norm_inr]

/-- A separate type for the actual algebraic tensor equipped with its proved
tensor multiplication and max-coordinate C⋆ norm. -/
def CliffordTensor (B : Type*) [NonUnitalCStarAlgebra B] := CliffordAlgebraicTensor B

instance cliffordTensorAddCommGroup : AddCommGroup (CliffordTensor B) :=
  inferInstanceAs (AddCommGroup (CliffordAlgebraicTensor B))

instance cliffordTensorComplexModule : Module ℂ (CliffordTensor B) :=
  inferInstanceAs (Module ℂ (CliffordAlgebraicTensor B))

instance cliffordTensorStar : Star (CliffordTensor B) :=
  inferInstanceAs (Star (CliffordAlgebraicTensor B))

instance cliffordTensorMulInstance : Mul (CliffordTensor B) := ⟨cliffordTensorMul⟩

def cliffordTensorCoordinateEquiv : CliffordTensor B ≃ₗ[ℂ] B × B :=
  cliffordTensorCoordinates

instance cliffordTensorNonUnitalRing : NonUnitalRing (CliffordTensor B) :=
  cliffordTensorCoordinateEquiv.injective.nonUnitalRing
    cliffordTensorCoordinateEquiv (map_zero _) (map_add _) cliffordTensorCoordinates_mul
    (map_neg _) (map_sub _) (fun n x => map_nsmul _ n x) (fun n x => map_zsmul _ n x)

instance cliffordTensorStarRing : StarRing (CliffordTensor B) :=
  cliffordTensorCoordinateEquiv.injective.starRing cliffordTensorCoordinateEquiv
    cliffordTensorCoordinates_star (map_add _) cliffordTensorCoordinates_mul

instance cliffordTensorNormedAddCommGroup : NormedAddCommGroup (CliffordTensor B) := by
  letI : SeminormedAddCommGroup (CliffordTensor B) :=
    SeminormedAddCommGroup.induced _ _ cliffordTensorCoordinateEquiv
  exact NormedAddCommGroup.ofSeparation (fun x hx =>
    cliffordTensorCoordinateEquiv.injective (by simpa only [map_zero] using norm_eq_zero.mp hx))

@[simp] theorem cliffordTensor_norm (x : CliffordTensor B) :
    ‖x‖ = cliffordTensorNorm x := rfl

instance cliffordTensorNormedSpace : NormedSpace ℂ (CliffordTensor B) where
  norm_smul_le c x := by
    change ‖cliffordTensorCoordinateEquiv (c • x)‖ ≤ ‖c‖ * ‖cliffordTensorCoordinateEquiv x‖
    rw [map_smul]
    exact norm_smul_le c (cliffordTensorCoordinateEquiv x)

instance cliffordTensorNonUnitalNormedRing : NonUnitalNormedRing (CliffordTensor B) where
  toNonUnitalRing := cliffordTensorNonUnitalRing
  toMetricSpace := inferInstance
  norm := (‖·‖)
  dist_eq x y := dist_eq_norm_neg_add x y
  norm_mul_le x y := cliffordTensorNorm_mul_le (B := B) x y

instance cliffordTensorStarModule : StarModule ℂ (CliffordTensor B) where
  star_smul c x := by
    apply cliffordTensorCoordinateEquiv.injective
    change cliffordTensorCoordinates (star (c • x)) = cliffordTensorCoordinates (star c • star x)
    calc
      cliffordTensorCoordinates (star (c • x)) = star (cliffordTensorCoordinates (c • x)) :=
        cliffordTensorCoordinates_star (B := B) (c • x)
      _ = star (c • cliffordTensorCoordinates x) :=
        congrArg star ((cliffordTensorCoordinates (B := B)).map_smul c x)
      _ = star c • star (cliffordTensorCoordinates x) := star_smul c _
      _ = cliffordTensorCoordinates (star c • star x) :=
        ((cliffordTensorCoordinates (B := B)).map_smul (star c) (star x)).trans
          (congrArg (fun y => star c • y) (cliffordTensorCoordinates_star (B := B) x)) |>.symm

instance cliffordTensorIsScalarTower : IsScalarTower ℂ (CliffordTensor B) (CliffordTensor B) where
  smul_assoc c x y := by
    apply cliffordTensorCoordinateEquiv.injective
    calc
      cliffordTensorCoordinateEquiv ((c • x) * y) =
          cliffordTensorCoordinateEquiv (c • x) * cliffordTensorCoordinateEquiv y :=
        cliffordTensorCoordinates_mul (B := B) (c • x) y
      _ = c • (cliffordTensorCoordinateEquiv x * cliffordTensorCoordinateEquiv y) := by
        rw [map_smul, smul_mul_assoc]
      _ = c • cliffordTensorCoordinateEquiv (x * y) :=
        congrArg (fun z => c • z) (cliffordTensorCoordinates_mul (B := B) x y).symm
      _ = cliffordTensorCoordinateEquiv (c • (x * y)) := (map_smul _ c (x * y)).symm

instance cliffordTensorSMulCommClass : SMulCommClass ℂ (CliffordTensor B) (CliffordTensor B) where
  smul_comm c x y := by
    apply cliffordTensorCoordinateEquiv.injective
    calc
      cliffordTensorCoordinateEquiv (c • (x * y)) =
          c • cliffordTensorCoordinateEquiv (x * y) := map_smul _ c (x * y)
      _ = c • (cliffordTensorCoordinateEquiv x * cliffordTensorCoordinateEquiv y) :=
        congrArg (fun z => c • z) (cliffordTensorCoordinates_mul (B := B) x y)
      _ = cliffordTensorCoordinateEquiv x * cliffordTensorCoordinateEquiv (c • y) := by
        rw [map_smul, mul_smul_comm]
      _ = cliffordTensorCoordinateEquiv (x * (c • y)) :=
        (cliffordTensorCoordinates_mul (B := B) x (c • y)).symm

instance cliffordTensorCStarRing : CStarRing (CliffordTensor B) where
  norm_mul_self_le x := (cliffordTensorNorm_cstar x).ge

/-- The constructed norm makes the algebraic coordinate bijection isometric. -/
def cliffordTensorCoordinateIsometry : CliffordTensor B ≃ₗᵢ[ℂ] B × B where
  toLinearEquiv := cliffordTensorCoordinateEquiv
  norm_map' _ := rfl

/-- The algebraic tensor with its genuine finite-factor C⋆ norm is already
complete. No additional coordinate vectors are added in its completion. -/
instance cliffordTensorCompleteSpace : CompleteSpace (CliffordTensor B) :=
  cliffordTensorCoordinateIsometry.toIsometryEquiv.completeSpace

/-- The actual completed one-generator Clifford tensor is a nonunital C⋆
algebra, with all operations and its norm constructed above. -/
instance cliffordTensorNonUnitalCStarAlgebra : NonUnitalCStarAlgebra (CliffordTensor B) where

/-- The genuine C⋆ tensor-coordinate star-algebra equivalence. -/
def cliffordTensorCoordinateStarAlgEquiv : CliffordTensor B ≃⋆ₐ[ℂ] B × B where
  toEquiv := cliffordTensorCoordinateEquiv.toEquiv
  map_add' := cliffordTensorCoordinateEquiv.map_add
  map_mul' := cliffordTensorCoordinates_mul
  map_star' := cliffordTensorCoordinates_star
  map_smul' := cliffordTensorCoordinateEquiv.map_smul

/-- Commuting representations used in the genuine universal maximal norm.
The target has the coefficient universe; the universal upper bound above also
holds for targets in any universe. A faithful target is constructed below. -/
structure CliffordCommutingRepresentation (B : Type u) [NonUnitalCStarAlgebra B] where
  carrier : Type u
  [cstarAlgebra : NonUnitalCStarAlgebra carrier]
  coefficientRepresentation : B →⋆ₙₐ[ℂ] carrier
  cliffordRepresentation : CliffordOne →⋆ₙₐ[ℂ] carrier
  commutes : ∀ b z, coefficientRepresentation b * cliffordRepresentation z =
    cliffordRepresentation z * coefficientRepresentation b

attribute [instance] CliffordCommutingRepresentation.cstarAlgebra

namespace CliffordCommutingRepresentation

variable {B : Type u} [NonUnitalCStarAlgebra B]

/-- The actual value of the algebraic tensor in the specified representation. -/
def normValue (ρ : CliffordCommutingRepresentation B) (x : CliffordAlgebraicTensor B) : ℝ :=
  ‖commutingCliffordLift ρ.coefficientRepresentation ρ.cliffordRepresentation ρ.commutes
    (cliffordTensorCoordinates x)‖

theorem normValue_le (ρ : CliffordCommutingRepresentation B) (x : CliffordAlgebraicTensor B) :
    ρ.normValue x ≤ cliffordTensorNorm x :=
  commutingCliffordLift_norm_le _ _ _ x

/-- The faithful representation uses the actual two unitizations of B. -/
def faithful : CliffordCommutingRepresentation B where
  carrier := Unitization ℂ B × Unitization ℂ B
  coefficientRepresentation := faithfulCliffordCoefficientRepresentation
  cliffordRepresentation := faithfulCliffordRepresentation.toNonUnitalStarAlgHom
  commutes := faithfulCliffordRepresentations_commute

@[simp] theorem faithful_normValue (x : CliffordAlgebraicTensor B) :
    (faithful (B := B)).normValue x = cliffordTensorNorm x :=
  faithfulCliffordLift_norm x

/-- The largest commuting-representation norm is attained by the explicitly
constructed faithful representation, and is exactly the max-coordinate norm. -/
theorem isGreatest_normValues (x : CliffordAlgebraicTensor B) :
    IsGreatest (Set.range fun ρ : CliffordCommutingRepresentation B => ρ.normValue x)
      (cliffordTensorNorm x) := by
  refine ⟨⟨faithful, faithful_normValue x⟩, ?_⟩
  rintro _ ⟨ρ, rfl⟩
  exact ρ.normValue_le x

/-- The universal maximal Clifford tensor norm is defined from actual
commuting representations, independently of the coordinate norm. -/
def maximalNorm (x : CliffordAlgebraicTensor B) : ℝ :=
  sSup (Set.range fun ρ : CliffordCommutingRepresentation B => ρ.normValue x)

/-- The constructed C⋆ norm is exactly the universal maximal tensor norm. -/
theorem maximalNorm_eq (x : CliffordAlgebraicTensor B) :
    maximalNorm x = cliffordTensorNorm x :=
  (isGreatest_normValues x).isLUB.csSup_eq
    ⟨cliffordTensorNorm x, (isGreatest_normValues x).1⟩

end CliffordCommutingRepresentation

end BC4lean.KKTheory
