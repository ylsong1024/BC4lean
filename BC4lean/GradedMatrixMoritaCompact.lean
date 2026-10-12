import BC4lean.GradedMatrixMoritaRow

/-! # Actual compact-operator identifications for the matrix Morita modules

The column identification uses actual finite matrix extraction. The row
identification is proved from its explicit rank-one formula, an approximate
unit of B, and the closed range of its isometric left action. No abstract
Morita equivalence or KK equivalence is an input to either construction.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace Topology
open Filter

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

namespace GradedMatrixMoritaColumn

def compactHom : GradedMatrixMoritaMatrix B →⋆ₙₐ[ℂ]
    CompactModuleOperator B (GradedMatrixMoritaColumn B) :=
  NonUnitalStarAlgHom.codRestrict leftAction (compactModuleOperatorAlgebra
    (B := B) (E := GradedMatrixMoritaColumn B)) leftAction_compact

theorem compactHom_bijective : Function.Bijective (compactHom (B := B)) := by
  constructor
  · intro M N h
    exact leftAction_injective (congrArg Subtype.val h)
  · intro T
    obtain ⟨M, hM⟩ := finiteModuleCompact_exists_matrix T.property
    exact ⟨M, Subtype.ext hM⟩

def compactEquiv : GradedMatrixMoritaMatrix B ≃⋆ₐ[ℂ]
    CompactModuleOperator B (GradedMatrixMoritaColumn B) :=
  StarAlgEquiv.ofBijective compactHom compactHom_bijective

@[simp] theorem compactEquiv_apply_val (M : GradedMatrixMoritaMatrix B) :
    (compactEquiv M).val = leftAction M := rfl

end GradedMatrixMoritaColumn

namespace GradedMatrixMoritaRow

def cornerRow (b : B) : GradedMatrixMoritaRow B :=
  ⟨MulOpposite.op (GradedMatrixMoritaMatrix.corner b), by
    intro j
    fin_cases j <;> simp [GradedMatrixMoritaMatrix.corner]⟩

@[simp] theorem matrix_cornerRow (b : B) :
    matrix (cornerRow b) = GradedMatrixMoritaMatrix.corner b := rfl

@[simp] theorem norm_cornerRow (b : B) : ‖cornerRow b‖ = ‖b‖ :=
  GradedMatrixMoritaMatrix.cornerHom_isometry.norm_map_of_map_zero
    (map_zero (GradedMatrixMoritaMatrix.cornerHom (B := B))) b

def leftInner (x y : GradedMatrixMoritaRow B) : B :=
  ∑ j : Fin 2, matrix x 0 j * star (matrix y 0 j)

/-- The actual row outer product is precisely a top-left corner coefficient. -/
theorem matrix_mul_star (x y : GradedMatrixMoritaRow B) :
    matrix x * star (matrix y) = GradedMatrixMoritaMatrix.corner (leftInner x y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GradedMatrixMoritaMatrix.corner, CStarMatrix.mul_apply, CStarMatrix.star_apply,
      Fin.sum_univ_two, leftInner]

/-- Row rank-one maps are actual left multiplications by their B-valued pairing. -/
theorem rankOne_eq_leftAction (x y : GradedMatrixMoritaRow B) :
    moduleRankOne (B := GradedMatrixMoritaMatrix B) x y = leftAction (leftInner x y) := by
  ext z
  apply MulOpposite.unop_injective
  change matrix x * (star (matrix y) * matrix z) =
    GradedMatrixMoritaMatrix.corner (leftInner x y) * matrix z
  rw [← mul_assoc, matrix_mul_star]

@[simp] theorem leftInner_cornerRow (b c : B) :
    leftInner (cornerRow b) (cornerRow c) = b * star c := by
  simp [leftInner, GradedMatrixMoritaMatrix.corner, Fin.sum_univ_two]

theorem leftAction_cornerRow (b c : B) : leftAction b (cornerRow c) = cornerRow (b * c) := by
  apply Subtype.ext
  apply MulOpposite.unop_injective
  change GradedMatrixMoritaMatrix.corner b * GradedMatrixMoritaMatrix.corner c =
    GradedMatrixMoritaMatrix.corner (b * c)
  exact (map_mul (GradedMatrixMoritaMatrix.cornerHom (B := B)) b c).symm

/-- The row action is faithful and has its exact C⋆ operator norm, without a unit. -/
theorem norm_leftAction (b : B) : ‖leftAction b‖ = ‖b‖ := by
  apply le_antisymm (NonUnitalStarAlgHom.norm_apply_le leftAction b)
  by_cases hb : ‖b‖ = 0
  · simpa only [hb] using norm_nonneg (leftAction b)
  · have h : ‖b‖ * ‖b‖ ≤ ‖leftAction b‖ * ‖b‖ := by
      have hbound := AdjointableMap.norm_apply_le (leftAction b) (cornerRow (star b))
      simpa only [leftAction_cornerRow, norm_cornerRow, norm_star,
        CStarRing.norm_self_mul_star, AdjointableMap.norm_def] using hbound
    exact le_of_mul_le_mul_right h (lt_of_le_of_ne (norm_nonneg b) (Ne.symm hb))

def leftLinear : B →ₗ[ℂ] AdjointableMap (GradedMatrixMoritaMatrix B)
    (GradedMatrixMoritaRow B) (GradedMatrixMoritaRow B) where
  toFun := leftAction
  map_add' := map_add leftAction
  map_smul' := map_smul leftAction

def leftIsometry : B →ₗᵢ[ℂ] AdjointableMap (GradedMatrixMoritaMatrix B)
    (GradedMatrixMoritaRow B) (GradedMatrixMoritaRow B) where
  toLinearMap := leftLinear
  norm_map' := norm_leftAction

/-- The coefficient approximate unit proves every left B coefficient compact. -/
theorem leftAction_compact (b : B) : IsModuleCompact (leftAction b) := by
  have hlim : Tendsto (fun u : B => leftAction (b * u))
      (CStarAlgebra.approximateUnit B) (𝓝 (leftAction b)) :=
    leftIsometry.continuous.tendsto b |>.comp
      ((CStarAlgebra.increasingApproximateUnit B).tendsto_mul_left b)
  apply moduleCompact_isClosed.mem_of_tendsto hlim
  exact Eventually.of_forall fun u => by
    change IsModuleCompact (leftAction (b * u))
    have hc : IsModuleCompact (moduleRankOne (B := GradedMatrixMoritaMatrix B)
        (cornerRow b) (cornerRow (star u))) :=
      moduleRankOne_mem_moduleCompact (B := GradedMatrixMoritaMatrix B)
        (cornerRow b) (cornerRow (star u))
    rw [rankOne_eq_leftAction, leftInner_cornerRow, star_star] at hc
    exact hc

theorem compact_eq_range : moduleCompact (GradedMatrixMoritaMatrix B)
    (GradedMatrixMoritaRow B) (GradedMatrixMoritaRow B) = (leftLinear (B := B)).range := by
  apply le_antisymm
  · apply moduleCompact_le_of_isClosed (B := GradedMatrixMoritaMatrix B)
      (E := GradedMatrixMoritaRow B) (F := GradedMatrixMoritaRow B) leftLinear.range
      leftIsometry.isometry.isClosedEmbedding.isClosed_range
    intro x y
    exact ⟨leftInner x y, (rankOne_eq_leftAction x y).symm⟩
  · rintro T ⟨b, rfl⟩
    exact leftAction_compact b

def compactHom : B →⋆ₙₐ[ℂ]
    CompactModuleOperator (GradedMatrixMoritaMatrix B) (GradedMatrixMoritaRow B) :=
  NonUnitalStarAlgHom.codRestrict leftAction (compactModuleOperatorAlgebra
    (B := GradedMatrixMoritaMatrix B) (E := GradedMatrixMoritaRow B)) leftAction_compact

theorem compactHom_bijective : Function.Bijective (compactHom (B := B)) := by
  constructor
  · intro b c h
    exact leftIsometry.injective (congrArg Subtype.val h)
  · intro T
    have hT : (T : AdjointableMap (GradedMatrixMoritaMatrix B)
        (GradedMatrixMoritaRow B) (GradedMatrixMoritaRow B)) ∈ leftLinear.range := by
      rw [← compact_eq_range]
      exact T.property
    obtain ⟨b, hb⟩ := hT
    exact ⟨b, Subtype.ext hb⟩

/-- B is identified with the actual compact operators on its genuine row module. -/
def compactEquiv : B ≃⋆ₐ[ℂ]
    CompactModuleOperator (GradedMatrixMoritaMatrix B) (GradedMatrixMoritaRow B) :=
  StarAlgEquiv.ofBijective compactHom compactHom_bijective

@[simp] theorem compactEquiv_apply_val (b : B) : (compactEquiv b).val = leftAction b := rfl

end GradedMatrixMoritaRow
end BC4lean.KKTheory
