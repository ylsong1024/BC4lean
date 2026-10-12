import BC4lean.LeftUnitIntervalTensorCompatibility

/-! # Explicit A support of the left-unit rank approximants

Continuous A sections embed isometrically in the genuine ideal J. Applying
left A multiplication to any J vector gives such a section. The coefficients
of localized frame ranks therefore lie in C(I,A) at every point of the
interval, which is the support used for the localized square and group errors.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def leftUnitIntervalASection : C(unitInterval, A)ᵐᵒᵖ →ₗᵢ[ℂ] LeftUnitIntervalIdeal A where
  toFun f := ⟨MulOpposite.op (leftUnitIntervalAEmbedding (MulOpposite.unop f)), rfl⟩
  map_add' f g := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    apply ContinuousMap.ext
    intro t
    exact Unitization.inr_add ℂ _ _
  map_smul' z f := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    apply ContinuousMap.ext
    intro t
    exact Unitization.inr_smul ℂ z _
  norm_map' f := by
    change ‖leftUnitIntervalAEmbedding (MulOpposite.unop f)‖ = ‖MulOpposite.unop f‖
    simp only [ContinuousMap.norm_eq_iSup_norm, leftUnitIntervalAEmbedding_apply,
      Unitization.norm_inr]

@[simp] theorem leftUnitIntervalASection_apply (f : C(unitInterval, A)ᵐᵒᵖ) (t : unitInterval) :
    MulOpposite.unop (leftUnitIntervalASection f : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) t =
      (MulOpposite.unop f t : Unitization ℂ A) := rfl

theorem leftUnitIntervalASection_inner (f g : C(unitInterval, A)ᵐᵒᵖ) :
    MulOpposite.unop ⟪leftUnitIntervalASection f, leftUnitIntervalASection g⟫_
      (C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) =
      leftUnitIntervalAEmbedding (MulOpposite.unop ⟪f, g⟫_(C(unitInterval, A)ᵐᵒᵖ)) := by
  apply ContinuousMap.ext
  intro t
  change star (MulOpposite.unop f t : Unitization ℂ A) *
      (MulOpposite.unop g t : Unitization ℂ A) =
    ((star (MulOpposite.unop f t) * MulOpposite.unop g t : A) : Unitization ℂ A)
  rw [← Unitization.inr_star, ← Unitization.inr_mul]

def leftUnitIntervalLeftLocalizedSection (a : A) (x : LeftUnitIntervalIdeal A) : C(unitInterval, A) :=
  ⟨fun t => (MulOpposite.unop (leftUnitIntervalRepresentation a x :
      C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) t).snd,
    Unitization.continuous_snd.comp
      (MulOpposite.unop (leftUnitIntervalRepresentation a x :
        C(unitInterval, Unitization ℂ A)ᵐᵒᵖ)).continuous⟩

theorem leftUnitIntervalLeftLocalizedSection_inr (a : A) (x : LeftUnitIntervalIdeal A) :
    leftUnitIntervalASection (MulOpposite.op (leftUnitIntervalLeftLocalizedSection a x)) =
      leftUnitIntervalRepresentation a x := by
  apply Subtype.ext
  apply MulOpposite.unop_injective
  apply ContinuousMap.ext
  intro t
  apply Unitization.ext
  · change 0 = ((a : Unitization ℂ A) *
      MulOpposite.unop (x : C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) t).fst
    rw [Unitization.fst_mul, Unitization.fst_inr, zero_mul]
  · rfl

/-- Every actual localized pair coefficient has a continuous A preimage. -/
def leftUnitIntervalLocalizedPairInner (a b : A) (x y : LeftUnitIntervalIdeal A) : C(unitInterval, A) :=
  MulOpposite.unop ⟪MulOpposite.op (leftUnitIntervalLeftLocalizedSection a x),
    MulOpposite.op (leftUnitIntervalLeftLocalizedSection b y)⟫_(C(unitInterval, A)ᵐᵒᵖ)

theorem leftUnitIntervalLocalizedPairInner_inr (a b : A) (x y : LeftUnitIntervalIdeal A) :
    leftUnitIntervalAEmbedding (leftUnitIntervalLocalizedPairInner a b x y) =
      MulOpposite.unop ⟪leftUnitIntervalRepresentation a x, leftUnitIntervalRepresentation b y⟫_
        (C(unitInterval, Unitization ℂ A)ᵐᵒᵖ) := by
  rw [← leftUnitIntervalLeftLocalizedSection_inr a x,
    ← leftUnitIntervalLeftLocalizedSection_inr b y,
    leftUnitIntervalASection_inner]
  rfl

theorem leftUnitIntervalRepresentation_mul_rankOne (a : A) (x y : LeftUnitIntervalIdeal A) :
    leftUnitIntervalRepresentation a * moduleRankOne (B := C(unitInterval, Unitization ℂ A)) x y =
      moduleRankOne (leftUnitIntervalRepresentation a x) y :=
  comp_moduleRankOne _ _ _

set_option maxHeartbeats 600000 in
theorem leftUnitIntervalRankOne_mul_representation (a : A) (x y : LeftUnitIntervalIdeal A) :
    moduleRankOne (B := C(unitInterval, Unitization ℂ A)) x y * leftUnitIntervalRepresentation a =
      moduleRankOne x (leftUnitIntervalRepresentation (star a) y) := by
  have h := moduleRankOne_comp
    (B := C(unitInterval, Unitization ℂ A))
    (E := LeftUnitIntervalIdeal A) (F := LeftUnitIntervalIdeal A)
    (G := LeftUnitIntervalIdeal A) x y (leftUnitIntervalRepresentation (A := A) a)
  have hstar : (leftUnitIntervalRepresentation (A := A) a).adjoint =
      leftUnitIntervalRepresentation (A := A) (star a) :=
    (map_star (leftUnitIntervalRepresentation (A := A)) a).symm
  exact h.trans (congrArg
    (fun S : AdjointableMap (C(unitInterval, Unitization ℂ A))
        (LeftUnitIntervalIdeal A) (LeftUnitIntervalIdeal A) =>
      moduleRankOne (B := C(unitInterval, Unitization ℂ A))
        (E := LeftUnitIntervalIdeal A) (F := LeftUnitIntervalIdeal A) x (S y)) hstar)

end BC4lean.KKTheory
