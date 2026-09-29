import BC4lean.NonUnitalK0Map
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! # Product decomposition for projection K₀ -/
noncomputable section
open scoped Matrix
namespace BC4lean.OperatorKTheory
universe u v
variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
variable [PartialOrder (A × B)] [StarOrderedRing (A × B)]

/-- A projection over a product is the orthogonal sum of its two components. -/
theorem productProjection_split (p : FiniteProjection (A × B)) :
    FiniteProjection.Equivalent p
      (FiniteProjection.blockSum
        (FiniteProjection.mapNU (NonUnitalStarAlgHom.inl ℂ A B)
          (FiniteProjection.map (StarAlgHom.fst ℂ A B) p))
        (FiniteProjection.mapNU (NonUnitalStarAlgHom.inr ℂ A B)
          (FiniteProjection.map (StarAlgHom.snd ℂ A B) p))) := by
  let P := projectionMatrix p.projection
  let l : A × B →⋆ₙₐ[ℂ] A × B :=
    (NonUnitalStarAlgHom.inl ℂ A B).comp (NonUnitalStarAlgHom.fst ℂ A B)
  let r : A × B →⋆ₙₐ[ℂ] A × B :=
    (NonUnitalStarAlgHom.inr ℂ A B).comp (NonUnitalStarAlgHom.snd ℂ A B)
  let L := P.map l
  let R := P.map r
  have hL : Lᴴ = L := by
    dsimp [L]
    rw [← Matrix.conjTranspose_map l (fun x => map_star l x)]
    exact congrArg (fun M => M.map l) (projectionMatrix_star p.projection)
  have hR : Rᴴ = R := by
    dsimp [R]
    rw [← Matrix.conjTranspose_map r (fun x => map_star r x)]
    exact congrArg (fun M => M.map r) (projectionMatrix_star p.projection)
  have hLL : L * L = L := by
    dsimp [L]
    rw [← Matrix.map_mul]
    exact congrArg (fun M => M.map l) (projectionMatrix_mul p.projection)
  have hRR : R * R = R := by
    dsimp [R]
    rw [← Matrix.map_mul]
    exact congrArg (fun M => M.map r) (projectionMatrix_mul p.projection)
  have hLR : L * R = 0 := by
    funext i j
    apply Prod.ext <;> simp [L, R, l, r, Matrix.mul_apply]
  have hRL : R * L = 0 := by
    funext i j
    apply Prod.ext <;> simp [L, R, l, r, Matrix.mul_apply]
  have hsum : L + R = P := by
    funext i j
    apply Prod.ext <;> simp [L, R, l, r]
  change ∃ v : Matrix p.Index (p.Index ⊕ p.Index) (A × B),
    v * vᴴ = P ∧ vᴴ * v = Matrix.fromBlocks L 0 0 R
  refine ⟨Matrix.fromCols L R, ?_, ?_⟩
  · rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromCols_mul_fromRows, hL, hR, hLL, hRR]
    exact hsum
  · rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromRows_mul_fromCols, hL, hR, hLL, hRR, hLR, hRL]

variable (A B)

def k0ProductForward : K0 (A × B) →+ K0 A × K0 B :=
  (k0Map (StarAlgHom.fst ℂ A B)).prod (k0Map (StarAlgHom.snd ℂ A B))

def k0ProductInverse : K0 A × K0 B →+ K0 (A × B) :=
  (k0MapNU (NonUnitalStarAlgHom.inl ℂ A B)).coprod (k0MapNU (NonUnitalStarAlgHom.inr ℂ A B))

/-- The component maps reconstruct every K₀ class. -/
theorem k0Product_leftInverse : Function.LeftInverse (k0ProductInverse A B) (k0ProductForward A B) := by
  have h : (k0ProductInverse A B).comp (k0ProductForward A B) = AddMonoidHom.id _ := by
    apply k0Hom_ext
    intro p
    change k0MapNU _ (k0Map _ (k0Projection p)) + k0MapNU _ (k0Map _ (k0Projection p)) = k0Projection p
    simp only [k0Map_projection, k0MapNU_projection]
    rw [← k0Projection_blockSum]
    exact (k0Projection_eq_of_equivalent (productProjection_split p)).symm
  intro x
  exact DFunLike.congr_fun h x

variable {A B}

omit [PartialOrder (A × B)] [StarOrderedRing (A × B)] in
@[simp] theorem k0MapNU_zero : k0MapNU (0 : A →⋆ₙₐ[ℂ] B) = 0 := by
  apply k0Hom_ext
  intro p
  rw [k0MapNU_projection]
  change k0Projection (FiniteProjection.ofProjection (projectionMapNU 0 p.projection)) = 0
  have h : projectionMapNU (0 : A →⋆ₙₐ[ℂ] B) p.projection = Projection.zero := by
    apply Subtype.ext
    rfl
  rw [h]
  exact (congrArg k0Class (StableProjectionMonoid.of_zeroProjection (A := B) (ι := p.Index))).trans
    (map_zero k0Class)

variable (A B)

theorem k0Product_rightInverse : Function.RightInverse (k0ProductInverse A B) (k0ProductForward A B) := by
  have fl : (k0Map (StarAlgHom.fst ℂ A B)).comp (k0MapNU (NonUnitalStarAlgHom.inl ℂ A B)) =
      AddMonoidHom.id (K0 A) := by
    rw [← k0MapNU_unital, ← k0MapNU_comp]
    have h : ((StarAlgHom.fst ℂ A B).toNonUnitalStarAlgHom).comp
        (NonUnitalStarAlgHom.inl ℂ A B) = NonUnitalStarAlgHom.id ℂ A := by ext; rfl
    rw [h, k0MapNU_id]
  have fr : (k0Map (StarAlgHom.fst ℂ A B)).comp (k0MapNU (NonUnitalStarAlgHom.inr ℂ A B)) = 0 := by
    rw [← k0MapNU_unital, ← k0MapNU_comp]
    have h : ((StarAlgHom.fst ℂ A B).toNonUnitalStarAlgHom).comp
        (NonUnitalStarAlgHom.inr ℂ A B) = 0 := by ext; rfl
    rw [h, k0MapNU_zero]
  have sl : (k0Map (StarAlgHom.snd ℂ A B)).comp (k0MapNU (NonUnitalStarAlgHom.inl ℂ A B)) = 0 := by
    rw [← k0MapNU_unital, ← k0MapNU_comp]
    have h : ((StarAlgHom.snd ℂ A B).toNonUnitalStarAlgHom).comp
        (NonUnitalStarAlgHom.inl ℂ A B) = 0 := by ext; rfl
    rw [h, k0MapNU_zero]
  have sr : (k0Map (StarAlgHom.snd ℂ A B)).comp (k0MapNU (NonUnitalStarAlgHom.inr ℂ A B)) =
      AddMonoidHom.id (K0 B) := by
    rw [← k0MapNU_unital, ← k0MapNU_comp]
    have h : ((StarAlgHom.snd ℂ A B).toNonUnitalStarAlgHom).comp
        (NonUnitalStarAlgHom.inr ℂ A B) = NonUnitalStarAlgHom.id ℂ B := by ext; rfl
    rw [h, k0MapNU_id]
  intro x
  apply Prod.ext
  · change k0Map (StarAlgHom.fst ℂ A B)
      (k0MapNU (NonUnitalStarAlgHom.inl ℂ A B) x.1 +
        k0MapNU (NonUnitalStarAlgHom.inr ℂ A B) x.2) = x.1
    rw [map_add]
    exact (congrArg₂ (· + ·) (DFunLike.congr_fun fl x.1) (DFunLike.congr_fun fr x.2)).trans (add_zero _)
  · change k0Map (StarAlgHom.snd ℂ A B)
      (k0MapNU (NonUnitalStarAlgHom.inl ℂ A B) x.1 +
        k0MapNU (NonUnitalStarAlgHom.inr ℂ A B) x.2) = x.2
    rw [map_add]
    exact (congrArg₂ (· + ·) (DFunLike.congr_fun sl x.1) (DFunLike.congr_fun sr x.2)).trans (zero_add _)

/-- K₀ carries finite products of unital C*-algebras to products of abelian groups. -/
def k0ProductEquiv : K0 (A × B) ≃+ K0 A × K0 B where
  toFun := k0ProductForward A B
  invFun := k0ProductInverse A B
  left_inv := k0Product_leftInverse A B
  right_inv := k0Product_rightInverse A B
  map_add' := map_add (k0ProductForward A B)

end BC4lean.OperatorKTheory
