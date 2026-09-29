import BC4lean.MatrixStabilization

/-! # Murray–von Neumann equivalence across finite matrix sizes

Rectangular witnesses compare projections without choosing an ordering of the
finite index sets. Their support identities follow from the C⋆-identity.
-/

noncomputable section
open scoped Matrix
namespace BC4lean.OperatorKTheory

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι κ τ υ : Type*} [Fintype ι] [Fintype κ] [Fintype τ] [Fintype υ]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq τ] [DecidableEq υ]

abbrev projectionMatrix (p : MatrixProjection A ι) : Matrix ι ι A :=
  CStarMatrix.ofMatrix.symm p.val

@[simp] theorem projectionMatrix_star (p : MatrixProjection A ι) :
    (projectionMatrix p)ᴴ = projectionMatrix p := p.property.isSelfAdjoint.star_eq

@[simp] theorem projectionMatrix_mul (p : MatrixProjection A ι) :
    projectionMatrix p * projectionMatrix p = projectionMatrix p := p.property.isIdempotentElem.eq

/-- Initial and final projections of a rectangular partial isometry. -/
def RectEquivalent (p : MatrixProjection A ι) (q : MatrixProjection A κ) : Prop :=
  ∃ v : Matrix ι κ A, v * vᴴ = projectionMatrix p ∧ vᴴ * v = projectionMatrix q

/-- The right support equation is derived, rather than included in the definition. -/
theorem rectangular_right_support (q : MatrixProjection A κ) (v : Matrix ι κ A)
    (hv : vᴴ * v = projectionMatrix q) : v * projectionMatrix q = v := by
  let V : CStarMatrix (ι ⊕ κ) (ι ⊕ κ) A :=
    CStarMatrix.ofMatrix (Matrix.fromBlocks (0 : Matrix ι ι A) v 0 0)
  let P : MatrixProjection A (ι ⊕ κ) := projectionBlockSum Projection.zero q
  have hMat :
      (Matrix.fromBlocks (0 : Matrix ι ι A) v (0 : Matrix κ ι A) (0 : Matrix κ κ A))ᴴ *
        Matrix.fromBlocks (0 : Matrix ι ι A) v (0 : Matrix κ ι A) (0 : Matrix κ κ A) =
        Matrix.fromBlocks (0 : Matrix ι ι A) (0 : Matrix ι κ A)
          (0 : Matrix κ ι A) (projectionMatrix q) := by
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, hv]
  have hV : star V * V = P.val := hMat
  have h := Projection.right_support P V hV
  have hMat' :
      Matrix.fromBlocks (0 : Matrix ι ι A) v (0 : Matrix κ ι A) (0 : Matrix κ κ A) *
        Matrix.fromBlocks (0 : Matrix ι ι A) (0 : Matrix ι κ A)
          (0 : Matrix κ ι A) (projectionMatrix q) =
      Matrix.fromBlocks (0 : Matrix ι ι A) v (0 : Matrix κ ι A) (0 : Matrix κ κ A) := h
  simp only [Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
    zero_add, add_zero] at hMat'
  exact congrArg Matrix.toBlocks₁₂ hMat'

theorem rectangular_left_support (p : MatrixProjection A ι) (v : Matrix ι κ A)
    (hv : v * vᴴ = projectionMatrix p) : projectionMatrix p * v = v := by
  have h := rectangular_right_support p vᴴ (by simpa using hv)
  simpa using congrArg Matrix.conjTranspose h

theorem rectEquivalent_refl (p : MatrixProjection A ι) : RectEquivalent p p :=
  ⟨projectionMatrix p, by simp, by simp⟩

theorem rectEquivalent_symm {p : MatrixProjection A ι} {q : MatrixProjection A κ}
    (h : RectEquivalent p q) : RectEquivalent q p := by
  obtain ⟨v, hv, hv'⟩ := h
  exact ⟨vᴴ, by simpa using hv', by simpa using hv⟩

theorem rectEquivalent_trans {p : MatrixProjection A ι} {q : MatrixProjection A κ}
    {r : MatrixProjection A τ} (h : RectEquivalent p q) (k : RectEquivalent q r) :
    RectEquivalent p r := by
  obtain ⟨v, hv, hv'⟩ := h
  obtain ⟨w, hw, hw'⟩ := k
  refine ⟨v * w, ?_, ?_⟩
  · calc
      (v * w) * (v * w)ᴴ = (v * (w * wᴴ)) * vᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (v * projectionMatrix q) * vᴴ := by rw [hw]
      _ = projectionMatrix p := by rw [rectangular_right_support q v hv', hv]
  · calc
      (v * w)ᴴ * (v * w) = wᴴ * ((vᴴ * v) * w) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = wᴴ * (projectionMatrix q * w) := by rw [hv']
      _ = projectionMatrix r := by rw [rectangular_left_support q w hw, hw']

/-- Rectangular equivalence agrees with the earlier relation at equal index types. -/
theorem rectEquivalent_iff_equivalent (p q : MatrixProjection A ι) :
    RectEquivalent p q ↔ Projection.Equivalent p q := by
  constructor
  · rintro ⟨v, hv, hv'⟩
    refine ⟨CStarMatrix.ofMatrix vᴴ, ?_, ?_⟩
    · change vᴴᴴ * vᴴ = projectionMatrix p
      simpa only [Matrix.conjTranspose_conjTranspose] using hv
    · change vᴴ * vᴴᴴ = projectionMatrix q
      simpa only [Matrix.conjTranspose_conjTranspose] using hv' 
  · rintro ⟨v, hv, hv'⟩
    change (CStarMatrix.ofMatrix.symm v)ᴴ * CStarMatrix.ofMatrix.symm v = projectionMatrix p at hv
    change CStarMatrix.ofMatrix.symm v * (CStarMatrix.ofMatrix.symm v)ᴴ = projectionMatrix q at hv'
    exact ⟨(CStarMatrix.ofMatrix.symm v)ᴴ, by simpa using hv, by simpa using hv'⟩

theorem rectEquivalent_blockSum {p : MatrixProjection A ι} {q : MatrixProjection A κ}
    {r : MatrixProjection A τ} {s : MatrixProjection A υ}
    (h : RectEquivalent p q) (k : RectEquivalent r s) :
    RectEquivalent (projectionBlockSum p r) (projectionBlockSum q s) := by
  obtain ⟨v, hv, hv'⟩ := h
  obtain ⟨w, hw, hw'⟩ := k
  refine ⟨Matrix.fromBlocks v 0 0 w, ?_, ?_⟩
  · change Matrix.fromBlocks v (0 : Matrix ι υ A) (0 : Matrix τ κ A) w *
      (Matrix.fromBlocks v 0 0 w)ᴴ =
      Matrix.fromBlocks (projectionMatrix p) 0 0 (projectionMatrix r)
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, hv, hw]
  · change (Matrix.fromBlocks v (0 : Matrix ι υ A) (0 : Matrix τ κ A) w)ᴴ *
      Matrix.fromBlocks v 0 0 w =
      Matrix.fromBlocks (projectionMatrix q) 0 0 (projectionMatrix s)
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, hv', hw']

/-- A change of finite matrix indices does not change the equivalence class. -/
theorem rectEquivalent_of_reindex (p : MatrixProjection A ι) (q : MatrixProjection A κ)
    (e : κ ≃ ι) (hq : projectionMatrix q = (projectionMatrix p).submatrix e e) :
    RectEquivalent p q := by
  refine ⟨(projectionMatrix p).submatrix id e, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_submatrix, projectionMatrix_star,
      Matrix.submatrix_mul_equiv, projectionMatrix_mul, Matrix.submatrix_id_id]
  · rw [Matrix.conjTranspose_submatrix, projectionMatrix_star]
    change (projectionMatrix p).submatrix e (Equiv.refl ι) *
      (projectionMatrix p).submatrix (Equiv.refl ι) e = projectionMatrix q
    rw [Matrix.submatrix_mul_equiv, projectionMatrix_mul, ← hq]

theorem rectEquivalent_zero : RectEquivalent (Projection.zero : MatrixProjection A ι)
    (Projection.zero : MatrixProjection A κ) := by
  refine ⟨0, ?_, ?_⟩ <;> simp only [Matrix.conjTranspose_zero, Matrix.zero_mul] <;> rfl

theorem rectEquivalent_block_comm (p : MatrixProjection A ι) (q : MatrixProjection A κ) :
    RectEquivalent (projectionBlockSum p q) (projectionBlockSum q p) := by
  apply rectEquivalent_of_reindex _ _ (Equiv.sumComm κ ι)
  ext i j
  cases i <;> cases j <;> rfl

/-- Adding a zero block does not change the rectangular equivalence class. -/
theorem rectEquivalent_stabilize (p : MatrixProjection A ι) :
    RectEquivalent p (stabilizeProjection (κ := κ) p) := by
  have h : RectEquivalent (projectionBlockSum p (Projection.zero : MatrixProjection A κ))
      (projectionBlockSum p (Projection.zero : MatrixProjection A Empty)) :=
    rectEquivalent_blockSum (rectEquivalent_refl p) rectEquivalent_zero
  have k : RectEquivalent p (projectionBlockSum p (Projection.zero : MatrixProjection A Empty)) := by
    apply rectEquivalent_of_reindex _ _ (Equiv.sumEmpty ι Empty)
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · rfl
      · exact j.elim
    · exact i.elim
  exact rectEquivalent_trans k (rectEquivalent_symm h)

/-- Rectangular witnesses are equivalent to ordinary equivalence in a common
matrix algebra after the two projections are placed in disjoint corners. -/
theorem rectEquivalent_iff_padded (p : MatrixProjection A ι) (q : MatrixProjection A κ) :
    RectEquivalent p q ↔ Projection.Equivalent
      (projectionBlockSum p (Projection.zero : MatrixProjection A κ))
      (projectionBlockSum (Projection.zero : MatrixProjection A ι) q) := by
  have hp := rectEquivalent_stabilize (κ := κ) p
  have hq := rectEquivalent_trans (rectEquivalent_stabilize (κ := ι) q)
    (rectEquivalent_block_comm q (Projection.zero : MatrixProjection A ι))
  rw [← rectEquivalent_iff_equivalent]
  constructor
  · intro h
    exact rectEquivalent_trans (rectEquivalent_trans (rectEquivalent_symm hp) h) hq
  · intro h
    exact rectEquivalent_trans (rectEquivalent_trans hp h) (rectEquivalent_symm hq)

end BC4lean.OperatorKTheory
