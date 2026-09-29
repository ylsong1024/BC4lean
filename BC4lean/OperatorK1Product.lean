import BC4lean.OperatorK1Functoriality

/-! # Product decomposition for stable unitary K₁ -/
noncomputable section
open scoped CStarAlgebra
namespace BC4lean.OperatorKTheory
universe u v
variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def matrixPair (x : CStarMatrix ι ι A) (y : CStarMatrix ι ι B) : CStarMatrix ι ι (A × B) :=
  CStarMatrix.ofMatrix (fun i j => (x i j, y i j))

@[simp] theorem matrixMap_fst_pair (x : CStarMatrix ι ι A) (y : CStarMatrix ι ι B) :
    matrixMap (StarAlgHom.fst ℂ A B) (matrixPair x y) = x := rfl
@[simp] theorem matrixMap_snd_pair (x : CStarMatrix ι ι A) (y : CStarMatrix ι ι B) :
    matrixMap (StarAlgHom.snd ℂ A B) (matrixPair x y) = y := rfl

theorem matrix_prod_ext {x y : CStarMatrix ι ι (A × B)}
    (h : matrixMap (StarAlgHom.fst ℂ A B) x = matrixMap (StarAlgHom.fst ℂ A B) y)
    (k : matrixMap (StarAlgHom.snd ℂ A B) x = matrixMap (StarAlgHom.snd ℂ A B) y) : x = y := by
  funext i j
  exact Prod.ext (congrArg (fun M : CStarMatrix ι ι A => M i j) h)
    (congrArg (fun M : CStarMatrix ι ι B => M i j) k)

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
variable [PartialOrder (A × B)] [StarOrderedRing (A × B)]

/-- Pair finite matrix unitaries of the same size, entry by entry. -/
def unitaryPair (a : MatrixUnitary A ι) (b : MatrixUnitary B ι) : MatrixUnitary (A × B) ι :=
  ⟨matrixPair a b, by
    rw [Unitary.mem_iff]
    constructor <;> apply matrix_prod_ext <;>
      simp only [map_mul, map_star, map_one, matrixMap_fst_pair, matrixMap_snd_pair,
        Unitary.star_mul_self_of_mem a.property, Unitary.mul_star_self_of_mem a.property,
        Unitary.star_mul_self_of_mem b.property, Unitary.mul_star_self_of_mem b.property]⟩

@[simp] theorem unitaryPair_fst (a : MatrixUnitary A ι) (b : MatrixUnitary B ι) :
    matrixUnitaryMap (StarAlgHom.fst ℂ A B) (unitaryPair a b) = a := by apply Subtype.ext; rfl
@[simp] theorem unitaryPair_snd (a : MatrixUnitary A ι) (b : MatrixUnitary B ι) :
    matrixUnitaryMap (StarAlgHom.snd ℂ A B) (unitaryPair a b) = b := by apply Subtype.ext; rfl

@[simp] theorem unitaryPair_one : unitaryPair (1 : MatrixUnitary A ι) (1 : MatrixUnitary B ι) = 1 := by
  apply Subtype.ext
  change matrixPair (1 : CStarMatrix ι ι A) (1 : CStarMatrix ι ι B) = 1
  apply matrix_prod_ext <;> simp only [map_one, matrixMap_fst_pair, matrixMap_snd_pair]

theorem continuous_unitaryPair : Continuous (fun x : MatrixUnitary A ι × MatrixUnitary B ι => unitaryPair x.1 x.2) := by
  apply Continuous.subtype_mk
  apply CStarMatrix.ofMatrixL.continuous.comp
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have ha := CStarMatrix.ofMatrixL.symm.continuous.comp
    (continuous_subtype_val.comp (continuous_fst : Continuous (fun x : MatrixUnitary A ι × MatrixUnitary B ι => x.1)))
  have hb := CStarMatrix.ofMatrixL.symm.continuous.comp
    (continuous_subtype_val.comp (continuous_snd : Continuous (fun x : MatrixUnitary A ι × MatrixUnitary B ι => x.2)))
  exact ((continuous_apply j).comp ((continuous_apply i).comp ha)).prodMk
    ((continuous_apply j).comp ((continuous_apply i).comp hb))

@[simp] theorem unitaryReindex_one (e : ι ≃ κ) : unitaryReindex e (1 : MatrixUnitary A ι) = 1 := by
  apply Subtype.ext
  exact map_one (CStarMatrix.reindexₐ ℂ A e)

theorem unitaryPair_reindex (e : ι ≃ κ) (a : MatrixUnitary A ι) (b : MatrixUnitary B ι) :
    unitaryReindex e (unitaryPair a b) = unitaryPair (unitaryReindex e a) (unitaryReindex e b) := by
  apply Subtype.ext
  rfl

theorem unitaryPair_blockSum (a : MatrixUnitary A ι) (b : MatrixUnitary B ι)
    (c : MatrixUnitary A κ) (d : MatrixUnitary B κ) :
    unitaryPair (unitaryBlockSum a c) (unitaryBlockSum b d) =
      unitaryBlockSum (unitaryPair a b) (unitaryPair c d) := by
  apply Subtype.ext
  funext i j
  cases i <;> cases j <;> rfl

namespace FiniteUnitary
abbrev prodInl (a : FiniteUnitary A) : FiniteUnitary (A × B) := ofUnitary (unitaryPair a.val 1)

theorem prodInl_blockSum (a b : FiniteUnitary A) :
    prodInl (B := B) (blockSum a b) = blockSum (prodInl a) (prodInl b) := by
  have h : unitaryBlockSum (1 : MatrixUnitary B a.Index) (1 : MatrixUnitary B b.Index) = 1 :=
    Subtype.ext matrixBlockSum_one
  change ofUnitary (unitaryPair (unitaryBlockSum a.val b.val) 1) = _
  rw [← h, unitaryPair_blockSum]

@[simp] theorem prodInl_identity (ι : Type) [Fintype ι] [DecidableEq ι] :
    prodInl (B := B) (identity (A := A) ι) = identity ι := by
  change ofUnitary (unitaryPair (1 : MatrixUnitary A ι) (1 : MatrixUnitary B ι)) = ofUnitary 1
  rw [unitaryPair_one]

theorem prodInl_congr {a b : FiniteUnitary A} (h : Equivalent a b) :
    Equivalent (prodInl (B := B) a) (prodInl b) := by
  induction h with
  | refl a => exact equivalent_refl _
  | symm a b h ih => exact equivalent_symm ih
  | trans a b c h k ih ik => exact equivalent_trans ih ik
  | rel a b h =>
    cases h with
    | homotopy b e h =>
      apply Relation.EqvGen.rel
      apply Move.homotopy (prodInl a) (prodInl b) e
      change UnitaryHomotopic (unitaryReindex e (unitaryPair a.val 1)) (unitaryPair b.val 1)
      rw [unitaryPair_reindex, unitaryReindex_one]
      exact (Joined.prod h (unitaryHomotopic_refl (1 : MatrixUnitary B b.Index))).map continuous_unitaryPair
    | stabilize κ =>
      rw [prodInl_blockSum, prodInl_identity]
      exact equivalent_stabilize _ κ
end FiniteUnitary

variable (A B)
def k1ProductInl : K1 A →+ K1 (A × B) where
  toFun := Quotient.map FiniteUnitary.prodInl (fun _ _ h => FiniteUnitary.prodInl_congr h)
  map_zero' := congrArg K1.of (FiniteUnitary.prodInl_identity (A := A) (B := B) Empty)
  map_add' a b := by
    refine Quotient.inductionOn₂ a b ?_
    intro a b
    exact congrArg K1.of (FiniteUnitary.prodInl_blockSum a b)

/-- Swap the factors using the unital coordinate homomorphisms. -/
def productSwap : B × A →⋆ₐ[ℂ] A × B := (StarAlgHom.snd ℂ B A).prod (StarAlgHom.fst ℂ B A)

def k1ProductInr : K1 B →+ K1 (A × B) := (k1Map (productSwap A B)).comp (k1ProductInl B A)

@[simp] theorem k1ProductInl_of (a : FiniteUnitary A) :
    k1ProductInl A B (K1.of a) = K1.of (FiniteUnitary.ofUnitary (unitaryPair a.val (1 : MatrixUnitary B a.Index))) := rfl

@[simp] theorem k1ProductInr_of (b : FiniteUnitary B) :
    k1ProductInr A B (K1.of b) = K1.of (FiniteUnitary.ofUnitary (unitaryPair (1 : MatrixUnitary A b.Index) b.val)) := by
  apply congrArg K1.of
  apply congrArg FiniteUnitary.ofUnitary
  apply Subtype.ext
  rfl

variable {A B}
/-- Multiplication and block sum give the same stable K₁ class. -/
theorem k1_of_mul (a b : MatrixUnitary A ι) :
    K1.of (FiniteUnitary.ofUnitary (a * b)) =
      K1.of (FiniteUnitary.ofUnitary a) + K1.of (FiniteUnitary.ofUnitary b) := by
  calc
    _ = K1.of (FiniteUnitary.ofUnitary (unitaryBlockSum (a * b) 1)) :=
      (K1.of_stabilize (FiniteUnitary.ofUnitary (a * b)) ι).symm
    _ = K1.of (FiniteUnitary.ofUnitary (unitaryBlockSum a b)) :=
      (K1.of_homotopic (unitaryHomotopic_blockSum_mul a b)).symm
    _ = _ := rfl

variable (A B)

def k1ProductForward : K1 (A × B) →+ K1 A × K1 B :=
  (k1Map (StarAlgHom.fst ℂ A B)).prod (k1Map (StarAlgHom.snd ℂ A B))

def k1ProductInverse : K1 A × K1 B →+ K1 (A × B) :=
  (k1ProductInl A B).coprod (k1ProductInr A B)

theorem k1Product_leftInverse : Function.LeftInverse (k1ProductInverse A B) (k1ProductForward A B) := by
  intro x
  refine Quotient.inductionOn x ?_
  intro p
  change k1ProductInl A B (k1Map (StarAlgHom.fst ℂ A B) (K1.of p)) +
    k1ProductInr A B (k1Map (StarAlgHom.snd ℂ A B) (K1.of p)) = K1.of p
  rw [k1Map_of, k1Map_of, k1ProductInl_of, k1ProductInr_of, ← k1_of_mul]
  apply congrArg K1.of
  apply congrArg FiniteUnitary.ofUnitary
  apply Subtype.ext
  change matrixPair (matrixMap (StarAlgHom.fst ℂ A B) (p.val : CStarMatrix p.Index p.Index (A × B)))
      (1 : CStarMatrix p.Index p.Index B) *
    matrixPair (1 : CStarMatrix p.Index p.Index A)
      (matrixMap (StarAlgHom.snd ℂ A B) (p.val : CStarMatrix p.Index p.Index (A × B))) =
    (p.val : CStarMatrix p.Index p.Index (A × B))
  apply matrix_prod_ext <;>
    simp only [map_mul, matrixMap_fst_pair, matrixMap_snd_pair, one_mul, mul_one]

theorem k1Product_rightInverse : Function.RightInverse (k1ProductInverse A B) (k1ProductForward A B) := by
  rintro ⟨x,y⟩
  refine Quotient.inductionOn₂ x y ?_
  intro p q
  apply Prod.ext
  · change k1Map (StarAlgHom.fst ℂ A B) (k1ProductInl A B (K1.of p) + k1ProductInr A B (K1.of q)) = K1.of p
    rw [map_add, k1ProductInl_of, k1ProductInr_of, k1Map_of, k1Map_of]
    change K1.of (FiniteUnitary.ofUnitary (matrixUnitaryMap (StarAlgHom.fst ℂ A B) (unitaryPair p.val 1))) +
      K1.of (FiniteUnitary.ofUnitary (matrixUnitaryMap (StarAlgHom.fst ℂ A B) (unitaryPair 1 q.val))) = _
    rw [unitaryPair_fst, unitaryPair_fst]
    change K1.of p + K1.of (FiniteUnitary.identity q.Index) = K1.of p
    rw [K1.of_identity, add_zero]
  · change k1Map (StarAlgHom.snd ℂ A B) (k1ProductInl A B (K1.of p) + k1ProductInr A B (K1.of q)) = K1.of q
    rw [map_add, k1ProductInl_of, k1ProductInr_of, k1Map_of, k1Map_of]
    change K1.of (FiniteUnitary.ofUnitary (matrixUnitaryMap (StarAlgHom.snd ℂ A B) (unitaryPair p.val 1))) +
      K1.of (FiniteUnitary.ofUnitary (matrixUnitaryMap (StarAlgHom.snd ℂ A B) (unitaryPair 1 q.val))) = _
    rw [unitaryPair_snd, unitaryPair_snd]
    change K1.of (FiniteUnitary.identity p.Index) + K1.of q = K1.of q
    rw [K1.of_identity, zero_add]

/-- K₁ carries finite products to products of abelian groups. -/
def k1ProductEquiv : K1 (A × B) ≃+ K1 A × K1 B where
  toFun := k1ProductForward A B
  invFun := k1ProductInverse A B
  left_inv := k1Product_leftInverse A B
  right_inv := k1Product_rightInverse A B
  map_add' := map_add (k1ProductForward A B)

end BC4lean.OperatorKTheory
