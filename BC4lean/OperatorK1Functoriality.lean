import BC4lean.StableUnitary
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-! # Functoriality of the stable unitary quotient -/
noncomputable section
open scoped CStarAlgebra
namespace BC4lean.OperatorKTheory
universe u v w
variable {A : Type u} {B : Type v} {C : Type w}
variable [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
variable [PartialOrder C] [StarOrderedRing C]
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def matrixUnitaryMap (φ : A →⋆ₐ[ℂ] B) (a : MatrixUnitary A ι) : MatrixUnitary B ι :=
  ⟨matrixMap φ a, Unitary.map_mem (matrixMap φ) a.property⟩

@[simp] theorem matrixUnitaryMap_apply (φ : A →⋆ₐ[ℂ] B) (a : MatrixUnitary A ι) (i j : ι) :
    (matrixUnitaryMap φ a : CStarMatrix ι ι B) i j = φ ((a : CStarMatrix ι ι A) i j) := rfl

theorem continuous_matrixUnitaryMap (φ : A →⋆ₐ[ℂ] B) :
    Continuous (matrixUnitaryMap (ι := ι) φ) :=
  ((map_continuous (matrixMap φ)).comp continuous_subtype_val).subtype_mk _

@[simp] theorem matrixUnitaryMap_one (φ : A →⋆ₐ[ℂ] B) :
    matrixUnitaryMap φ (1 : MatrixUnitary A ι) = 1 := by
  apply Subtype.ext
  exact map_one (matrixMap φ)

@[simp] theorem matrixUnitaryMap_blockSum (φ : A →⋆ₐ[ℂ] B)
    (a : MatrixUnitary A ι) (b : MatrixUnitary A κ) :
    matrixUnitaryMap φ (unitaryBlockSum a b) =
      unitaryBlockSum (matrixUnitaryMap φ a) (matrixUnitaryMap φ b) := by
  apply Subtype.ext
  ext i j
  cases i <;> cases j <;> simp [unitaryBlockSum, matrixBlockSum, Matrix.fromBlocks, matrixUnitaryMap_apply]

@[simp] theorem matrixUnitaryMap_reindex (φ : A →⋆ₐ[ℂ] B) (e : ι ≃ κ) (a : MatrixUnitary A ι) :
    matrixUnitaryMap φ (unitaryReindex e a) = unitaryReindex e (matrixUnitaryMap φ a) := by
  apply Subtype.ext
  rfl

theorem unitaryHomotopic_map (φ : A →⋆ₐ[ℂ] B) {a b : MatrixUnitary A ι}
    (h : UnitaryHomotopic a b) : UnitaryHomotopic (matrixUnitaryMap φ a) (matrixUnitaryMap φ b) :=
  h.map (continuous_matrixUnitaryMap φ)

namespace FiniteUnitary

abbrev map (φ : A →⋆ₐ[ℂ] B) (a : FiniteUnitary A) : FiniteUnitary B :=
  ofUnitary (matrixUnitaryMap φ a.val)

@[simp] theorem map_identity (φ : A →⋆ₐ[ℂ] B) (ι : Type) [Fintype ι] [DecidableEq ι] :
    map φ (identity ι) = identity ι := by
  change ofUnitary (matrixUnitaryMap φ 1) = ofUnitary 1
  rw [matrixUnitaryMap_one]

@[simp] theorem map_blockSum (φ : A →⋆ₐ[ℂ] B) (a b : FiniteUnitary A) :
    map φ (blockSum a b) = blockSum (map φ a) (map φ b) := by
  change ofUnitary (matrixUnitaryMap φ (unitaryBlockSum a.val b.val)) = _
  rw [matrixUnitaryMap_blockSum]

theorem equivalent_map (φ : A →⋆ₐ[ℂ] B) {a b : FiniteUnitary A} (h : Equivalent a b) :
    Equivalent (map φ a) (map φ b) := by
  induction h with
  | refl a => exact equivalent_refl _
  | symm a b h ih => exact equivalent_symm ih
  | trans a b c h k ih ik => exact equivalent_trans ih ik
  | rel a b h =>
    cases h with
    | homotopy b e h =>
      apply Relation.EqvGen.rel
      apply Move.homotopy (map φ a) (map φ b) e
      simpa only [map, ofUnitary, matrixUnitaryMap_reindex] using unitaryHomotopic_map φ h
    | stabilize κ =>
      rw [map_blockSum, map_identity]
      exact equivalent_stabilize _ κ

@[simp] theorem map_id (a : FiniteUnitary A) : map (StarAlgHom.id ℂ A) a = a := by
  cases a
  rfl

@[simp] theorem map_comp (ψ : B →⋆ₐ[ℂ] C) (φ : A →⋆ₐ[ℂ] B) (a : FiniteUnitary A) :
    map (ψ.comp φ) a = map ψ (map φ a) := rfl
end FiniteUnitary

def k1Map (φ : A →⋆ₐ[ℂ] B) : K1 A →+ K1 B where
  toFun := Quotient.map (FiniteUnitary.map φ) (fun _ _ h => FiniteUnitary.equivalent_map φ h)
  map_zero' := by
    change K1.of (FiniteUnitary.map φ (FiniteUnitary.identity Empty)) = _
    rw [FiniteUnitary.map_identity]
    rfl
  map_add' a b := by
    refine Quotient.inductionOn₂ a b ?_
    intro a b
    change K1.of (FiniteUnitary.map φ (FiniteUnitary.blockSum a b)) = _
    rw [FiniteUnitary.map_blockSum]
    rfl

@[simp] theorem k1Map_of (φ : A →⋆ₐ[ℂ] B) (a : FiniteUnitary A) :
    k1Map φ (K1.of a) = K1.of (FiniteUnitary.map φ a) := rfl

@[simp] theorem k1Map_id : k1Map (StarAlgHom.id ℂ A) = AddMonoidHom.id (K1 A) := by
  ext x
  refine Quotient.inductionOn x ?_
  intro a
  exact congrArg K1.of (FiniteUnitary.map_id a)

@[simp] theorem k1Map_comp (ψ : B →⋆ₐ[ℂ] C) (φ : A →⋆ₐ[ℂ] B) :
    k1Map (ψ.comp φ) = (k1Map ψ).comp (k1Map φ) := by
  ext x
  refine Quotient.inductionOn x ?_
  intro a
  rfl

end BC4lean.OperatorKTheory
