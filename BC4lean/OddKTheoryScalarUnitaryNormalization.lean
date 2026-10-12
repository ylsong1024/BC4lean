import BC4lean.NonunitalOperatorK
import BC4lean.OperatorK1Product
import BC4lean.OddFredholmOperatorK1Index

/-! # Actual full scalar-identity representatives of OperatorK1

Multiply u by the adjoint of the actual lift of its scalar matrix. The full
scalar matrix becomes I. The actual K1 multiplication path and the scalar
kernel equation prove that the corrected unitary represents the same element.
No computation of K1(ℂ), logarithm, Bott theorem or quotient identification is
assumed. This correction is continuous and respects finite block operations.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped CStarAlgebra
open BC4lean.OperatorKTheory

namespace OddKTheoryUniverseSupport
open BC4lean.OperatorKTheory

universe uA uD uF uI uJ uR uS
variable {A : Type uA} {D : Type uD} {F : Type uF}
  [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra F]
  [PartialOrder A] [StarOrderedRing A]
  [PartialOrder D] [StarOrderedRing D]
  [PartialOrder F] [StarOrderedRing F]
variable {ι : Type uI} {κ : Type uJ} {ρ : Type uR} {σ : Type uS}
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ρ] [DecidableEq ρ] [Fintype σ] [DecidableEq σ]

/-- The old entrywise unitary map, with its original mathematical data and
arbitrary independent finite-index universe. -/
def generalMap (φ : A →⋆ₐ[ℂ] D) (a : MatrixUnitary A ι) : MatrixUnitary D ι :=
  ⟨matrixMap (A := A) (B := D) (ι := ι) φ (a : CStarMatrix ι ι A),
    Unitary.map_mem (matrixMap (A := A) (B := D) (ι := ι) φ) a.property⟩

@[simp] theorem generalMap_apply (φ : A →⋆ₐ[ℂ] D)
    (a : MatrixUnitary A ι) (i j : ι) :
    (generalMap φ a : CStarMatrix ι ι D) i j = φ ((a : CStarMatrix ι ι A) i j) := rfl

theorem continuous_generalMap (φ : A →⋆ₐ[ℂ] D) : Continuous (generalMap (ι := ι) φ) :=
  ((map_continuous (matrixMap (A := A) (B := D) (ι := ι) φ)).comp continuous_subtype_val).subtype_mk _

@[simp] theorem generalMap_one (φ : A →⋆ₐ[ℂ] D) :
    generalMap φ (1 : MatrixUnitary A ι) = 1 :=
  Subtype.ext (map_one (matrixMap φ))

theorem generalMap_mul (φ : A →⋆ₐ[ℂ] D) (a b : MatrixUnitary A ι) :
    generalMap φ (a * b) = generalMap φ a * generalMap φ b :=
  Subtype.ext (map_mul (matrixMap φ) (a : CStarMatrix ι ι A) (b : CStarMatrix ι ι A))

theorem generalMap_star (φ : A →⋆ₐ[ℂ] D) (a : MatrixUnitary A ι) :
    generalMap φ (star a) = star (generalMap φ a) :=
  Subtype.ext (map_star (matrixMap φ) (a : CStarMatrix ι ι A))

theorem generalMap_comp (ψ : D →⋆ₐ[ℂ] F) (φ : A →⋆ₐ[ℂ] D)
    (a : MatrixUnitary A ι) :
    generalMap (ψ.comp φ) a = generalMap ψ (generalMap φ a) := by
  apply Subtype.ext
  rfl

theorem generalMap_id (a : MatrixUnitary A ι) : generalMap (StarAlgHom.id ℂ A) a = a := by
  apply Subtype.ext
  rfl

theorem generalMap_blockSum (φ : A →⋆ₐ[ℂ] D)
    (a : MatrixUnitary A ι) (b : MatrixUnitary A κ) :
    generalMap φ (unitaryBlockSum a b) =
      unitaryBlockSum (generalMap φ a) (generalMap φ b) := by
  apply Subtype.ext
  ext i j
  cases i <;> cases j
  · rfl
  · change φ 0 = 0
    exact map_zero φ
  · change φ 0 = 0
    exact map_zero φ
  · rfl

/-- The established arbitrary-universe CStarMatrix star algebra equivalence
restricts to the same genuine unitary reindexing as the old Type0 helper. -/
def generalReindex (e : ι ≃ κ) (a : MatrixUnitary A ι) : MatrixUnitary A κ :=
  ⟨CStarMatrix.reindexₐ ℂ A e (a : CStarMatrix ι ι A), Unitary.map_mem (CStarMatrix.reindexₐ ℂ A e) a.property⟩

@[simp] theorem generalReindex_apply (e : ι ≃ κ) (a : MatrixUnitary A ι) (i j : κ) :
    (generalReindex e a : CStarMatrix κ κ A) i j =
      (a : CStarMatrix ι ι A) (e.symm i) (e.symm j) := rfl

theorem generalReindex_mul (e : ι ≃ κ) (a b : MatrixUnitary A ι) :
    generalReindex e (a * b) = generalReindex e a * generalReindex e b :=
  Subtype.ext (map_mul (CStarMatrix.reindexₐ ℂ A e)
    (a : CStarMatrix ι ι A) (b : CStarMatrix ι ι A))

theorem generalReindex_star (e : ι ≃ κ) (a : MatrixUnitary A ι) :
    generalReindex e (star a) = star (generalReindex e a) :=
  Subtype.ext (map_star (CStarMatrix.reindexₐ ℂ A e) (a : CStarMatrix ι ι A))

theorem generalReindex_trans (e : ι ≃ κ) (f : κ ≃ ρ) (a : MatrixUnitary A ι) :
    generalReindex (e.trans f) a = generalReindex f (generalReindex e a) := by
  apply Subtype.ext
  rfl

theorem generalReindex_blockSum (e : ι ≃ κ) (f : ρ ≃ σ)
    (a : MatrixUnitary A ι) (b : MatrixUnitary A ρ) :
    generalReindex (e.sumCongr f) (unitaryBlockSum a b) =
      unitaryBlockSum (generalReindex e a) (generalReindex f b) := by
  apply Subtype.ext
  ext i j
  cases i <;> cases j <;> rfl

theorem generalMap_reindex (φ : A →⋆ₐ[ℂ] D) (e : ι ≃ κ) (a : MatrixUnitary A ι) :
    generalMap φ (generalReindex e a) = generalReindex e (generalMap φ a) := by
  apply Subtype.ext
  rfl

/-- The actual old K1 quotient class of an arbitrary-universe finite matrix.
All matrix entries are retained; only genuine coordinates change. -/
def unitaryK1Class (a : MatrixUnitary A ι) : K1 A :=
  K1.of (FiniteUnitary.ofUnitary (generalReindex (Fintype.equivFin ι) a))

section SmallIndices
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem small_class_reindex (e : α ≃ β) (a : MatrixUnitary A α) :
    K1.of (FiniteUnitary.ofUnitary (unitaryReindex e a)) =
      K1.of (FiniteUnitary.ofUnitary a) :=
  (Quotient.sound (FiniteUnitary.equivalent_reindex
    (FiniteUnitary.ofUnitary a) (FiniteUnitary.ofUnitary (unitaryReindex e a)) e rfl)).symm

theorem generalReindex_small (e : α ≃ β) (a : MatrixUnitary A α) :
    generalReindex e a = unitaryReindex e a := rfl

theorem generalMap_small (φ : A →⋆ₐ[ℂ] D) (a : MatrixUnitary A α) :
    generalMap φ a = matrixUnitaryMap φ a := rfl

/-- The generalized class is exactly the old native class when that expression
is already well typed. This is the conversion needed by existing callers. -/
theorem unitaryK1Class_small (a : MatrixUnitary A α) :
    unitaryK1Class a = K1.of (FiniteUnitary.ofUnitary a) := by
  change K1.of (FiniteUnitary.ofUnitary (unitaryReindex (Fintype.equivFin α) a)) = _
  exact small_class_reindex (Fintype.equivFin α) a
end SmallIndices

/-- Any genuine enumeration into any old finite Type0 index computes the same
actual K1 class. In particular the canonical Fin enumeration is not assumed
to intertwine arbitrary coordinate changes definitionally. -/
theorem unitaryK1Class_of_small_equiv {α : Type} [Fintype α] [DecidableEq α]
    (e : ι ≃ α) (a : MatrixUnitary A ι) :
    unitaryK1Class a = K1.of (FiniteUnitary.ofUnitary (generalReindex e a)) := by
  let e₀ : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let q : Fin (Fintype.card ι) ≃ α := e₀.symm.trans e
  have h : unitaryReindex q (generalReindex e₀ a) = generalReindex e a := by
    apply Subtype.ext
    ext i j
    change (a : CStarMatrix ι ι A) (e₀.symm (q.symm i)) (e₀.symm (q.symm j)) =
      (a : CStarMatrix ι ι A) (e.symm i) (e.symm j)
    simp only [q, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  change K1.of (FiniteUnitary.ofUnitary (generalReindex e₀ a)) = _
  rw [← h]
  exact (small_class_reindex q (generalReindex e₀ a)).symm

theorem unitaryK1Class_enumeration_independent
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : ι ≃ α) (f : ι ≃ β) (a : MatrixUnitary A ι) :
    K1.of (FiniteUnitary.ofUnitary (generalReindex e a)) =
      K1.of (FiniteUnitary.ofUnitary (generalReindex f a)) :=
  (unitaryK1Class_of_small_equiv e a).symm.trans (unitaryK1Class_of_small_equiv f a)

theorem unitaryK1Class_reindex (e : ι ≃ κ) (a : MatrixUnitary A ι) :
    unitaryK1Class (generalReindex e a) = unitaryK1Class a := by
  change K1.of (FiniteUnitary.ofUnitary
    (generalReindex (Fintype.equivFin κ) (generalReindex e a))) = unitaryK1Class a
  rw [← generalReindex_trans]
  exact (unitaryK1Class_of_small_equiv (e.trans (Fintype.equivFin κ)) a).symm

theorem unitaryK1Class_map (φ : A →⋆ₐ[ℂ] D) (a : MatrixUnitary A ι) :
    k1Map φ (unitaryK1Class a) = unitaryK1Class (generalMap φ a) := by
  change K1.of (FiniteUnitary.ofUnitary
    (matrixUnitaryMap φ (generalReindex (Fintype.equivFin ι) a))) =
      K1.of (FiniteUnitary.ofUnitary
        (generalReindex (Fintype.equivFin ι) (generalMap φ a)))
  rfl

theorem unitaryK1Class_mul (a b : MatrixUnitary A ι) :
    unitaryK1Class (a * b) = unitaryK1Class a + unitaryK1Class b := by
  unfold unitaryK1Class
  rw [generalReindex_mul]
  exact k1_of_mul _ _

theorem unitaryK1Class_star (a : MatrixUnitary A ι) :
    unitaryK1Class (star a) = -unitaryK1Class a := by
  unfold unitaryK1Class
  rw [generalReindex_star]
  rfl

theorem unitaryK1Class_blockSum (a : MatrixUnitary A ι) (b : MatrixUnitary A κ) :
    unitaryK1Class (unitaryBlockSum a b) = unitaryK1Class a + unitaryK1Class b := by
  let e := (Fintype.equivFin ι).sumCongr (Fintype.equivFin κ)
  calc
    unitaryK1Class (unitaryBlockSum a b) =
        K1.of (FiniteUnitary.ofUnitary (generalReindex e (unitaryBlockSum a b))) :=
      unitaryK1Class_of_small_equiv e _
    _ = K1.of (FiniteUnitary.ofUnitary
        (unitaryBlockSum (generalReindex (Fintype.equivFin ι) a)
          (generalReindex (Fintype.equivFin κ) b))) := by
      rw [generalReindex_blockSum]
    _ = unitaryK1Class a + unitaryK1Class b := rfl

end OddKTheoryUniverseSupport

open OddKTheoryUniverseSupport

variable {B ι κ : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
local instance oddContinuationOddKTheoryScalarUnitaryNormalizationLocalInstance01 : PartialOrder (Unitization ℂ B) := CStarAlgebra.spectralOrder _
local instance oddContinuationOddKTheoryScalarUnitaryNormalizationLocalInstance02 : StarOrderedRing (Unitization ℂ B) := CStarAlgebra.spectralOrderedRing _
local instance oddContinuationOddKTheoryScalarUnitaryNormalizationLocalInstance03 : PartialOrder ℂ := CStarAlgebra.spectralOrder _
local instance oddContinuationOddKTheoryScalarUnitaryNormalizationLocalInstance04 : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing _

def oddKTheoryScalarNormalizedUnitary
    (u : MatrixUnitary (Unitization ℂ B) ι) : MatrixUnitary (Unitization ℂ B) ι :=
  u * star (generalMap (scalarSection B) (generalMap (scalarQuotient B) u))

omit [PartialOrder B] [StarOrderedRing B] in
theorem continuous_oddKTheoryScalarNormalizedUnitary
    [PartialOrder B] [StarOrderedRing B] :
    Continuous (oddKTheoryScalarNormalizedUnitary (B := B) (ι := ι)) :=
  continuous_id.mul (((continuous_generalMap (scalarSection B)).comp
    (continuous_generalMap (scalarQuotient B))).star)

omit [PartialOrder B] [StarOrderedRing B] in
theorem oddKTheoryScalarSectionUnitary (w : MatrixUnitary ℂ ι) :
    generalMap (scalarQuotient B) (generalMap (scalarSection B) w) = w := by
  rw [← generalMap_comp, scalarQuotient_section, generalMap_id]

omit [PartialOrder B] [StarOrderedRing B] in
theorem oddKTheoryScalarNormalizedUnitary_scalar
    [PartialOrder B] [StarOrderedRing B]
    (u : MatrixUnitary (Unitization ℂ B) ι) :
    unitizationScalarMatrix (oddKTheoryScalarNormalizedUnitary u :
      CStarMatrix ι ι (Unitization ℂ B)) = 1 := by
  have h : generalMap (scalarQuotient B) (oddKTheoryScalarNormalizedUnitary u) = 1 := by
    unfold oddKTheoryScalarNormalizedUnitary
    rw [generalMap_mul, generalMap_star, oddKTheoryScalarSectionUnitary]
    exact Unitary.mul_star_self _
  exact congrArg Subtype.val h

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem oddKTheoryScalarNormalizedUnitary_one
    [PartialOrder B] [StarOrderedRing B] :
    oddKTheoryScalarNormalizedUnitary (1 : MatrixUnitary (Unitization ℂ B) ι) = 1 := by
  rw [oddKTheoryScalarNormalizedUnitary, generalMap_one, generalMap_one, star_one, one_mul]

omit [PartialOrder B] [StarOrderedRing B] in
theorem oddKTheoryScalarNormalizedUnitary_of_scalarIdentity
    [PartialOrder B] [StarOrderedRing B]
    (u : MatrixUnitary (Unitization ℂ B) ι)
    (hu : unitizationScalarMatrix (u : CStarMatrix ι ι (Unitization ℂ B)) = 1) :
    oddKTheoryScalarNormalizedUnitary u = u := by
  have hs : generalMap (scalarQuotient B) u = 1 := Subtype.ext hu
  rw [oddKTheoryScalarNormalizedUnitary, hs, generalMap_one, star_one, mul_one]

omit [PartialOrder B] [StarOrderedRing B] in
theorem oddKTheoryScalarNormalizedUnitary_blockSum
    [PartialOrder B] [StarOrderedRing B]
    (u : MatrixUnitary (Unitization ℂ B) ι) (v : MatrixUnitary (Unitization ℂ B) κ) :
    oddKTheoryScalarNormalizedUnitary (unitaryBlockSum u v) =
      unitaryBlockSum (oddKTheoryScalarNormalizedUnitary u) (oddKTheoryScalarNormalizedUnitary v) := by
  unfold oddKTheoryScalarNormalizedUnitary
  rw [generalMap_blockSum, generalMap_blockSum]
  apply Subtype.ext
  change matrixBlockSum (u : CStarMatrix ι ι (Unitization ℂ B))
      (v : CStarMatrix κ κ (Unitization ℂ B)) *
      star (matrixBlockSum
        (generalMap (scalarSection B) (generalMap (scalarQuotient B) u) :
          CStarMatrix ι ι (Unitization ℂ B))
        (generalMap (scalarSection B) (generalMap (scalarQuotient B) v) :
          CStarMatrix κ κ (Unitization ℂ B))) = _
  rw [matrixBlockSum_star, matrixBlockSum_mul]
  rfl

omit [PartialOrder B] [StarOrderedRing B] in
theorem oddKTheoryScalarNormalizedUnitary_reindex
    [PartialOrder B] [StarOrderedRing B] (e : ι ≃ κ) (u : MatrixUnitary (Unitization ℂ B) ι) :
    oddKTheoryScalarNormalizedUnitary (generalReindex e u) = generalReindex e (oddKTheoryScalarNormalizedUnitary u) := by
  unfold oddKTheoryScalarNormalizedUnitary
  rw [generalMap_reindex, generalMap_reindex, generalReindex_mul, generalReindex_star]

omit [PartialOrder B] [StarOrderedRing B] in
/-- This is the honest arbitrary-universe correction of the old ill-typed
ofUnitary expressions. The hypotheses and conclusion refer to the same actual
native K1 class after genuine finite-coordinate transport. -/
theorem oddKTheoryScalarNormalizedUnitary_k1
    [PartialOrder B] [StarOrderedRing B] (u : MatrixUnitary (Unitization ℂ B) ι)
    (hu : k1Map (scalarQuotient B) (unitaryK1Class u) = 0) :
    unitaryK1Class (oddKTheoryScalarNormalizedUnitary u) = unitaryK1Class u := by
  unfold oddKTheoryScalarNormalizedUnitary
  rw [unitaryK1Class_mul, unitaryK1Class_star]
  have he : unitaryK1Class
      (generalMap (scalarSection B) (generalMap (scalarQuotient B) u)) = 0 := by
    rw [← unitaryK1Class_map, ← unitaryK1Class_map, hu, map_zero]
  rw [he, neg_zero, add_zero]

omit [PartialOrder B] [StarOrderedRing B] in
/-- Small-index native formulation: exactly the original native K1 theorem. -/
theorem oddKTheoryScalarNormalizedUnitary_k1_small
    [PartialOrder B] [StarOrderedRing B] {α : Type} [Fintype α] [DecidableEq α]
    (u : MatrixUnitary (Unitization ℂ B) α)
    (hu : k1Map (scalarQuotient B) (K1.of (FiniteUnitary.ofUnitary u)) = 0) :
    K1.of (FiniteUnitary.ofUnitary (oddKTheoryScalarNormalizedUnitary u)) = K1.of (FiniteUnitary.ofUnitary u) := by
  have hs : k1Map (scalarQuotient B) (unitaryK1Class u) = 0 := by
    rw [unitaryK1Class_small]
    exact hu
  simpa only [unitaryK1Class_small] using oddKTheoryScalarNormalizedUnitary_k1 u hs

omit [PartialOrder B] [StarOrderedRing B] in
/-- Final conclusion remains the project's actual nonunital OperatorK1 and
original ordinary Fin-indexed representative, not a replacement quotient. -/
theorem oddKTheoryOperatorK1_exists_scalarIdentityRepresentative
    [PartialOrder B] [StarOrderedRing B] (x : OperatorK1 B) :
    ∃ (n : ℕ) (u : MatrixUnitary (Unitization ℂ B) (Fin n))
      (hu : unitizationScalarMatrix (u : CStarMatrix (Fin n) (Fin n) (Unitization ℂ B)) = 1),
      oddFredholmScalarIdentityUnitaryIndex u hu = x := by
  obtain ⟨n, v, hv⟩ := K1.exists_finRepresentative x.val
  have hs : k1Map (scalarQuotient B) (K1.of (FiniteUnitary.ofUnitary v)) = 0 := by
    rw [hv]
    exact x.property
  refine ⟨n, oddKTheoryScalarNormalizedUnitary v, oddKTheoryScalarNormalizedUnitary_scalar v, ?_⟩
  apply Subtype.ext
  exact (oddKTheoryScalarNormalizedUnitary_k1_small v hs).trans hv

end BC4lean.KKTheory
