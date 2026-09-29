import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Star.StarProjection

/-! # Projections and Murray–von Neumann equivalence

Projection-level foundations for operator K₀. The two support equations for
partial isometries are consequences of the C⋆-identity, not extra assumptions.
-/

noncomputable section
namespace BC4lean.OperatorKTheory

variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

/-- A projection in a unital complex C⋆-algebra. -/
abbrev Projection (A : Type*) [CStarAlgebra A] := {p : A // IsStarProjection p}

namespace Projection

@[simp] theorem star_coe (p : Projection A) : star (p : A) = p :=
  p.property.isSelfAdjoint.star_eq

@[simp] theorem mul_self (p : Projection A) : (p : A) * p = p :=
  p.property.isIdempotentElem.eq

def zero : Projection A := ⟨0, IsStarProjection.zero A⟩
def one : Projection A := ⟨1, IsStarProjection.one A⟩
def complement (p : Projection A) : Projection A := ⟨1 - p, p.property.one_sub⟩

def map (φ : A →⋆ₐ[ℂ] B) (p : Projection A) : Projection B :=
  ⟨φ p, p.property.map φ⟩

@[simp] theorem map_coe (φ : A →⋆ₐ[ℂ] B) (p : Projection A) :
    (map φ p : B) = φ p := rfl

@[simp] theorem map_id (p : Projection A) : map (StarAlgHom.id ℂ A) p = p := rfl

@[simp] theorem map_comp (ψ : B →⋆ₐ[ℂ] C) (φ : A →⋆ₐ[ℂ] B) (p : Projection A) :
    map (ψ.comp φ) p = map ψ (map φ p) := rfl

@[simp] theorem map_zero (φ : A →⋆ₐ[ℂ] B) : map φ zero = zero :=
  Subtype.ext (_root_.map_zero φ)

@[simp] theorem map_one (φ : A →⋆ₐ[ℂ] B) : map φ one = one :=
  Subtype.ext (_root_.map_one φ)

/-- The initial projection acts as the right support of a partial isometry. -/
theorem right_support (p : Projection A) (v : A) (hv : star v * v = p) : v * p = v := by
  apply sub_eq_zero.mp
  apply (CStarRing.star_mul_self_eq_zero_iff (v * p - v)).mp
  have h₁ : star v * (v * p) = p := by rw [← mul_assoc, hv, mul_self]
  simp only [star_sub, star_mul, star_coe, sub_mul, mul_sub, mul_assoc, h₁, hv,
    mul_self, sub_self]

/-- Equivalence implemented by the usual two partial-isometry equations. -/
def Equivalent (p q : Projection A) : Prop :=
  ∃ v : A, star v * v = p ∧ v * star v = q

theorem equivalent_refl (p : Projection A) : Equivalent p p :=
  ⟨p, by simp, by simp⟩

theorem equivalent_symm {p q : Projection A} (h : Equivalent p q) : Equivalent q p := by
  obtain ⟨v, hv, hv'⟩ := h
  exact ⟨star v, by simpa using hv', by simpa using hv⟩

theorem equivalent_trans {p q r : Projection A}
    (hpq : Equivalent p q) (hqr : Equivalent q r) : Equivalent p r := by
  obtain ⟨v, hv, hv'⟩ := hpq
  obtain ⟨w, hw, hw'⟩ := hqr
  have hvp := right_support p v hv
  have hqv : (q : A) * v = v := by rw [← hv', mul_assoc, hv, hvp]
  have hwq := right_support q w hw
  refine ⟨w * v, ?_, ?_⟩
  · calc
      star (w * v) * (w * v) = star v * (star w * w) * v := by simp only [star_mul, mul_assoc]
      _ = star v * q * v := by rw [hw]
      _ = p := by rw [mul_assoc, hqv, hv]
  · calc
      (w * v) * star (w * v) = w * (v * star v) * star w := by simp only [star_mul, mul_assoc]
      _ = w * q * star w := by rw [hv']
      _ = r := by rw [hwq, hw']

/-- Equivalence classes at a fixed algebra, in particular a fixed matrix size. -/
def equivalenceSetoid : Setoid (Projection A) where
  r := Equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

abbrev Classes (A : Type*) [CStarAlgebra A] := Quotient (equivalenceSetoid (A := A))

theorem equivalent_map (φ : A →⋆ₐ[ℂ] B) {p q : Projection A}
    (h : Equivalent p q) : Equivalent (map φ p) (map φ q) := by
  obtain ⟨v, hv, hv'⟩ := h
  refine ⟨φ v, ?_, ?_⟩
  · simpa only [map_mul, map_star, map_coe] using congrArg φ hv
  · simpa only [map_mul, map_star, map_coe] using congrArg φ hv'

def mapClasses (φ : A →⋆ₐ[ℂ] B) : Classes A → Classes B :=
  Quotient.map (map φ) (fun _ _ h => equivalent_map φ h)

@[simp] theorem mapClasses_mk (φ : A →⋆ₐ[ℂ] B) (p : Projection A) :
    mapClasses φ (Quotient.mk _ p) = Quotient.mk _ (map φ p) := rfl

end Projection
end BC4lean.OperatorKTheory
