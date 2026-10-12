import BC4lean.OddFredholmCompactUnitary
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-! # Actual polar normalization for invertible finite-cutoff approximants

The polar operator is `a (sqrt(a* a))⁻¹ʳ`, using the actual continuous functional
calculus and ring inverse. Its unitarity follows from actual invertibility.
It varies continuously on the open set of invertible elements and commutes
with unital star homomorphisms, including the full scalar quotient of a forced
unitization. These lemmas supply the analytic polar step of odd finite cutoff
reduction, without assuming an odd recovery isomorphism.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped Ring CStarAlgebra

variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- The actual polar operator, defined by genuine functional calculus. -/
def oddFredholmPolarElement (a : A) : A :=
  a * (CFC.sqrt (star a * a))⁻¹ʳ

theorem oddFredholmGramSqrt_isUnit (a : A) (ha : IsUnit a) :
    IsUnit (CFC.sqrt (star a * a)) :=
  (CFC.isUnit_sqrt_iff _ (star_mul_self_nonneg a)).mpr (ha.star.mul ha)

/-- The actual polar operator of an invertible element is genuinely unitary. -/
theorem oddFredholmPolarElement_mem_unitary (a : A) (ha : IsUnit a) :
    oddFredholmPolarElement a ∈ unitary A := by
  let s := CFC.sqrt (star a * a)
  have hs : IsUnit s := oddFredholmGramSqrt_isUnit a ha
  have hsa : IsSelfAdjoint s := (CFC.sqrt_nonneg _).isSelfAdjoint
  have hsquare : s * s = star a * a :=
    CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg a)
  have hpolar : IsUnit (oddFredholmPolarElement a) := ha.mul hs.ringInverse
  apply hpolar.mem_unitary_of_star_mul_self
  change star (a * s⁻¹ʳ) * (a * s⁻¹ʳ) = 1
  rw [star_mul, hsa.ringInverse.star_eq]
  calc
    s⁻¹ʳ * star a * (a * s⁻¹ʳ) = s⁻¹ʳ * (star a * a) * s⁻¹ʳ := by
      simp only [mul_assoc]
    _ = s⁻¹ʳ * (s * s) * s⁻¹ʳ := by rw [hsquare]
    _ = 1 := by
      rw [← mul_assoc s⁻¹ʳ s s, Ring.inverse_mul_cancel s hs,
        one_mul, Ring.mul_inverse_cancel s hs]

/-- Bundle the actual unitary polar correction. -/
def oddFredholmPolarUnitary (a : A) (ha : IsUnit a) : unitary A :=
  ⟨oddFredholmPolarElement a, oddFredholmPolarElement_mem_unitary a ha⟩

@[simp] theorem oddFredholmPolarElement_one : oddFredholmPolarElement (1 : A) = 1 := by
  simp [oddFredholmPolarElement]

@[simp] theorem oddFredholmPolarElement_unitary (U : unitary A) :
    oddFredholmPolarElement (U : A) = U := by
  simp [oddFredholmPolarElement]

/-- The positive Gram square root varies continuously even at nonunits. -/
theorem continuous_oddFredholmGramSqrt :
    Continuous (fun a : A => CFC.sqrt (star a * a)) :=
  CFC.continuousOn_sqrt.comp_continuous (continuous_star.mul continuous_id)
    (fun a => star_mul_self_nonneg a)

/-- Polar correction is norm-continuous on the actual open set of invertible
elements. No arbitrary choice of unitary approximants is made. -/
theorem continuousOn_oddFredholmPolarElement :
    ContinuousOn oddFredholmPolarElement {a : A | IsUnit a} := by
  intro a ha
  have hs := oddFredholmGramSqrt_isUnit a ha
  obtain ⟨v, hv⟩ := hs
  have hinv : ContinuousAt Ring.inverse (CFC.sqrt (star a * a)) := by
    simpa only [hv] using NormedRing.inverse_continuousAt v
  have hInvGram : ContinuousAt
      (fun b : A => (CFC.sqrt (star b * b))⁻¹ʳ) a :=
    hinv.comp (f := fun b : A => CFC.sqrt (star b * b)) (x := a)
      continuous_oddFredholmGramSqrt.continuousAt
  exact (continuousAt_id.mul hInvGram).continuousWithinAt

/-- A genuine norm-continuous path of invertible approximants polar-normalizes
to an actual unitary path. -/
def oddFredholmPolarUnitaryPath {a b : A} (p : Path a b)
    (hp : ∀ t, IsUnit (p t)) :
    Path (oddFredholmPolarUnitary a (by simpa only [Path.source] using hp 0))
      (oddFredholmPolarUnitary b (by simpa only [Path.target] using hp 1)) where
  toFun t := oddFredholmPolarUnitary (p t) (hp t)
  continuous_toFun :=
    (continuousOn_oddFredholmPolarElement.comp_continuous p.continuous hp).subtype_mk _
  source' := by simp only [Path.source]
  target' := by simp only [Path.target]

/-- Unital star homomorphisms preserve the actual Gram square root. -/
theorem oddFredholmGramSqrt_map (φ : A →⋆ₐ[ℂ] C) (a : A) :
    φ (CFC.sqrt (star a * a)) = CFC.sqrt (star (φ a) * φ a) := by
  have hφ : Continuous φ :=
    AddMonoidHomClass.continuous_of_bound φ 1 (fun b => by
      simpa only [one_mul] using
        NonUnitalStarAlgHom.norm_apply_le φ b)
  rw [CFC.sqrt_eq_cfc, CFC.sqrt_eq_cfc]
  rw [φ.map_cfc (R := NNReal) NNReal.sqrt (star a * a)
    NNReal.continuous_sqrt.continuousOn hφ
    (star_mul_self_nonneg a) (by
      rw [map_mul, map_star]
      exact star_mul_self_nonneg (φ a)), map_mul, map_star]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder C] [StarOrderedRing C] in
/-- Ring inverse commutes with a unital homomorphism at each actual unit. -/
theorem oddFredholmRingInverse_map (φ : A →⋆ₐ[ℂ] C) (a : A) (ha : IsUnit a) :
    φ a⁻¹ʳ = (φ a)⁻¹ʳ := by
  have hφ : IsUnit (φ a) := ha.map φ.toMonoidHom
  calc
    φ a⁻¹ʳ = (φ a)⁻¹ʳ * (φ a * φ a⁻¹ʳ) := by
      rw [← mul_assoc, Ring.inverse_mul_cancel (φ a) hφ, one_mul]
    _ = (φ a)⁻¹ʳ := by
      rw [← map_mul, Ring.mul_inverse_cancel a ha, map_one, mul_one]

/-- Polar normalization preserves every full scalar matrix quotient, by actual
functional-calculus and inverse functoriality. -/
theorem oddFredholmPolarElement_map (φ : A →⋆ₐ[ℂ] C) (a : A) (ha : IsUnit a) :
    φ (oddFredholmPolarElement a) = oddFredholmPolarElement (φ a) := by
  rw [oddFredholmPolarElement, map_mul,
    oddFredholmRingInverse_map φ _ (oddFredholmGramSqrt_isUnit a ha),
    oddFredholmGramSqrt_map, oddFredholmPolarElement]

theorem oddFredholmPolarElement_scalar_one
    (φ : A →⋆ₐ[ℂ] C) (a : A) (ha : IsUnit a) (hScalar : φ a = 1) :
    φ (oddFredholmPolarElement a) = 1 := by
  rw [oddFredholmPolarElement_map φ a ha, hScalar, oddFredholmPolarElement_one]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Every actual unitary has a radius-one invertible neighborhood. This is the
concrete analytic criterion used after the compact finite-coordinate cutoff. -/
theorem oddFredholmIsUnit_of_norm_sub_unitary_lt_one [Nontrivial A]
    (a : A) (U : unitary A) (h : ‖a - (U : A)‖ < 1) : IsUnit a := by
  let v := Unitary.toUnits U
  have hv : ‖(↑v⁻¹ : A)‖ = 1 := by
    change ‖star (U : A)‖ = 1
    rw [norm_star, CStarRing.norm_coe_unitary]
  have hNearby : ‖a - (v : A)‖ < ‖(↑v⁻¹ : A)‖⁻¹ := by
    rw [hv, inv_one]
    change ‖a - (U : A)‖ < 1
    exact h
  exact (v.ofNearby a hNearby).isUnit

end BC4lean.KKTheory
