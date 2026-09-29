import BC4lean.OperatorProjections
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Tactic.NoncommRing

/-! # Norm homotopies of projections preserve Murray–von Neumann classes -/
noncomputable section
open Filter Topology
namespace BC4lean.OperatorKTheory
namespace Projection
variable {A : Type*} [CStarAlgebra A]

/-- An invertible intertwiner between projections can be normalized to a partial isometry. -/
theorem equivalent_of_invertible_intertwiner (p q : Projection A) (s : A)
    (hs : IsUnit s) (hsp : s * p = q * s) : Equivalent p q := by
  let _ := CStarAlgebra.spectralOrder A
  let _ := CStarAlgebra.spectralOrderedRing A
  let t := star s * s
  have ht : IsUnit t := hs.star.mul hs
  have htpos : 0 ≤ t := star_mul_self_nonneg s
  let z : A := CFC.rpow t (- (1 / 2 : ℝ))
  have hzstar : star z = z := (CFC.rpow_nonneg (a := t) (y := -(1 / 2 : ℝ))).isSelfAdjoint.star_eq
  have hzunit : IsUnit z := ht.cfcRpow _ htpos
  have hstar : (p : A) * star s = star s * q := by
    simpa only [star_mul, star_coe] using congrArg star hsp
  have htp : Commute t (p : A) := by
    show (star s * s) * p = p * (star s * s)
    calc
      (star s * s) * p = star s * (q * s) := by rw [mul_assoc, hsp]
      _ = (p * star s) * s := by rw [hstar, mul_assoc]
      _ = p * (star s * s) := mul_assoc _ _ _
  have hzp : z * p = p * z := (htp.cfc_nnreal (fun x => x ^ (-(1 / 2 : ℝ)))).eq
  have hztz : z * t * z = 1 := by
    simp only [z, CFC.rpow_eq_pow]
    calc
      t ^ (-(1 / 2 : ℝ)) * t * t ^ (-(1 / 2 : ℝ)) = (t ^ (-(1 / 2 : ℝ)) * t ^ (1 : ℝ)) *
          t ^ (-(1 / 2 : ℝ)) := by rw [CFC.rpow_one t htpos]
      _ = t ^ ((-(1 / 2 : ℝ) + 1) + -(1 / 2 : ℝ)) := by
        rw [CFC.rpow_add ht, CFC.rpow_add ht]
      _ = 1 := by norm_num; exact CFC.rpow_zero t htpos
  let u := s * z
  have hu : star u * u = 1 := by
    calc
      star u * u = z * t * z := by simp only [u, t, star_mul, hzstar, mul_assoc]
      _ = 1 := hztz
  have huu : u * star u = 1 := by
    apply (hs.mul hzunit).mul_right_cancel
    change (u * star u) * u = 1 * u
    rw [mul_assoc, hu, mul_one, one_mul]
  have hup : u * p = q * u := by
    change (s * z) * p = q * (s * z)
    rw [mul_assoc, hzp, ← mul_assoc, hsp, mul_assoc]
  refine ⟨u * p, ?_, ?_⟩
  · calc
      star (u * p) * (u * p) = p * (star u * u) * p := by simp only [star_mul, star_coe, mul_assoc]
      _ = p := by rw [hu, mul_one, mul_self]
  · calc
      (u * p) * star (u * p) = u * ((p * p) * star u) := by simp only [star_mul, star_coe, mul_assoc]
      _ = (u * p) * star u := by rw [mul_self]; exact (mul_assoc u (p : A) (star u)).symm
      _ = q * (u * star u) := by rw [hup, mul_assoc]
      _ = q := by rw [huu, mul_one]

/-- The standard intertwiner is invertible on a neighborhood of a projection. -/
theorem eventually_equivalent (p : Projection A) : ∀ᶠ q in nhds p, Equivalent p q := by
  let s : Projection A → A := fun q => (q : A) * p + (1 - q) * (1 - p)
  have hc : Continuous s :=
    (continuous_subtype_val.mul continuous_const).add
      ((continuous_const.sub continuous_subtype_val).mul continuous_const)
  have hsp : s p = 1 := by
    dsimp [s]
    noncomm_ring [mul_self p]
  have he : ∀ᶠ q in nhds p, IsUnit (s q) :=
    hc.continuousAt (Units.isOpen.mem_nhds (hsp ▸ isUnit_one))
  filter_upwards [he] with q hq
  apply equivalent_of_invertible_intertwiner p q (s q) hq
  dsimp [s]
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, mul_assoc,
    ← mul_assoc (q : A) (q : A) (p : A), mul_self]
  noncomm_ring

/-- The Murray–von Neumann class of a projection is locally constant in norm. -/
theorem isLocallyConstant_class :
    IsLocallyConstant (fun p : Projection A => (Quotient.mk _ p : Classes A)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro p
  filter_upwards [eventually_equivalent p] with q hq
  exact Quotient.sound (equivalent_symm hq)

/-- Endpoints of a norm-continuous projection path are Murray–von Neumann equivalent. -/
theorem equivalent_of_path {p q : Projection A} (h : Path p q) : Equivalent p q := by
  have hc := isLocallyConstant_class.comp_continuous h.continuous
  have he := hc.apply_eq_of_preconnectedSpace (0 : unitInterval) 1
  change (Quotient.mk _ (h 0) : Classes A) = Quotient.mk _ (h 1) at he
  rw [h.source, h.target] at he
  exact Quotient.exact he

end Projection
end BC4lean.OperatorKTheory
