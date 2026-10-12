import BC4lean.KasparovBandControl

/-! # Actual norm estimates for weighted technical-theorem bands

The ideal conclusions of the technical theorem require norm-convergent
product and error series. These estimates turn the selected geometric
controls into such series. Only the unmultiplied positive band sums use
strong convergence; bounded monotone sums alone are never asserted to
converge in norm.
-/

noncomputable section
namespace BC4lean.KKTheory
open Filter
open scoped Topology

section AlgebraEstimates
variable {A : Type*} [NormedRing A]

private theorem norm_three_mul_le (x y z : A) : ‖x * y * z‖ ≤ (‖x‖ * ‖y‖) * ‖z‖ :=
  (norm_mul_le (x * y) z).trans
    (mul_le_mul_of_nonneg_right (norm_mul_le x y) (norm_nonneg z))

/-- Weighted-band commutators have two band errors and one weight error. -/
theorem norm_weighted_band_commutator_le (d w a : A) (hd : ‖d‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖(d * w * d) * a - a * (d * w * d)‖ ≤
      2 * ‖d * a - a * d‖ + ‖w * a - a * w‖ := by
  have heq : (d * w * d) * a - a * (d * w * d) =
      d * w * (d * a - a * d) + d * (w * a - a * w) * d +
        (d * a - a * d) * w * d := by noncomm_ring
  rw [heq]
  calc
    _ ≤ ‖d * w * (d * a - a * d)‖ + ‖d * (w * a - a * w) * d‖ +
        ‖(d * a - a * d) * w * d‖ := norm_add₃_le
    _ ≤ (‖d‖ * ‖w‖) * ‖d * a - a * d‖ +
        (‖d‖ * ‖w * a - a * w‖) * ‖d‖ +
        (‖d * a - a * d‖ * ‖w‖) * ‖d‖ :=
      add_le_add (add_le_add (norm_three_mul_le _ _ _) (norm_three_mul_le _ _ _))
        (norm_three_mul_le _ _ _)
    _ ≤ 2 * ‖d * a - a * d‖ + ‖w * a - a * w‖ := by
      have hd0 := norm_nonneg d
      have hw0 := norm_nonneg w
      have ha0 := norm_nonneg (d * a - a * d)
      have hwc0 := norm_nonneg (w * a - a * w)
      have h1 : (‖d‖ * ‖w‖) * ‖d * a - a * d‖ ≤ ‖d * a - a * d‖ := by
        calc
          _ ≤ (1 * 1) * ‖d * a - a * d‖ := by gcongr
          _ = _ := by ring
      have h2 : (‖d‖ * ‖w * a - a * w‖) * ‖d‖ ≤ ‖w * a - a * w‖ := by
        calc
          _ ≤ (1 * ‖w * a - a * w‖) * 1 := by gcongr
          _ = _ := by ring
      have h3 : (‖d * a - a * d‖ * ‖w‖) * ‖d‖ ≤ ‖d * a - a * d‖ := by
        calc
          _ ≤ (‖d * a - a * d‖ * 1) * 1 := by gcongr
          _ = _ := by ring
      linarith

/-- Moving the last band past a tested coefficient exposes the actual
approximate-unit product and one commutator error. -/
theorem norm_weighted_band_product_le (d w a : A) (hd : ‖d‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖d * w * d * a‖ ≤ ‖w * a‖ + ‖d * a - a * d‖ := by
  have heq : d * w * d * a = d * (w * a) * d + d * w * (d * a - a * d) := by
    noncomm_ring
  rw [heq]
  calc
    _ ≤ ‖d * (w * a) * d‖ + ‖d * w * (d * a - a * d)‖ := norm_add_le _ _
    _ ≤ (‖d‖ * ‖w * a‖) * ‖d‖ + (‖d‖ * ‖w‖) * ‖d * a - a * d‖ :=
      add_le_add (norm_three_mul_le _ _ _) (norm_three_mul_le _ _ _)
    _ ≤ (1 * ‖w * a‖) * 1 + (1 * 1) * ‖d * a - a * d‖ := by gcongr
    _ = _ := by ring

/-- For the other partition half, the selected compact product is
multiplied first by the band; its residual estimate controls this term. -/
theorem norm_weighted_band_product_le_band_product (d w b : A)
    (hd : ‖d‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖d * w * d * b‖ ≤ ‖d * (w * b)‖ + ‖d * b - b * d‖ := by
  have heq : d * w * d * b = (d * (w * b)) * d + d * w * (d * b - b * d) := by
    noncomm_ring
  rw [heq]
  calc
    _ ≤ ‖(d * (w * b)) * d‖ + ‖d * w * (d * b - b * d)‖ := norm_add_le _ _
    _ ≤ ‖d * (w * b)‖ * ‖d‖ + (‖d‖ * ‖w‖) * ‖d * b - b * d‖ :=
      add_le_add (norm_mul_le _ _) (norm_three_mul_le _ _ _)
    _ ≤ ‖d * (w * b)‖ * 1 + (1 * 1) * ‖d * b - b * d‖ := by gcongr
    _ = _ := by ring

end AlgebraEstimates

section CStarEstimates
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A band whose square is below a positive residual acts on an actual
compact coefficient with the required squared norm bound. -/
theorem norm_band_mul_sq_le_residual (d r x : A) (hd : star d = d)
    (hres : d * d ≤ r) : ‖d * x‖ ^ 2 ≤ ‖x‖ * ‖r * x‖ := by
  have hpos : 0 ≤ star x * (d * d) * x := by
    have hdd : 0 ≤ d * d := by simpa only [hd] using star_mul_self_nonneg d
    exact star_left_conjugate_nonneg hdd x
  have horder := star_left_conjugate_le_conjugate hres x
  have heq : star (d * x) * (d * x) = star x * (d * d) * x := by
    rw [star_mul, hd]
    noncomm_ring
  calc
    ‖d * x‖ ^ 2 = ‖star (d * x) * (d * x)‖ := by
      rw [CStarRing.norm_star_mul_self]
      ring
    _ = ‖star x * (d * d) * x‖ := congrArg norm heq
    _ ≤ ‖star x * r * x‖ := CStarAlgebra.norm_le_norm_of_nonneg_of_le hpos horder
    _ = ‖star x * (r * x)‖ := by rw [mul_assoc]
    _ ≤ ‖star x‖ * ‖r * x‖ := norm_mul_le _ _
    _ = ‖x‖ * ‖r * x‖ := by rw [norm_star]

/-- The stage-dependent squared geometric residual bound gives a
geometric band-product bound. The denominator includes the actual norm
of the family value, so no uniform family norm is silently assumed. -/
theorem norm_band_weighted_product_lt_of_residual
    (d e u b : A) (hd : star d = d) (hres : d * d ≤ 1 - e)
    (hu : ‖u‖ ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (herr : ‖e * (u * b) - u * b‖ < ε ^ 2 / (‖b‖ + 1)) :
    ‖d * (u * b)‖ < ε := by
  have hs := norm_band_mul_sq_le_residual d (1 - e) (u * b) hd hres
  have hn : ‖u * b‖ ≤ ‖b‖ := (norm_mul_le u b).trans
    (by simpa using mul_le_mul_of_nonneg_right hu (norm_nonneg b))
  have hr : ‖(1 - e) * (u * b)‖ = ‖e * (u * b) - u * b‖ := by
    rw [sub_mul, one_mul, norm_sub_rev]
  rw [hr] at hs
  have hp := (lt_div_iff₀ (by positivity : 0 < ‖b‖ + 1)).mp herr
  have hmul := mul_le_mul_of_nonneg_right hn (norm_nonneg (e * (u * b) - u * b))
  have hslt : ‖d * (u * b)‖ ^ 2 < ε ^ 2 := by
    nlinarith [norm_nonneg (e * (u * b) - u * b)]
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le (by decide : (2 : ℕ) ≠ 0)).mp hslt

omit [PartialOrder A] [StarOrderedRing A] in
/-- Star automorphisms give two actual band errors and one weight error. -/
theorem norm_weighted_band_action_le (α : A ≃⋆ₐ[ℂ] A) (d w : A)
    (hd : ‖d‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖α (d * w * d) - d * w * d‖ ≤ 2 * ‖α d - d‖ + ‖α w - w‖ := by
  have hαd : ‖α d‖ ≤ 1 := by simpa only [StarAlgEquiv.norm_map] using hd
  have hαw : ‖α w‖ ≤ 1 := by simpa only [StarAlgEquiv.norm_map] using hw
  have heq : α (d * w * d) - d * w * d =
      (α d - d) * α w * α d + d * (α w - w) * α d + d * w * (α d - d) := by
    rw [map_mul, map_mul]
    noncomm_ring
  rw [heq]
  calc
    _ ≤ ‖(α d - d) * α w * α d‖ + ‖d * (α w - w) * α d‖ +
        ‖d * w * (α d - d)‖ := norm_add₃_le
    _ ≤ (‖α d - d‖ * ‖α w‖) * ‖α d‖ +
        (‖d‖ * ‖α w - w‖) * ‖α d‖ + (‖d‖ * ‖w‖) * ‖α d - d‖ :=
      add_le_add (add_le_add (norm_three_mul_le _ _ _) (norm_three_mul_le _ _ _))
        (norm_three_mul_le _ _ _)
    _ ≤ (‖α d - d‖ * 1) * 1 + (1 * ‖α w - w‖) * 1 +
        (1 * 1) * ‖α d - d‖ := by gcongr
    _ = _ := by ring

end CStarEstimates
end BC4lean.KKTheory
