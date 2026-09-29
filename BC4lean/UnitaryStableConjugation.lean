import BC4lean.StableUnitary

/-! # A geometric justification for stable changes of coordinates -/
noncomputable section
namespace BC4lean.OperatorKTheory
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Conjugation by any matrix unitary is norm homotopic to the identity action
on a unitary after adjoining an identity block. -/
theorem unitaryHomotopic_stable_conjugate (w a : MatrixUnitary A ι) :
    UnitaryHomotopic (unitaryBlockSum (w * a * star w) (1 : MatrixUnitary A ι)) (unitaryBlockSum a (1 : MatrixUnitary A ι)) := by
  have h := unitaryHomotopic_blockSum_star w
  have hi := unitaryHomotopic_inv h
  have hstar : (unitaryBlockSum w (star w))⁻¹ = unitaryBlockSum (star w) w := by
    change star (unitaryBlockSum w (star w)) = _
    rw [unitaryBlockSum_star, star_star]
  rw [hstar, inv_one] at hi
  have hh := unitaryHomotopic_mul (unitaryHomotopic_mul h
    (unitaryHomotopic_refl (unitaryBlockSum a (1 : MatrixUnitary A ι)))) hi
  simpa only [unitaryBlockSum_mul, one_mul, mul_one, Unitary.star_mul_self] using hh

end BC4lean.OperatorKTheory
