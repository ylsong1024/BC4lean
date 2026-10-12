import BC4lean.OddFredholmExponential
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

/-! # Actual projection phases of commuting operator unitaries

A selfadjoint reflection R has complementary spectral projections (I±R)/2.
An actual unitary w commuting with R acts on the negative projection and
fixes the positive projection, giving a genuine unitary. This is the
operator-coefficient version of the scalar reflection phase; it is used for
an explicit arbitrary-Fredholm normal-form homotopy.
-/

noncomputable section
namespace BC4lean.KKTheory

variable {A : Type*} [CStarAlgebra A]

def oddFredholmReflectionPositive (R : A) : A := (1 / 2 : ℂ) • (1 + R)
def oddFredholmReflectionNegative (R : A) : A := (1 / 2 : ℂ) • (1 - R)

theorem oddFredholmReflectionPositive_star (R : A) (hR : star R = R) :
    star (oddFredholmReflectionPositive R) = oddFredholmReflectionPositive R := by
  simp [oddFredholmReflectionPositive, hR]

theorem oddFredholmReflectionNegative_star (R : A) (hR : star R = R) :
    star (oddFredholmReflectionNegative R) = oddFredholmReflectionNegative R := by
  simp [oddFredholmReflectionNegative, hR]

theorem oddFredholmReflectionProjections_sum (R : A) :
    oddFredholmReflectionPositive R + oddFredholmReflectionNegative R = 1 := by
  unfold oddFredholmReflectionPositive oddFredholmReflectionNegative
  module

theorem oddFredholmReflectionProjections_products (R : A) (hR2 : R * R = 1) :
    oddFredholmReflectionPositive R * oddFredholmReflectionPositive R = oddFredholmReflectionPositive R ∧
    oddFredholmReflectionNegative R * oddFredholmReflectionNegative R = oddFredholmReflectionNegative R ∧
    oddFredholmReflectionPositive R * oddFredholmReflectionNegative R = 0 ∧
    oddFredholmReflectionNegative R * oddFredholmReflectionPositive R = 0 := by
  simp only [oddFredholmReflectionPositive, oddFredholmReflectionNegative,
    smul_mul_assoc, mul_smul_comm, add_mul, mul_add, sub_mul, mul_sub,
    one_mul, mul_one, hR2]
  constructor
  · module
  constructor
  · module
  constructor <;> module

/-- Every actual commuting operator commutes with both reflection projections. -/
theorem oddFredholmReflectionProjections_commute (R w : A) (hRw : Commute R w) :
    Commute (oddFredholmReflectionPositive R) w ∧ Commute (oddFredholmReflectionNegative R) w := by
  constructor
  all_goals
    rw [commute_iff_eq]
    simp only [oddFredholmReflectionPositive, oddFredholmReflectionNegative,
      smul_mul_assoc, mul_smul_comm, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, hRw.eq]

/-- The actual operator-valued reflection phase. -/
def oddFredholmCommutingPhaseElement (R : A) (w : unitary A) : A :=
  oddFredholmReflectionPositive R + (w : A) * oddFredholmReflectionNegative R

theorem oddFredholmCommutingPhaseElement_star (R : A) (hR : star R = R)
    (w : unitary A) (hRw : Commute R (w : A)) :
    star (oddFredholmCommutingPhaseElement R w) = oddFredholmCommutingPhaseElement R (star w) := by
  have hRws : Commute R (star (w : A)) := by
    rw [commute_iff_eq]
    simpa only [star_mul, hR] using (congrArg star hRw.eq).symm
  rw [oddFredholmCommutingPhaseElement, star_add, star_mul,
    oddFredholmReflectionPositive_star R hR, oddFredholmReflectionNegative_star R hR]
  exact congrArg (fun x => oddFredholmReflectionPositive R + x)
    (oddFredholmReflectionProjections_commute R _ hRws).2.eq

theorem oddFredholmCommutingPhaseElement_starPhase_mul (R : A) (hR2 : R * R = 1)
    (w : unitary A) (hRw : Commute R (w : A)) :
    oddFredholmCommutingPhaseElement R (star w) * oddFredholmCommutingPhaseElement R w = 1 := by
  let P := oddFredholmReflectionPositive R
  let Q := oddFredholmReflectionNegative R
  have hprod := oddFredholmReflectionProjections_products R hR2
  have hP : P * P = P := hprod.1
  have hQ : Q * Q = Q := hprod.2.1
  have hPQ : P * Q = 0 := hprod.2.2.1
  have hQP : Q * P = 0 := hprod.2.2.2
  have hcomm := oddFredholmReflectionProjections_commute R (w : A) hRw
  have hQcomm : Q * (w : A) = (w : A) * Q := hcomm.2.eq
  have hcross : P * ((w : A) * Q) = 0 := by
    rw [← mul_assoc, hcomm.1.eq, mul_assoc, hPQ, mul_zero]
  have hlast : (star (w : A) * Q) * ((w : A) * Q) = Q := by
    calc
      _ = star (w : A) * (Q * (w : A)) * Q := by simp only [mul_assoc]
      _ = star (w : A) * (w : A) * (Q * Q) := by rw [hQcomm]; simp only [mul_assoc]
      _ = Q := by rw [Unitary.coe_star_mul_self, hQ, one_mul]
  change (P + star (w : A) * Q) * (P + (w : A) * Q) = 1
  rw [add_mul, mul_add, mul_add, hP, hcross, mul_assoc, hQP, mul_zero, hlast]
  simpa only [add_zero, zero_add] using oddFredholmReflectionProjections_sum R

/-- The actual operator-valued phase is unitary by both genuine unitary
identities; no one-sided inverse is mistaken for unitarity. -/
theorem oddFredholmCommutingPhaseElement_mem_unitary (R : A) (hR : star R = R)
    (hR2 : R * R = 1) (w : unitary A) (hRw : Commute R (w : A)) :
    oddFredholmCommutingPhaseElement R w ∈ unitary A := by
  have hRws : Commute R (star (w : A)) := by
    rw [commute_iff_eq]
    simpa only [star_mul, hR] using (congrArg star hRw.eq).symm
  apply Unitary.mem_iff.mpr
  constructor
  · rw [oddFredholmCommutingPhaseElement_star R hR w hRw]
    exact oddFredholmCommutingPhaseElement_starPhase_mul R hR2 w hRw
  · rw [oddFredholmCommutingPhaseElement_star R hR w hRw]
    simpa only [star_star] using oddFredholmCommutingPhaseElement_starPhase_mul R hR2 (star w) hRws

def oddFredholmCommutingPhase (R : A) (hR : star R = R) (hR2 : R * R = 1)
    (w : unitary A) (hRw : Commute R (w : A)) : unitary A :=
  ⟨oddFredholmCommutingPhaseElement R w,
    oddFredholmCommutingPhaseElement_mem_unitary R hR hR2 w hRw⟩

@[simp] theorem oddFredholmCommutingPhaseElement_one (R : A) :
    oddFredholmCommutingPhaseElement R (1 : unitary A) = 1 := by
  rw [oddFredholmCommutingPhaseElement, Submonoid.coe_one, one_mul,
    oddFredholmReflectionProjections_sum]

end BC4lean.KKTheory
