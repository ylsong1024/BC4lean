import BC4lean.OddKTheoryMatrixLoopExponential
import BC4lean.CliffordTwoMatrix
import Mathlib.Topology.ContinuousMap.Star

/-! # A concrete based finite-unitary recovery homotopy on the circle

Rotate the two-coordinate projection by the phase exp(iπst), and multiply
its varying part by exp(2πit)-1. The resulting genuine finite matrix unitary
has equal interval endpoints I at every homotopy parameter. Descending the
entire continuous family through the endpoints quotient gives a continuous
based circle homotopy; its upper endpoint has the actual four exponential
entries from the infinite Fredholm construction.
-/

noncomputable section
namespace BC4lean.KKTheory

open unitInterval
open scoped Matrix CStarAlgebra

abbrev OddKTheoryRecoveryMatrix := CStarMatrix (Fin 2) (Fin 2) ℂ

local instance oddKTheoryRecoveryMatrixCStarAlgebra : CStarAlgebra OddKTheoryRecoveryMatrix :=
  CliffordTwo.pauliCStarAlgebra

def oddKTheoryRecoveryProjection : OddKTheoryRecoveryMatrix :=
  CStarMatrix.ofMatrix ![![1, 0], ![0, 0]]

def oddKTheoryRecoveryReflection : OddKTheoryRecoveryMatrix :=
  CStarMatrix.ofMatrix ![![0, 1], ![1, 0]]

theorem oddKTheoryRecoveryProjection_isStarProjection :
    IsStarProjection oddKTheoryRecoveryProjection := by
  apply isStarProjection_iff'.mpr
  constructor
  · change (CStarMatrix.ofMatrix !![1, 0; 0, 0] : OddKTheoryRecoveryMatrix) *
      CStarMatrix.ofMatrix !![1, 0; 0, 0] = CStarMatrix.ofMatrix !![1, 0; 0, 0]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [CStarMatrix.mul_apply, Fin.sum_univ_two]
  · change star (CStarMatrix.ofMatrix !![1, 0; 0, 0] : OddKTheoryRecoveryMatrix) =
      CStarMatrix.ofMatrix !![1, 0; 0, 0]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [CStarMatrix.star_apply]

theorem oddKTheoryRecoveryReflection_star :
    star oddKTheoryRecoveryReflection = oddKTheoryRecoveryReflection := by
  change star (CStarMatrix.ofMatrix !![0, 1; 1, 0] : OddKTheoryRecoveryMatrix) =
    CStarMatrix.ofMatrix !![0, 1; 1, 0]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [CStarMatrix.star_apply]

theorem oddKTheoryRecoveryReflection_square :
    oddKTheoryRecoveryReflection * oddKTheoryRecoveryReflection = 1 := by
  change (CStarMatrix.ofMatrix !![0, 1; 1, 0] : OddKTheoryRecoveryMatrix) *
    CStarMatrix.ofMatrix !![0, 1; 1, 0] = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [CStarMatrix.mul_apply, Fin.sum_univ_two, CStarMatrix.one_apply]

def oddKTheoryRecoveryPhase (s t : ℝ) : unitary OddKTheoryRecoveryMatrix :=
  oddKTheoryReflectionPhase oddKTheoryRecoveryReflection oddKTheoryRecoveryReflection_star
    oddKTheoryRecoveryReflection_square (oddKTheoryHalfPhase (s * t))

def oddKTheoryRecoveryMovingProjection (s t : ℝ) : OddKTheoryRecoveryMatrix :=
  star (oddKTheoryRecoveryPhase s t : OddKTheoryRecoveryMatrix) *
    oddKTheoryRecoveryProjection * oddKTheoryRecoveryPhase s t

theorem oddKTheoryRecoveryMovingProjection_isStarProjection (s t : ℝ) :
    IsStarProjection (oddKTheoryRecoveryMovingProjection s t) := by
  let w := oddKTheoryRecoveryPhase s t
  have hp := oddKTheoryRecoveryProjection_isStarProjection
  have hw : (w : OddKTheoryRecoveryMatrix) * star (w : OddKTheoryRecoveryMatrix) = 1 :=
    Unitary.mul_star_self_of_mem w.property
  apply isStarProjection_iff'.mpr
  constructor
  · change (star (w : OddKTheoryRecoveryMatrix) * oddKTheoryRecoveryProjection * w) *
      (star (w : OddKTheoryRecoveryMatrix) * oddKTheoryRecoveryProjection * w) = _
    calc
      _ = star (w : OddKTheoryRecoveryMatrix) * oddKTheoryRecoveryProjection *
        ((w : OddKTheoryRecoveryMatrix) * star (w : OddKTheoryRecoveryMatrix)) *
          oddKTheoryRecoveryProjection * w := by simp only [mul_assoc]
      _ = _ := by
        rw [hw, mul_one]
        change star (w : OddKTheoryRecoveryMatrix) * oddKTheoryRecoveryProjection *
          oddKTheoryRecoveryProjection * w =
            star (w : OddKTheoryRecoveryMatrix) * oddKTheoryRecoveryProjection * w
        rw [mul_assoc (star (w : OddKTheoryRecoveryMatrix)) oddKTheoryRecoveryProjection
          oddKTheoryRecoveryProjection, hp.isIdempotentElem.eq]
  · simp only [oddKTheoryRecoveryMovingProjection, star_mul, star_star,
      hp.isSelfAdjoint.star_eq, mul_assoc]

theorem oddKTheoryProjectionScalarUnitary_mem {A : Type*} [CStarAlgebra A]
    (p : A) (hp : IsStarProjection p) (z : unitary ℂ) :
    (1 - p) + (z : ℂ) • p ∈ unitary A := by
  have hpp := hp.isIdempotentElem.eq
  have hzstar : star (z : ℂ) * (z : ℂ) = 1 := Unitary.star_mul_self_of_mem z.property
  have hz : (z : ℂ) * star (z : ℂ) = 1 := Unitary.mul_star_self_of_mem z.property
  have hqp : (1 - p) * p = 0 := by rw [sub_mul, one_mul, hpp, sub_self]
  have hpq : p * (1 - p) = 0 := by rw [mul_sub, mul_one, hpp, sub_self]
  have hqq : (1 - p) * (1 - p) = 1 - p := hp.one_sub.isIdempotentElem.eq
  apply Unitary.mem_iff.mpr
  constructor
  · simp only [star_add, star_sub, star_one, hp.isSelfAdjoint.star_eq, star_smul,
      add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
      hqq, hqp, hpq, hpp, smul_zero, add_zero, zero_add,
      hz, one_smul]
    abel
  · simp only [star_add, star_sub, star_one, hp.isSelfAdjoint.star_eq, star_smul,
      add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
      hqq, hqp, hpq, hpp, smul_zero, add_zero, zero_add,
      hzstar, one_smul]
    abel

def oddKTheoryRecoveryIntervalUnitary (s t : ℝ) : unitary OddKTheoryRecoveryMatrix :=
  ⟨(1 - oddKTheoryRecoveryMovingProjection s t) +
      (oddKTheoryHalfPhase (2 * t) : ℂ) • oddKTheoryRecoveryMovingProjection s t,
    oddKTheoryProjectionScalarUnitary_mem _ (oddKTheoryRecoveryMovingProjection_isStarProjection s t) _⟩

theorem continuous_oddKTheoryRecoveryIntervalUnitary :
    Continuous (fun x : ℝ × ℝ => oddKTheoryRecoveryIntervalUnitary x.1 x.2) := by
  have hw : Continuous (fun x : ℝ × ℝ => oddKTheoryRecoveryPhase x.1 x.2) :=
    ((continuous_oddKTheoryReflectionPhaseElement oddKTheoryRecoveryReflection).comp
      (continuous_oddKTheoryHalfPhase.comp (continuous_fst.mul continuous_snd))).subtype_mk _
  have hp : Continuous (fun x : ℝ × ℝ => oddKTheoryRecoveryMovingProjection x.1 x.2) :=
    ((continuous_subtype_val.comp hw).star.mul continuous_const).mul (continuous_subtype_val.comp hw)
  exact ((continuous_const.sub hp).add
    ((continuous_subtype_val.comp (continuous_oddKTheoryHalfPhase.comp
      (continuous_const.mul continuous_snd))).smul hp)).subtype_mk _

@[simp] theorem oddKTheoryHalfPhase_two_coe : (oddKTheoryHalfPhase 2 : ℂ) = 1 := by
  change NormedSpace.exp (Complex.I • ((Real.pi * 2) • (1 : ℂ))) = 1
  rw [← Complex.exp_eq_exp_ℂ]
  have harg : Complex.I • ((Real.pi * 2) • (1 : ℂ)) =
      2 * (Real.pi : ℂ) * Complex.I := by
    simp only [RCLike.real_smul_eq_coe_mul, smul_eq_mul]
    push_cast
    ring_nf
    all_goals rfl
  rw [harg]
  exact Complex.exp_two_pi_mul_I

@[simp] theorem oddKTheoryRecoveryIntervalUnitary_zero (s : ℝ) :
    oddKTheoryRecoveryIntervalUnitary s 0 = 1 := by
  apply Subtype.ext
  simp [oddKTheoryRecoveryIntervalUnitary]

@[simp] theorem oddKTheoryRecoveryIntervalUnitary_one (s : ℝ) :
    oddKTheoryRecoveryIntervalUnitary s 1 = 1 := by
  apply Subtype.ext
  simp [oddKTheoryRecoveryIntervalUnitary, oddKTheoryHalfPhase_two_coe]

/-- The whole homotopy family is descended at once, retaining continuity
in the homotopy parameter through the actual compact-open mapping topology. -/
def oddKTheoryRecoveryCircleFamily : C(Circle, C(I, unitary OddKTheoryRecoveryMatrix)) where
  toFun z := AddCircle.liftIco (1 : ℝ) 0
    (fun t : ℝ => (⟨fun s : I => oddKTheoryRecoveryIntervalUnitary (s : ℝ) t, by
      have hpair : Continuous (fun s : I => ((s : ℝ), t)) :=
        continuous_subtype_val.prodMk continuous_const
      simpa only [Function.comp_def] using
        (Continuous.comp
          (f := fun s : I => ((s : ℝ), t))
          (g := fun x : ℝ × ℝ => oddKTheoryRecoveryIntervalUnitary x.1 x.2)
          continuous_oddKTheoryRecoveryIntervalUnitary hpair)⟩ :
        C(I, unitary OddKTheoryRecoveryMatrix)))
      ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm z)
  continuous_toFun := by
    let F : ℝ → C(I, unitary OddKTheoryRecoveryMatrix) := fun t =>
      ⟨fun s : I => oddKTheoryRecoveryIntervalUnitary (s : ℝ) t, by
        have hpair : Continuous (fun s : I => ((s : ℝ), t)) :=
          continuous_subtype_val.prodMk continuous_const
        simpa only [Function.comp_def] using
          (Continuous.comp
            (f := fun s : I => ((s : ℝ), t))
            (g := fun x : ℝ × ℝ => oddKTheoryRecoveryIntervalUnitary x.1 x.2)
            continuous_oddKTheoryRecoveryIntervalUnitary hpair)⟩
    change Continuous (fun z : Circle => AddCircle.liftIco (1 : ℝ) 0 F
      ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm z))
    apply Continuous.comp
      (f := fun z : Circle =>
        (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm z)
      (g := AddCircle.liftIco (1 : ℝ) 0 F)
      ?_ (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.continuous
    apply AddCircle.liftIco_zero_continuous
    · apply ContinuousMap.ext
      intro s
      change oddKTheoryRecoveryIntervalUnitary (s : ℝ) 0 =
        oddKTheoryRecoveryIntervalUnitary (s : ℝ) 1
      simp only [oddKTheoryRecoveryIntervalUnitary_zero, oddKTheoryRecoveryIntervalUnitary_one]
    · apply Continuous.continuousOn
      apply ContinuousMap.continuous_of_continuous_uncurry F
      change Continuous (fun x : ℝ × I =>
        oddKTheoryRecoveryIntervalUnitary (x.2 : ℝ) x.1)
      have hpair : Continuous (fun x : ℝ × I => ((x.2 : ℝ), x.1)) :=
        (continuous_subtype_val.comp continuous_snd).prodMk continuous_fst
      simpa only [Function.comp_def] using
        (Continuous.comp
          (f := fun x : ℝ × I => ((x.2 : ℝ), x.1))
          (g := fun x : ℝ × ℝ => oddKTheoryRecoveryIntervalUnitary x.1 x.2)
          continuous_oddKTheoryRecoveryIntervalUnitary hpair)

theorem oddKTheoryRecoveryCircleFamily_apply (z : Circle) (s : I) :
    oddKTheoryRecoveryCircleFamily z s =
      oddKTheoryRecoveryIntervalUnitary s (oddKTheoryCircleLoopParameter z) := rfl

/-- Each scalar matrix entry is an actual continuously varying circle
coefficient, with continuity in the operator norm on the compact circle. -/
def oddKTheoryRecoveryCircleEntry (s : I) (i j : Fin 2) : C(Circle, ℂ) where
  toFun z := (oddKTheoryRecoveryCircleFamily z s : OddKTheoryRecoveryMatrix) i j
  continuous_toFun := by
    have hentry : Continuous (fun a : OddKTheoryRecoveryMatrix => a i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp CStarMatrix.ofMatrixL.symm.continuous)
    exact hentry.comp (continuous_subtype_val.comp
      ((continuous_eval_const s).comp (map_continuous oddKTheoryRecoveryCircleFamily)))

theorem continuous_oddKTheoryRecoveryCircleEntry (i j : Fin 2) :
    Continuous (fun s : I => oddKTheoryRecoveryCircleEntry s i j) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hentry : Continuous (fun a : OddKTheoryRecoveryMatrix => a i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp CStarMatrix.ofMatrixL.symm.continuous)
  exact hentry.comp (continuous_subtype_val.comp
    (continuous_eval.comp
      (((map_continuous oddKTheoryRecoveryCircleFamily).comp continuous_snd).prodMk continuous_fst)))

/-- The whole circle family remains based at I at every homotopy parameter. -/
@[simp] theorem oddKTheoryRecoveryCircleFamily_one (s : I) :
    oddKTheoryRecoveryCircleFamily 1 s = 1 := by
  let e := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have he : e.symm (1 : Circle) = 0 := by
    apply e.injective
    rw [e.apply_symm_apply]
    simp [e, AddCircle.homeomorphCircle_apply]
  change AddCircle.liftIco (1 : ℝ) 0
    (fun t => (⟨fun v : I => oddKTheoryRecoveryIntervalUnitary v t, _⟩ :
      C(I, unitary OddKTheoryRecoveryMatrix))) (e.symm 1) s = 1
  have hz (F : ℝ → C(I, unitary OddKTheoryRecoveryMatrix)) :
      AddCircle.liftIco (1 : ℝ) 0 F (0 : AddCircle (1 : ℝ)) s = F 0 s := by
    have h := AddCircle.liftIco_zero_coe_apply (f := F) (x := (0 : ℝ))
      (by norm_num : (0 : ℝ) ∈ Set.Ico 0 1)
    simpa only [AddCircle.coe_zero] using
      congrArg (fun g : C(I, unitary OddKTheoryRecoveryMatrix) => g s) h
  rw [he, hz]
  exact oddKTheoryRecoveryIntervalUnitary_zero s

@[simp] theorem oddKTheoryRecoveryCircleEntry_one (s : I) (i j : Fin 2) :
    oddKTheoryRecoveryCircleEntry s i j 1 = if i = j then 1 else 0 := by
  change (oddKTheoryRecoveryCircleFamily 1 s : OddKTheoryRecoveryMatrix) i j = _
  rw [oddKTheoryRecoveryCircleFamily_one]
  exact CStarMatrix.one_apply

theorem oddKTheoryCircleLoopParameter_phase (z : Circle) :
    Circle.exp (2 * Real.pi * oddKTheoryCircleLoopParameter z) = z := by
  let e := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have hh : ((oddKTheoryCircleLoopParameter z : ℝ) : AddCircle (1 : ℝ)) = e.symm z :=
    AddCircle.coe_equivIco
  have hp : e ((oddKTheoryCircleLoopParameter z : ℝ) : AddCircle (1 : ℝ)) =
      Circle.exp (2 * Real.pi * oddKTheoryCircleLoopParameter z) := by
    rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk, div_one]
  rw [← hp, hh, e.apply_symm_apply]

theorem oddKTheoryHalfPhase_coe_eq_exp (t : ℝ) :
    (oddKTheoryHalfPhase t : ℂ) = Complex.exp (((Real.pi * t : ℝ) : ℂ) * Complex.I) := by
  change NormedSpace.exp (Complex.I • ((Real.pi * t) • (1 : ℂ))) = _
  rw [← Complex.exp_eq_exp_ℂ]
  have harg : Complex.I • ((Real.pi * t) • (1 : ℂ)) =
      ((Real.pi * t : ℝ) : ℂ) * Complex.I := by
    simp only [RCLike.real_smul_eq_coe_mul, smul_eq_mul]
    ring_nf
    all_goals rfl
  rw [harg]

theorem oddKTheoryRecoveryMovingProjection_zero (t : ℝ) :
    oddKTheoryRecoveryMovingProjection 0 t = oddKTheoryRecoveryProjection := by
  simp [oddKTheoryRecoveryMovingProjection, oddKTheoryRecoveryPhase,
    oddKTheoryReflectionPhase, oddKTheoryReflectionPhaseElement_one]

/-- The lower endpoint is the elementary finite circle unitary diag(z,1). -/
theorem oddKTheoryRecoveryCircleFamily_zero (z : Circle) :
    (oddKTheoryRecoveryCircleFamily z 0 : OddKTheoryRecoveryMatrix) =
      CStarMatrix.ofMatrix ![![(z : ℂ), 0], ![0, 1]] := by
  rw [oddKTheoryRecoveryCircleFamily_apply]
  change (1 - oddKTheoryRecoveryMovingProjection 0 (oddKTheoryCircleLoopParameter z)) +
    (oddKTheoryHalfPhase (2 * oddKTheoryCircleLoopParameter z) : ℂ) •
      oddKTheoryRecoveryMovingProjection 0 (oddKTheoryCircleLoopParameter z) = _
  rw [oddKTheoryRecoveryMovingProjection_zero]
  have hphase : (oddKTheoryHalfPhase (2 * oddKTheoryCircleLoopParameter z) : ℂ) = (z : ℂ) := by
    rw [oddKTheoryHalfPhase_coe_eq_exp]
    have he := congrArg (fun w : Circle => (w : ℂ)) (oddKTheoryCircleLoopParameter_phase z)
    rw [Circle.coe_exp] at he
    rw [← he]
    congr 1
    push_cast
    ring
  rw [hphase]
  change (1 - (CStarMatrix.ofMatrix !![1, 0; 0, 0] : OddKTheoryRecoveryMatrix)) +
    (z : ℂ) • CStarMatrix.ofMatrix !![1, 0; 0, 0] =
      CStarMatrix.ofMatrix !![(z : ℂ), 0; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [CStarMatrix.one_apply]

/-- The moving actual projection has exactly the four scalar rank-one
entries used in the exponential recovery formula. -/
theorem oddKTheoryRecoveryMovingProjection_entryMatrix (s t : ℝ) :
    oddKTheoryRecoveryMovingProjection s t = CStarMatrix.ofMatrix
      ![![oddKTheoryLoopProjectionScalarEntries (s * t) 0,
          oddKTheoryLoopProjectionScalarEntries (s * t) 1],
        ![oddKTheoryLoopProjectionScalarEntries (s * t) 2,
          oddKTheoryLoopProjectionScalarEntries (s * t) 3]] := by
  change star (oddKTheoryReflectionPhaseElement
      (CStarMatrix.ofMatrix !![0, 1; 1, 0] : OddKTheoryRecoveryMatrix)
      (oddKTheoryHalfPhase (s * t))) * CStarMatrix.ofMatrix !![1, 0; 0, 0] *
    oddKTheoryReflectionPhaseElement
      (CStarMatrix.ofMatrix !![0, 1; 1, 0] : OddKTheoryRecoveryMatrix)
      (oddKTheoryHalfPhase (s * t)) =
    CStarMatrix.ofMatrix !![oddKTheoryLoopProjectionScalarEntries (s * t) 0,
      oddKTheoryLoopProjectionScalarEntries (s * t) 1;
      oddKTheoryLoopProjectionScalarEntries (s * t) 2,
      oddKTheoryLoopProjectionScalarEntries (s * t) 3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oddKTheoryReflectionPhaseElement, CStarMatrix.mul_apply,
      CStarMatrix.star_apply, CStarMatrix.one_apply, Fin.sum_univ_two,
      oddKTheoryLoopProjectionScalarEntries]

/-- The upper endpoint is the actual four-entry exponential finite matrix. -/
theorem oddKTheoryRecoveryIntervalUnitary_one_entryMatrix (t : ℝ) :
    (oddKTheoryRecoveryIntervalUnitary 1 t : OddKTheoryRecoveryMatrix) =
      CStarMatrix.ofMatrix
        ![![1 + oddKTheoryLoopExponentialScalarEntry 0 t,
            oddKTheoryLoopExponentialScalarEntry 1 t],
          ![oddKTheoryLoopExponentialScalarEntry 2 t,
            1 + oddKTheoryLoopExponentialScalarEntry 3 t]] := by
  change (1 - oddKTheoryRecoveryMovingProjection 1 t) +
    (oddKTheoryHalfPhase (2 * t) : ℂ) • oddKTheoryRecoveryMovingProjection 1 t =
    CStarMatrix.ofMatrix !![1 + oddKTheoryLoopExponentialScalarEntry 0 t,
      oddKTheoryLoopExponentialScalarEntry 1 t;
      oddKTheoryLoopExponentialScalarEntry 2 t, 1 + oddKTheoryLoopExponentialScalarEntry 3 t]
  have hp := oddKTheoryRecoveryMovingProjection_entryMatrix 1 t
  change oddKTheoryRecoveryMovingProjection 1 t =
    CStarMatrix.ofMatrix !![oddKTheoryLoopProjectionScalarEntries (1 * t) 0,
      oddKTheoryLoopProjectionScalarEntries (1 * t) 1;
      oddKTheoryLoopProjectionScalarEntries (1 * t) 2,
      oddKTheoryLoopProjectionScalarEntries (1 * t) 3] at hp
  simp only [one_mul] at hp
  rw [hp, oddKTheoryHalfPhase_coe_eq_exp]
  have hphase : Complex.exp (((Real.pi * (2 * t) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) := by
    congr 1
    push_cast
    ring
  rw [hphase]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [CStarMatrix.add_apply, CStarMatrix.sub_apply, CStarMatrix.smul_apply,
      CStarMatrix.one_apply, oddKTheoryLoopExponentialScalarEntry_phase, smul_eq_mul]
  all_goals
    simp only [CStarMatrix.ofMatrix_apply, Matrix.of_apply]
    dsimp
    ring

theorem oddKTheoryRecoveryCircleEntry_target (i j : Fin 2) :
    oddKTheoryRecoveryCircleEntry 1 i j =
      CStarMatrix.ofMatrix
        ![![1 + oddKTheoryLoopExponentialCircleEntry 0,
            oddKTheoryLoopExponentialCircleEntry 1],
          ![oddKTheoryLoopExponentialCircleEntry 2,
            1 + oddKTheoryLoopExponentialCircleEntry 3]] i j := by
  apply ContinuousMap.ext
  intro z
  change (oddKTheoryRecoveryCircleFamily z 1 : OddKTheoryRecoveryMatrix) i j =
    (CStarMatrix.ofMatrix !![1 + oddKTheoryLoopExponentialCircleEntry 0,
      oddKTheoryLoopExponentialCircleEntry 1;
      oddKTheoryLoopExponentialCircleEntry 2, 1 + oddKTheoryLoopExponentialCircleEntry 3] i j) z
  rw [oddKTheoryRecoveryCircleFamily_apply]
  change (oddKTheoryRecoveryIntervalUnitary (1 : ℝ) (oddKTheoryCircleLoopParameter z) :
    OddKTheoryRecoveryMatrix) i j = _
  have hu := oddKTheoryRecoveryIntervalUnitary_one_entryMatrix (oddKTheoryCircleLoopParameter z)
  change (oddKTheoryRecoveryIntervalUnitary (1 : ℝ) (oddKTheoryCircleLoopParameter z) :
    OddKTheoryRecoveryMatrix) =
    CStarMatrix.ofMatrix !![1 + oddKTheoryLoopExponentialScalarEntry 0 (oddKTheoryCircleLoopParameter z),
      oddKTheoryLoopExponentialScalarEntry 1 (oddKTheoryCircleLoopParameter z);
      oddKTheoryLoopExponentialScalarEntry 2 (oddKTheoryCircleLoopParameter z),
      1 + oddKTheoryLoopExponentialScalarEntry 3 (oddKTheoryCircleLoopParameter z)] at hu
  rw [hu]
  fin_cases i <;> fin_cases j <;> rfl

end BC4lean.KKTheory
