import BC4lean.OddKTheoryLoopDefectPowerTransfer
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.ContinuousMap.Compact

/-! # Actual bounded weighted circle coefficient maps

Continuous functions on a compact scalar set containing the crossing interval
are evaluated at the interval eigenvalue and multiplied by the actual
vanishing defect entries. These products descend continuously to Circle.
Their explicit uniform bound bundles the four maps as actual complex
continuous linear maps, without evaluating a nonperiodic eigenvalue function
or a nonperiodic projection at a unitary.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped Topology CStarAlgebra

/-- The scalar crossing interval, embedded in the actual complex plane. -/
def oddKTheoryLoopEigenvalue (t : unitInterval) : ℂ := 2 * (t : ℂ) - 1

theorem continuous_oddKTheoryLoopEigenvalue : Continuous oddKTheoryLoopEigenvalue := by
  unfold oddKTheoryLoopEigenvalue
  fun_prop

/-- The actual scalar representative of a circle point is in the closed
unit interval; this assertion is used only for scalar coefficient identities. -/
theorem oddKTheoryCircleLoopParameter_mem_Icc (z : Circle) :
    oddKTheoryCircleLoopParameter z ∈ Set.Icc (0 : ℝ) 1 := by
  have h := (AddCircle.equivIco (1 : ℝ) 0
    ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm z)).property
  simpa only [oddKTheoryCircleLoopParameter, Set.mem_Icc, zero_add] using And.intro h.1 h.2.le

section WeightedEntries

variable (K : Set ℂ) [CompactSpace K]
  (hsegment : Set.range oddKTheoryLoopEigenvalue ⊆ K)

/-- A genuine continuous extension of the interval eigenvalue into K, using
the actual closed-interval projection for scalar functions only. -/
def oddKTheoryLoopClampedEigenvalue (t : ℝ) : K :=
  ⟨oddKTheoryLoopEigenvalue (Set.projIcc 0 1 (by norm_num) t),
    hsegment ⟨Set.projIcc 0 1 (by norm_num) t, rfl⟩⟩

omit [CompactSpace K] in
theorem continuous_oddKTheoryLoopClampedEigenvalue :
    Continuous (oddKTheoryLoopClampedEigenvalue K hsegment) :=
  (continuous_oddKTheoryLoopEigenvalue.comp continuous_projIcc).subtype_mk _

/-- The actual weighted interval defect entry. Its endpoint values are zero
regardless of the endpoint values of the continuous function. -/
def oddKTheoryLoopWeightedRawEntry (f : C(K, ℂ)) (i : Fin 4) (t : ℝ) : ℂ :=
  f (oddKTheoryLoopClampedEigenvalue K hsegment t) * oddKTheoryLoopDefectScalarEntries i t

omit [CompactSpace K] in
theorem continuous_oddKTheoryLoopWeightedRawEntry (f : C(K, ℂ)) (i : Fin 4) :
    Continuous (oddKTheoryLoopWeightedRawEntry K hsegment f i) :=
  (f.continuous.comp (continuous_oddKTheoryLoopClampedEigenvalue K hsegment)).mul
    (continuous_oddKTheoryLoopDefectScalarEntries i)

omit [CompactSpace K] in
@[simp] theorem oddKTheoryLoopWeightedRawEntry_zero (f : C(K, ℂ)) (i : Fin 4) :
    oddKTheoryLoopWeightedRawEntry K hsegment f i 0 = 0 := by
  simp [oddKTheoryLoopWeightedRawEntry]

omit [CompactSpace K] in
@[simp] theorem oddKTheoryLoopWeightedRawEntry_one (f : C(K, ℂ)) (i : Fin 4) :
    oddKTheoryLoopWeightedRawEntry K hsegment f i 1 = 0 := by
  simp [oddKTheoryLoopWeightedRawEntry]

/-- Actual continuous descended weighted defect coefficient. -/
def oddKTheoryLoopWeightedCircleEntry (f : C(K, ℂ)) (i : Fin 4) : C(Circle, ℂ) :=
  oddKTheoryDescendScalarLoop (oddKTheoryLoopWeightedRawEntry K hsegment f i)
    (continuous_oddKTheoryLoopWeightedRawEntry K hsegment f i) (by simp)

omit [CompactSpace K] in
@[simp] theorem oddKTheoryLoopWeightedCircleEntry_one_point (f : C(K, ℂ)) (i : Fin 4) :
    oddKTheoryLoopWeightedCircleEntry K hsegment f i 1 = 0 := by
  simp [oddKTheoryLoopWeightedCircleEntry]

omit [CompactSpace K] in
@[simp] theorem oddKTheoryLoopWeightedCircleEntry_one_function (i : Fin 4) :
    oddKTheoryLoopWeightedCircleEntry K hsegment (1 : C(K, ℂ)) i =
      oddKTheoryLoopDefectCircleEntry i := by
  ext z
  simp [oddKTheoryLoopWeightedCircleEntry, oddKTheoryLoopWeightedRawEntry,
    oddKTheoryLoopDefectCircleEntry, oddKTheoryDescendScalarLoop_apply]

omit [CompactSpace K] in
/-- Exact pointwise weighted-circle formula at the scalar representative. -/
theorem oddKTheoryLoopWeightedCircleEntry_apply (f : C(K, ℂ)) (i : Fin 4) (z : Circle) :
    oddKTheoryLoopWeightedCircleEntry K hsegment f i z =
      f (oddKTheoryLoopClampedEigenvalue K hsegment (oddKTheoryCircleLoopParameter z)) *
        oddKTheoryLoopDefectCircleEntry i z := rfl

/-- The explicit actual uniform bound needed for continuous coefficient
functional calculus transfer. -/
theorem oddKTheoryLoopWeightedCircleEntry_norm_le (f : C(K, ℂ)) (i : Fin 4) :
    ‖oddKTheoryLoopWeightedCircleEntry K hsegment f i‖ ≤
      ‖oddKTheoryLoopDefectCircleEntry i‖ * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro z
  rw [oddKTheoryLoopWeightedCircleEntry_apply, norm_mul, mul_comm]
  exact mul_le_mul (ContinuousMap.norm_coe_le_norm _ z)
    (ContinuousMap.norm_coe_le_norm f _) (norm_nonneg _) (norm_nonneg _)

/-- The weighted circle coefficient construction is genuinely complex linear. -/
def oddKTheoryLoopWeightedCircleEntryLinear (i : Fin 4) : C(K, ℂ) →ₗ[ℂ] C(Circle, ℂ) where
  toFun f := oddKTheoryLoopWeightedCircleEntry K hsegment f i
  map_add' f g := by
    ext z
    simp only [oddKTheoryLoopWeightedCircleEntry_apply, ContinuousMap.add_apply, add_mul]
  map_smul' c f := by
    ext z
    simp only [oddKTheoryLoopWeightedCircleEntry_apply, ContinuousMap.smul_apply,
      smul_eq_mul, mul_assoc, RingHom.id_apply]

/-- The actual bounded complex linear weighted coefficient map. -/
def oddKTheoryLoopWeightedCircleEntryCLM (i : Fin 4) : C(K, ℂ) →L[ℂ] C(Circle, ℂ) :=
  (oddKTheoryLoopWeightedCircleEntryLinear K hsegment i).mkContinuous
    ‖oddKTheoryLoopDefectCircleEntry i‖ (fun f => oddKTheoryLoopWeightedCircleEntry_norm_le K hsegment f i)

@[simp] theorem oddKTheoryLoopWeightedCircleEntryCLM_apply (i : Fin 4) (f : C(K, ℂ)) :
    oddKTheoryLoopWeightedCircleEntryCLM K hsegment i f =
      oddKTheoryLoopWeightedCircleEntry K hsegment f i := rfl

end WeightedEntries
end BC4lean.KKTheory
