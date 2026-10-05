import BC4lean.ClosedStageTelescope
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Tactic.Linarith

/-! # Lifting a controlled contraction through telescope height
A continuous height bound on a homotopy is sufficient. This is a local-control
interface; it does not presume uniform control over a group-orbit stage.
-/
noncomputable section
open scoped unitInterval
namespace BC4lean.ClosedStageTelescope
variable {X : Type*} [TopologicalSpace X]
variable (E : ℕ → Set X) (hm : Monotone E)

include hm in
omit [TopologicalSpace X] in
/-- Increasing the height preserves a telescope point. -/
theorem carrier_raise (p : Telescope E) (q : ℝ) (hq : p.val.2 ≤ q) :
    (p.val.1, q) ∈ carrier E := by
  obtain ⟨n, hn, ht⟩ := p.property
  have hnq : (n : ℝ) ≤ q := ht.1.trans hq
  have hq0 : 0 ≤ q := (Nat.cast_nonneg n).trans hnq
  exact ⟨⌊q⌋₊, hm (Nat.le_floor hnq) hn,
    Nat.floor_le hq0, (Nat.lt_floor_add_one q).le⟩

def raisedMap (q : C(Telescope E, ℝ)) (hq : ∀ p, p.val.2 ≤ q p) :
    C(Telescope E, Telescope E) where
  toFun p := ⟨(p.val.1, q p), carrier_raise E hm p (q p) (hq p)⟩
  continuous_toFun := ((continuous_fst.comp continuous_subtype_val).prodMk q.continuous).subtype_mk _

def verticalRaise (q : C(Telescope E, ℝ)) (hq : ∀ p, p.val.2 ≤ q p) :
    ContinuousMap.Homotopy (ContinuousMap.id (Telescope E)) (raisedMap E hm q hq) where
  toFun p := ⟨(p.2.val.1, (1 - (p.1 : ℝ)) * p.2.val.2 + (p.1 : ℝ) * q p.2), by
    apply carrier_raise E hm p.2
    have hnonneg : 0 ≤ (p.1 : ℝ) * (q p.2 - p.2.val.2) :=
      mul_nonneg p.1.property.1 (sub_nonneg.mpr (hq p.2))
    nlinarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact continuous_fst.comp (continuous_subtype_val.comp continuous_snd)
    · exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))).add
        ((continuous_subtype_val.comp continuous_fst).mul (q.continuous.comp continuous_snd))
  map_zero_left p := by apply Subtype.ext; apply Prod.ext; rfl; simp
  map_one_left p := by apply Subtype.ext; apply Prod.ext; rfl; simp [raisedMap]

/-- The projection as a bundled map. -/
def projectionMap : C(Telescope E, X) where
  toFun p := p.val.1
  continuous_toFun := continuous_projection E

include hm in
omit [TopologicalSpace X] in
/-- A fixed base point can occur at every height above an admissible integer. -/
theorem constantBase_mem (x₀ : X) (n₀ : ℕ) (hx₀ : x₀ ∈ E n₀)
    (q : ℝ) (hq : (n₀ : ℝ) ≤ q) : (x₀,q) ∈ carrier E :=
  ⟨⌊q⌋₊, hm (Nat.le_floor hq) hx₀,
    Nat.floor_le ((Nat.cast_nonneg n₀).trans hq), (Nat.lt_floor_add_one q).le⟩

def constantBaseMap (x₀ : X) (n₀ : ℕ) (hx₀ : x₀ ∈ E n₀)
    (q : C(Telescope E, ℝ)) (hq : ∀ p, (n₀ : ℝ) ≤ q p) :
    C(Telescope E, Telescope E) where
  toFun p := ⟨(x₀,q p), constantBase_mem E hm x₀ n₀ hx₀ (q p) (hq p)⟩
  continuous_toFun := (continuous_const.prodMk q.continuous).subtype_mk _

/-- A homotopy controlled at a continuous height lifts directly to the telescope. -/
def controlledLift (x₀ : X) (n₀ : ℕ) (hx₀ : x₀ ∈ E n₀)
    (C : ContinuousMap.Homotopy (projectionMap E) (ContinuousMap.const _ x₀))
    (q : C(Telescope E, ℝ)) (hq : ∀ p, p.val.2 ≤ q p)
    (hnq : ∀ p, (n₀ : ℝ) ≤ q p)
    (hb : ∀ t p, C (t,p) ∈ E ⌊q p⌋₊) :
    ContinuousMap.Homotopy (raisedMap E hm q hq)
      (constantBaseMap E hm x₀ n₀ hx₀ q hnq) := by
  refine
    { toFun := fun p => ⟨(C p, q p.2), ?_⟩
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_ }
  · refine ⟨⌊q p.2⌋₊, hb p.1 p.2, ?_, (Nat.lt_floor_add_one (q p.2)).le⟩
    obtain ⟨n, _, ht⟩ := p.2.property
    exact Nat.floor_le ((Nat.cast_nonneg n).trans (ht.1.trans (hq p.2)))
  · exact (C.continuous.prodMk (q.continuous.comp continuous_snd)).subtype_mk _
  · intro p
    exact Subtype.ext (Prod.ext (C.map_zero_left p) rfl)
  · intro p
    exact Subtype.ext (Prod.ext (C.map_one_left p) rfl)

/-- Contract the remaining height coordinate along the fixed vertical ray. -/
def lowerConstantBase (x₀ : X) (n₀ : ℕ) (hx₀ : x₀ ∈ E n₀)
    (q : C(Telescope E, ℝ)) (hq : ∀ p, (n₀ : ℝ) ≤ q p) :
    ContinuousMap.Homotopy (constantBaseMap E hm x₀ n₀ hx₀ q hq)
      (ContinuousMap.const _ (⟨(x₀,(n₀ : ℝ)), n₀, hx₀, le_rfl,
        le_add_of_nonneg_right zero_le_one⟩ : Telescope E)) where
  toFun p := ⟨(x₀, (1-(p.1 : ℝ))*q p.2 + (p.1 : ℝ)*(n₀ : ℝ)), by
    apply constantBase_mem E hm x₀ n₀ hx₀
    have hnonneg : 0 ≤ (1-(p.1 : ℝ))*(q p.2-(n₀ : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr p.1.property.2) (sub_nonneg.mpr (hq p.2))
    nlinarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk continuous_const
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (q.continuous.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).mul continuous_const)
  map_zero_left p := by apply Subtype.ext; apply Prod.ext; rfl; simp [constantBaseMap]
  map_one_left p := by apply Subtype.ext; apply Prod.ext; rfl; simp

include hm in
/-- A contraction of the projected points with a continuous stage bound yields
an actual contraction of the telescope. -/
theorem contractible_of_controlled (x₀ : X) (n₀ : ℕ) (hx₀ : x₀ ∈ E n₀)
    (C : ContinuousMap.Homotopy (projectionMap E) (ContinuousMap.const _ x₀))
    (q : C(Telescope E, ℝ)) (hq : ∀ p, p.val.2 ≤ q p)
    (hnq : ∀ p, (n₀ : ℝ) ≤ q p)
    (hb : ∀ t p, C (t,p) ∈ E ⌊q p⌋₊) : ContractibleSpace (Telescope E) := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  let p₀ : Telescope E := ⟨(x₀,(n₀ : ℝ)), n₀, hx₀, le_rfl,
    le_add_of_nonneg_right zero_le_one⟩
  refine ⟨p₀, ⟨?_⟩⟩
  have h₂ := controlledLift E hm x₀ n₀ hx₀ C q hq hnq hb
  exact ((verticalRaise E hm q hq).trans h₂).trans
    (lowerConstantBase E hm x₀ n₀ hx₀ q hnq)

end BC4lean.ClosedStageTelescope
