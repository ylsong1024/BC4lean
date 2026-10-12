import BC4lean.OddFredholmExponential
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Topology.Path
import Mathlib.Tactic.NoncommRing

/-! # Genuine forced-unitization representatives of odd exponential indices

A unitary on an actual Hilbert module whose difference from the identity is
compact gives a unitary with scalar part exactly one in the forced unitization
of its compact operator algebra. The proof keeps the scalar coordinate, and
therefore also applies when the identity operator itself is compact.

Norm-continuous paths lift to genuine unitary paths in that forced unitization.
This is an analytic forward construction; it does not identify the compact
operator algebra K-group with the coefficient K-group or assert the missing
odd recovery isomorphism.
-/

noncomputable section
namespace BC4lean.KKTheory

open unitInterval

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

/-- The genuine compact coefficient of a unitary compact perturbation. -/
def compactPerturbationUnitaryCoefficient
    (U : unitary (AdjointableMap B E E))
    (hU : IsModuleCompact ((U : AdjointableMap B E E) - 1)) :
    CompactModuleOperator B E :=
  ⟨(U : AdjointableMap B E E) - 1, hU⟩

omit [CompleteSpace E] in
@[simp] theorem compactPerturbationUnitaryCoefficient_coe
    (U : unitary (AdjointableMap B E E))
    (hU : IsModuleCompact ((U : AdjointableMap B E E) - 1)) :
    (compactPerturbationUnitaryCoefficient U hU : AdjointableMap B E E) =
      (U : AdjointableMap B E E) - 1 := rfl

/-- The actual forced-unitization element retains scalar coordinate `1`. -/
def compactPerturbationUnitaryElement
    (U : unitary (AdjointableMap B E E))
    (hU : IsModuleCompact ((U : AdjointableMap B E E) - 1)) :
    Unitization ℂ (CompactModuleOperator B E) :=
  1 + (compactPerturbationUnitaryCoefficient U hU :
    Unitization ℂ (CompactModuleOperator B E))

omit [CompleteSpace E] in
@[simp] theorem compactPerturbationUnitaryElement_fst
    (U : unitary (AdjointableMap B E E))
    (hU : IsModuleCompact ((U : AdjointableMap B E E) - 1)) :
    (compactPerturbationUnitaryElement U hU).fst = 1 := by
  simp [compactPerturbationUnitaryElement]

omit [CompleteSpace E] in
@[simp] theorem compactPerturbationUnitaryElement_snd
    (U : unitary (AdjointableMap B E E))
    (hU : IsModuleCompact ((U : AdjointableMap B E E) - 1)) :
    (compactPerturbationUnitaryElement U hU).snd =
      compactPerturbationUnitaryCoefficient U hU := by
  simp [compactPerturbationUnitaryElement]

/-- Unitarity follows by expanding the genuine scalar-one unitization product,
using both actual unitary identities of the represented operator. -/
theorem compactPerturbationUnitaryElement_mem_unitary
    (U : unitary (AdjointableMap B E E))
    (hU : IsModuleCompact ((U : AdjointableMap B E E) - 1)) :
    compactPerturbationUnitaryElement U hU ∈
      unitary (Unitization ℂ (CompactModuleOperator B E)) := by
  apply Unitary.mem_iff.mpr
  constructor
  · apply Unitization.ext
    · simp
    · simp only [Unitization.snd_mul, Unitization.snd_star,
        compactPerturbationUnitaryElement_fst, compactPerturbationUnitaryElement_snd,
        Unitization.fst_star, star_one, one_smul, Unitization.snd_one]
      apply Subtype.ext
      change ((U : AdjointableMap B E E) - 1) +
        star ((U : AdjointableMap B E E) - 1) +
        star ((U : AdjointableMap B E E) - 1) *
          ((U : AdjointableMap B E E) - 1) = 0
      rw [star_sub, star_one]
      calc
        _ = star (U : AdjointableMap B E E) * (U : AdjointableMap B E E) - 1 := by
          noncomm_ring
        _ = 0 := by rw [(Unitary.mem_iff.mp U.property).1, sub_self]
  · apply Unitization.ext
    · simp
    · simp only [Unitization.snd_mul, Unitization.snd_star,
        compactPerturbationUnitaryElement_fst, compactPerturbationUnitaryElement_snd,
        Unitization.fst_star, star_one, one_smul, Unitization.snd_one]
      apply Subtype.ext
      change star ((U : AdjointableMap B E E) - 1) +
        ((U : AdjointableMap B E E) - 1) +
        ((U : AdjointableMap B E E) - 1) *
          star ((U : AdjointableMap B E E) - 1) = 0
      rw [star_sub, star_one]
      calc
        _ = (U : AdjointableMap B E E) * star (U : AdjointableMap B E E) - 1 := by
          noncomm_ring
        _ = 0 := by rw [(Unitary.mem_iff.mp U.property).2, sub_self]

/-- The genuine unitary of the forced compact-operator unitization. -/
def compactPerturbationUnitary
    (U : unitary (AdjointableMap B E E))
    (hU : IsModuleCompact ((U : AdjointableMap B E E) - 1)) :
    unitary (Unitization ℂ (CompactModuleOperator B E)) :=
  ⟨compactPerturbationUnitaryElement U hU,
    compactPerturbationUnitaryElement_mem_unitary U hU⟩

@[simp] theorem compactPerturbationUnitary_fst
    (U : unitary (AdjointableMap B E E))
    (hU : IsModuleCompact ((U : AdjointableMap B E E) - 1)) :
    (compactPerturbationUnitary U hU : Unitization ℂ (CompactModuleOperator B E)).fst = 1 :=
  compactPerturbationUnitaryElement_fst U hU

/-- Continuity of the actual unitization representative, proved with the
induced norm topology on genuine compact module maps. -/
theorem continuous_compactPerturbationUnitary
    {X : Type*} [TopologicalSpace X]
    (U : X → unitary (AdjointableMap B E E)) (hU : Continuous U)
    (hCompact : ∀ x, IsModuleCompact ((U x : AdjointableMap B E E) - 1)) :
    Continuous (fun x => compactPerturbationUnitary (U x) (hCompact x)) := by
  have hK : Continuous (fun x => compactPerturbationUnitaryCoefficient (U x) (hCompact x)) :=
    ((continuous_subtype_val.comp hU).sub continuous_const).subtype_mk _
  have hElement : Continuous (fun x => compactPerturbationUnitaryElement (U x) (hCompact x)) :=
    continuous_const.add (Unitization.continuous_inr.comp hK)
  exact hElement.subtype_mk _

/-- A genuine norm path of compact-perturbation unitaries lifts to a norm path
in the forced compact-operator unitization, retaining scalar part one. -/
def compactPerturbationUnitaryPath
    {U₀ U₁ : unitary (AdjointableMap B E E)} (p : Path U₀ U₁)
    (hCompact : ∀ t : I, IsModuleCompact ((p t : AdjointableMap B E E) - 1)) :
    Path (compactPerturbationUnitary U₀ (by simpa only [Path.source] using hCompact 0))
      (compactPerturbationUnitary U₁ (by simpa only [Path.target] using hCompact 1)) where
  toFun t := compactPerturbationUnitary (p t) (hCompact t)
  continuous_toFun := continuous_compactPerturbationUnitary p p.continuous hCompact
  source' := by simp only [Path.source]
  target' := by simp only [Path.target]

/-- The actual odd exponential index representative in the forced unitization
of the actual compact operator algebra of the specified module. -/
def oddFredholmCompactUnitary
    (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) * (F : AdjointableMap B E E) - 1)) :
    unitary (Unitization ℂ (CompactModuleOperator B E)) :=
  compactPerturbationUnitary (oddFredholmExponential F)
    (oddFredholmExponential_sub_one_isModuleCompact F hF)

@[simp] theorem oddFredholmCompactUnitary_fst
    (F : selfAdjoint (AdjointableMap B E E))
    (hF : IsModuleCompact ((F : AdjointableMap B E E) * (F : AdjointableMap B E E) - 1)) :
    (oddFredholmCompactUnitary F hF : Unitization ℂ (CompactModuleOperator B E)).fst = 1 :=
  compactPerturbationUnitary_fst _ _

/-- A norm-continuous family of actual selfadjoint Fredholm operators gives a
norm-continuous family of scalar-one compact-unitization index unitaries. -/
theorem continuous_oddFredholmCompactUnitary
    {X : Type*} [TopologicalSpace X]
    (F : X → selfAdjoint (AdjointableMap B E E)) (hF : Continuous F)
    (hCompact : ∀ x, IsModuleCompact
      ((F x : AdjointableMap B E E) * (F x : AdjointableMap B E E) - 1)) :
    Continuous (fun x => oddFredholmCompactUnitary (F x) (hCompact x)) := by
  have hU : Continuous (fun x => oddFredholmExponential (A := AdjointableMap B E E) (F x)) :=
    (continuous_oddFredholmExponential (A := AdjointableMap B E E)).comp hF
  exact continuous_compactPerturbationUnitary (B := B) (E := E) (X := X)
    (fun x => oddFredholmExponential (A := AdjointableMap B E E) (F x)) hU
    (fun x => oddFredholmExponential_sub_one_isModuleCompact
      (B := B) (E := E) (F x) (hCompact x))

/-- The forward exponential construction respects actual selfadjoint Fredholm
operator paths on the specified module. -/
def oddFredholmCompactUnitaryPath
    {F₀ F₁ : selfAdjoint (AdjointableMap B E E)} (p : Path F₀ F₁)
    (hCompact : ∀ t : I, IsModuleCompact
      ((p t : AdjointableMap B E E) * (p t : AdjointableMap B E E) - 1)) :
    Path (oddFredholmCompactUnitary F₀ (by simpa only [Path.source] using hCompact 0))
      (oddFredholmCompactUnitary F₁ (by simpa only [Path.target] using hCompact 1)) where
  toFun t := oddFredholmCompactUnitary (p t) (hCompact t)
  continuous_toFun := continuous_oddFredholmCompactUnitary p p.continuous hCompact
  source' := by simp only [Path.source]
  target' := by simp only [Path.target]

end BC4lean.KKTheory
