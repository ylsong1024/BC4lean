import BC4lean.FullGradedKasparovHomotopy
import BC4lean.KasparovHomotopyGroup
import BC4lean.IntervalModuleFibreNorm

/-! # Genuine full witnesses in the trivial algebra-grading specialization

Both conversions preserve the actual module, representation and operator.
For interval coefficients the module grading is rebuilt with the same
isometry and the actual pointwise trivial inner law. Fibre identifications
are proved on the genuine onto canonical fibre maps.
-/

noncomputable section
universe u
namespace BC4lean.KKTheory.GradedMatrixMoritaEvenBase
open scoped InnerProductSpace

variable {Γ A B : Type u} [Group Γ] [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

def toEven (c : BundledGradedKasparovCycle.{u,u,u,u} α β CStarGrading.trivial CStarGrading.trivial) :
    BundledKasparovCycle.{u,u,u,u} α β := .of c.cycle.toKasparovCycle

def ofEven (c : BundledKasparovCycle.{u,u,u,u} α β) :
    BundledGradedKasparovCycle.{u,u,u,u} α β CStarGrading.trivial CStarGrading.trivial :=
  .of (GradedKasparovCycle.ofKasparovCycle c.cycle)

@[simp] theorem toEven_ofEven (c : BundledKasparovCycle.{u,u,u,u} α β) : toEven (ofEven c) = c := by
  change BundledKasparovCycle.of
    ((GradedKasparovCycle.ofKasparovCycle c.cycle).toKasparovCycle) = c
  rw [GradedKasparovCycle.toKasparovCycle_ofKasparovCycle, BundledKasparovCycle.of_storedCycle]

@[simp] theorem ofEven_toEven
    (c : BundledGradedKasparovCycle.{u,u,u,u} α β CStarGrading.trivial CStarGrading.trivial) :
    ofEven (toEven c) = c := by
  change BundledGradedKasparovCycle.of
    (GradedKasparovCycle.ofKasparovCycle c.cycle.toKasparovCycle) = c
  rw [GradedKasparovCycle.ofKasparovCycle_toKasparovCycle, BundledGradedKasparovCycle.of_storedCycle]

def inverseIso
    (c : BundledGradedKasparovCycle.{u,u,u,u} α β CStarGrading.trivial CStarGrading.trivial) :
    (ofEven (toEven c)).Iso c where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

section Raw

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]

def isoToEven {c : GradedKasparovCycle α β CStarGrading.trivial CStarGrading.trivial E}
    {d : GradedKasparovCycle α β CStarGrading.trivial CStarGrading.trivial F}
    (e : GradedKasparovCycleIso c d) : KasparovCycleIso c.toKasparovCycle d.toKasparovCycle where
  moduleEquiv := e.moduleEquiv
  grading_intertwine := e.grading_intertwine
  action_intertwine := e.action_intertwine
  representation_intertwine := e.representation_intertwine
  operator_intertwine := e.operator_intertwine

def isoOfEven {c : KasparovCycle α β E} {d : KasparovCycle α β F}
    (e : KasparovCycleIso c d) : GradedKasparovCycleIso
      (GradedKasparovCycle.ofKasparovCycle c) (GradedKasparovCycle.ofKasparovCycle d) where
  moduleEquiv := e.moduleEquiv
  grading_intertwine := e.grading_intertwine
  action_intertwine := e.action_intertwine
  representation_intertwine := e.representation_intertwine
  operator_intertwine := e.operator_intertwine

end Raw

@[simp] theorem trivialSectionAutomorphism (b : C(unitInterval, B)) :
    (CStarGrading.trivial : CStarGrading B).continuousSections.automorphism b = b := by
  ext t
  rfl

section Interval

variable {M : Type u} [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(unitInterval, B)ᵐᵒᵖ M] [CStarModule C(unitInterval, B)ᵐᵒᵖ M] [CompleteSpace M]

def sectionToEven
    (c : GradedKasparovCycle α (β.continuousSections (X := unitInterval)) CStarGrading.trivial
      (CStarGrading.trivial : CStarGrading B).continuousSections M) :
    KasparovCycle α (β.continuousSections (X := unitInterval)) M where
  countablyGenerated := c.countablyGenerated
  grading :=
    { grading := c.grading.grading
      involutive := c.grading.involutive
      inner_grading x y := by
        change ⟪c.grading.grading x, c.grading.grading y⟫_(C(unitInterval, B)ᵐᵒᵖ) =
          ⟪x, y⟫_(C(unitInterval, B)ᵐᵒᵖ)
        simpa only [opStarAlgEquiv_apply, trivialSectionAutomorphism, MulOpposite.op_unop] using
          c.grading.inner_grading x y }
  groupAction := c.groupAction
  grading_preserved := c.grading_preserved
  representation := c.representation
  representation_even := c.representation_graded
  representation_equivariant := c.representation_equivariant
  operator := c.operator
  operator_odd := c.operator_odd
  selfadjoint_mod_compact := c.selfadjoint_mod_compact
  square_mod_compact := c.square_mod_compact
  commutator_compact := c.commutator_compact
  equivariance_mod_compact := c.equivariance_mod_compact

def sectionOfEven (c : KasparovCycle α (β.continuousSections (X := unitInterval)) M) :
    GradedKasparovCycle α (β.continuousSections (X := unitInterval)) CStarGrading.trivial
      (CStarGrading.trivial : CStarGrading B).continuousSections M where
  sourceAction_preservesGrading := α.preservesGrading_trivial
  coefficientAction_preservesGrading :=
    CStarAlgebraAction.preservesGrading_continuousSections
      (X := unitInterval) β.preservesGrading_trivial
  countablyGenerated := c.countablyGenerated
  grading :=
    { grading := c.grading.grading
      involutive := c.grading.involutive
      inner_grading x y := by
        change ⟪c.grading.grading x, c.grading.grading y⟫_(C(unitInterval, B)ᵐᵒᵖ) =
          MulOpposite.op ((CStarGrading.trivial : CStarGrading B).continuousSections.automorphism
            (MulOpposite.unop ⟪x, y⟫_(C(unitInterval, B)ᵐᵒᵖ)))
        rw [trivialSectionAutomorphism, MulOpposite.op_unop]
        exact c.grading.inner_grading x y }
  groupAction := c.groupAction
  grading_preserved := c.grading_preserved
  representation := c.representation
  representation_graded := c.representation_even
  representation_equivariant := c.representation_equivariant
  operator := c.operator
  operator_odd := c.operator_odd
  selfadjoint_mod_compact := c.selfadjoint_mod_compact
  square_mod_compact := c.square_mod_compact
  commutator_compact := c.commutator_compact
  equivariance_mod_compact := c.equivariance_mod_compact

def sectionToEvenFibreIso
    (c : GradedKasparovCycle α (β.continuousSections (X := unitInterval)) CStarGrading.trivial
      (CStarGrading.trivial : CStarGrading B).continuousSections M) (t : unitInterval) :
    KasparovCycleIso ((sectionToEven c).fibre t) (c.fibre t).toKasparovCycle where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine z := by
    change ((sectionToEven c).grading.fibre t).grading z = (c.grading.gradedFibre t).grading z
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := M) t z
    rw [GradedHilbertModule.fibre_grading_mk, GradedHilbertModule.gradedFibre_grading_mk]
    rfl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

def sectionOfEvenFibreIso (c : KasparovCycle α (β.continuousSections (X := unitInterval)) M)
    (t : unitInterval) : GradedKasparovCycleIso ((sectionOfEven c).fibre t)
      (GradedKasparovCycle.ofKasparovCycle (c.fibre t)) where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine z := by
    change ((sectionOfEven c).grading.gradedFibre t).grading z = (c.grading.fibre t).grading z
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := M) t z
    rw [GradedHilbertModule.gradedFibre_grading_mk, GradedHilbertModule.fibre_grading_mk]
    rfl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

end Interval

def fullToEven
    {c d : BundledGradedKasparovCycle.{u,u,u,u} α β CStarGrading.trivial CStarGrading.trivial}
    (h : FullGradedKasparovHomotopy c d) : FullKasparovHomotopy (toEven c) (toEven d) where
  intervalCycle := .of (sectionToEven h.intervalCycle.cycle)
  sourceIso := (sectionToEvenFibreIso h.intervalCycle.cycle 0).trans (isoToEven h.sourceIso)
  targetIso := (sectionToEvenFibreIso h.intervalCycle.cycle 1).trans (isoToEven h.targetIso)

def fullOfEven {c d : BundledKasparovCycle.{u,u,u,u} α β}
    (h : FullKasparovHomotopy c d) : FullGradedKasparovHomotopy (ofEven c) (ofEven d) where
  intervalCycle := .of (sectionOfEven h.intervalCycle.cycle)
  sourceIso := (sectionOfEvenFibreIso h.intervalCycle.cycle 0).trans (isoOfEven h.sourceIso)
  targetIso := (sectionOfEvenFibreIso h.intervalCycle.cycle 1).trans (isoOfEven h.targetIso)

theorem full_iff_toEven
    (c d : BundledGradedKasparovCycle.{u,u,u,u} α β CStarGrading.trivial CStarGrading.trivial) :
    Nonempty (FullGradedKasparovHomotopy c d) ↔ Nonempty (FullKasparovHomotopy (toEven c) (toEven d)) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨fullToEven h⟩
  · rintro ⟨h⟩
    exact ⟨(fullOfEven h).changeEndpoints (inverseIso c) (inverseIso d)⟩

variable [TopologicalSpace.SeparableSpace B]

theorem full_iff_homotopic
    (c d : BundledGradedKasparovCycle.{u,u,u,u} α β CStarGrading.trivial CStarGrading.trivial) :
    Nonempty (FullGradedKasparovHomotopy c d) ↔ (toEven c).Homotopic (toEven d) :=
  (full_iff_toEven c d).trans BundledKasparovCycle.homotopic_iff_full.symm

/-- Single genuine graded witnesses form a setoid here by the proved even gluing theorem. -/
def fullSetoid : Setoid (BundledGradedKasparovCycle.{u,u,u,u} α β CStarGrading.trivial CStarGrading.trivial) where
  r c d := Nonempty (FullGradedKasparovHomotopy c d)
  iseqv :=
    { refl c := (full_iff_homotopic c c).mpr
        (BundledKasparovCycle.homotopySetoid.iseqv.refl (toEven c))
      symm := by
        intro c d h
        exact (full_iff_homotopic d c).mpr
          (BundledKasparovCycle.homotopySetoid.iseqv.symm ((full_iff_homotopic c d).mp h))
      trans := by
        intro c d e h h'
        exact (full_iff_homotopic c e).mpr
          (BundledKasparovCycle.homotopySetoid.iseqv.trans
            ((full_iff_homotopic c d).mp h) ((full_iff_homotopic d e).mp h')) }

def ofIso
    {c d : BundledGradedKasparovCycle.{u,u,u,u} α β CStarGrading.trivial CStarGrading.trivial}
    (e : c.Iso d) : FullGradedKasparovHomotopy c d :=
  (fullOfEven (FullKasparovHomotopy.ofIso (isoToEven e))).changeEndpoints (inverseIso c) (inverseIso d)

end BC4lean.KKTheory.GradedMatrixMoritaEvenBase
