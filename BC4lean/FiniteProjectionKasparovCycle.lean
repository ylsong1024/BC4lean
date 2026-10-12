import BC4lean.FiniteProjectionModule
import BC4lean.KasparovCycleIso
import BC4lean.StableProjectionMonoid

/-! # Genuine Kasparov cycles of finite projection ranges

For a finite projection over a unital coefficient C*-algebra, its supported
right module has compact identity. Scalar multiplication with the even grading
and zero Fredholm operator is therefore an actual even Kasparov cycle. A
rectangular Murray--von Neumann witness restricts to an isomorphism of these
cycles. This records the concrete data needed before descending to stable
projection classes; no K0/KK equivalence is asserted.

The possibly nonunital K0 target is a kernel in the K0 of the unitization.
Unitization projections with nonzero scalar image require scalar cancellation
before producing cycles over the original coefficient algebra; they are not
silently treated as projections in that algebra here.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped Matrix

variable {Γ B E : Type*} [Group Γ]

section ScalarRepresentation
variable [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

/-- Scalar multiplication, bundled as the actual complex star representation. -/
def scalarModuleRepresentation : ℂ →⋆ₙₐ[ℂ] AdjointableMap B E E :=
  (StarAlgHom.ofId ℂ (AdjointableMap B E E)).toNonUnitalStarAlgHom

@[simp] theorem scalarModuleRepresentation_apply (a : ℂ) (x : E) :
    scalarModuleRepresentation (B := B) a x = a • x := by
  change (algebraMap ℂ (AdjointableMap B E E) a) x = a • x
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

theorem scalarModuleRepresentation_eq_smul_one (a : ℂ) :
    scalarModuleRepresentation (B := B) (E := E) a = a • 1 :=
  Algebra.algebraMap_eq_smul_one a

variable [StarOrderedRing B]

/-- A module with compact identity has a compact scalar representation. -/
theorem scalarModuleRepresentation_isModuleCompact
    (h : IsModuleCompact (1 : AdjointableMap B E E)) (a : ℂ) :
    IsModuleCompact (scalarModuleRepresentation (B := B) (E := E) a) := by
  rw [scalarModuleRepresentation_eq_smul_one]
  exact h.smul a

end ScalarRepresentation

section CompactIdentityCycle
variable [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- The actual even scalar cycle of a countably generated module with compact identity. -/
def compactIdentityScalarCycle (hE : IsCountablyGeneratedModule B E)
    (hI : IsModuleCompact (1 : AdjointableMap B E E)) :
    KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B) E where
  countablyGenerated := hE
  grading := GradedHilbertModule.trivial
  groupAction := EquivariantHilbertModule.trivial
  grading_preserved := by intro g x; rfl
  representation := scalarModuleRepresentation
  representation_even := by intro a x; rfl
  representation_equivariant := by intro g a; ext x; rfl
  operator := 0
  operator_odd := by intro x; simp
  selfadjoint_mod_compact := by
    intro a
    simpa using IsModuleCompact.zero (B := B) (E := E) (F := E)
  square_mod_compact := by
    intro a
    simpa using (scalarModuleRepresentation_isModuleCompact hI a).neg
  commutator_compact := by
    intro a
    simpa using IsModuleCompact.zero (B := B) (E := E) (F := E)
  equivariance_mod_compact := by
    intro g a
    change IsModuleCompact
      (((EquivariantHilbertModule.trivial : EquivariantHilbertModule
        (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B) E).conjugateOperator g
          (AdjointableMap.zero (B := B) (E := E) (F := E)) - AdjointableMap.zero) *
        scalarModuleRepresentation a)
    rw [EquivariantHilbertModule.conjugateOperator_zero]
    simpa using IsModuleCompact.zero (B := B) (E := E) (F := E)

@[simp] theorem compactIdentityScalarCycle_operator (hE : IsCountablyGeneratedModule B E)
    (hI : IsModuleCompact (1 : AdjointableMap B E E)) :
    (compactIdentityScalarCycle (Γ := Γ) hE hI).operator = 0 := rfl

@[simp] theorem compactIdentityScalarCycle_representation (hE : IsCountablyGeneratedModule B E)
    (hI : IsModuleCompact (1 : AdjointableMap B E E)) (a : ℂ) :
    (compactIdentityScalarCycle (Γ := Γ) hE hI).representation a = scalarModuleRepresentation a := rfl

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
  [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]

/-- A genuine Hilbert-module unitary intertwines all data of these scalar cycles. -/
def compactIdentityScalarCycleIso
    (hE : IsCountablyGeneratedModule B E) (hF : IsCountablyGeneratedModule B F)
    (hIE : IsModuleCompact (1 : AdjointableMap B E E))
    (hIF : IsModuleCompact (1 : AdjointableMap B F F)) (u : HilbertModuleEquiv B E F) :
    KasparovCycleIso (compactIdentityScalarCycle (Γ := Γ) hE hIE)
      (compactIdentityScalarCycle (Γ := Γ) hF hIF) where
  moduleEquiv := u
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine a x := by
    change u (scalarModuleRepresentation a x) = scalarModuleRepresentation a (u x)
    simp only [scalarModuleRepresentation_apply, HilbertModuleEquiv.map_smul]
  operator_intertwine x := u.map_zero

end CompactIdentityCycle

section FiniteProjectionCycle
variable [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The actual projection-supported even cycle, with no separability assumption on B.
Finite unital generation and complete closed ranges were proved independently. -/
def finiteProjectionRangeCycle (p : BC4lean.OperatorKTheory.FiniteProjection B) :
    KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B) (FiniteProjectionModule p.projection) :=
  compactIdentityScalarCycle (finiteProjectionModule_isCountablyGenerated p.projection)
    (finiteProjectionModule_identity_isModuleCompact p.projection)

@[simp] theorem finiteProjectionRangeCycle_operator (p : BC4lean.OperatorKTheory.FiniteProjection B) :
    (finiteProjectionRangeCycle (Γ := Γ) p).operator = 0 := rfl

@[simp] theorem finiteProjectionRangeCycle_representation
    (p : BC4lean.OperatorKTheory.FiniteProjection B) (a : ℂ) :
    (finiteProjectionRangeCycle (Γ := Γ) p).representation a = scalarModuleRepresentation a := rfl

/-- A specified rectangular witness induces an actual cycle isomorphism via its adjoint.
The ambient rectangular operator is only a partial isometry. -/
def finiteProjectionRangeCycleIsoOfWitness
    (p q : BC4lean.OperatorKTheory.FiniteProjection B) (v : Matrix p.Index q.Index B)
    (hp : v * vᴴ = BC4lean.OperatorKTheory.projectionMatrix p.projection)
    (hq : vᴴ * v = BC4lean.OperatorKTheory.projectionMatrix q.projection) :
    KasparovCycleIso (finiteProjectionRangeCycle (Γ := Γ) p) (finiteProjectionRangeCycle (Γ := Γ) q) :=
  compactIdentityScalarCycleIso _ _ _ _ (finiteProjectionRangeEquiv p.projection q.projection v hp hq)

/-- The exact equivalence relation defining the stable projection monoid respects
the concrete projection cycles, including projections with different finite index types. -/
theorem finiteProjection_equivalent_rangeCycleIso
    (p q : BC4lean.OperatorKTheory.FiniteProjection B)
    (h : BC4lean.OperatorKTheory.FiniteProjection.Equivalent p q) :
    Nonempty (KasparovCycleIso (finiteProjectionRangeCycle (Γ := Γ) p)
      (finiteProjectionRangeCycle (Γ := Γ) q)) := by
  obtain ⟨v, hp, hq⟩ := h
  exact ⟨finiteProjectionRangeCycleIsoOfWitness p q v hp hq⟩

/-- The empty projection gives an actual degenerate cycle on its zero range. -/
theorem finiteProjectionRangeCycle_zero_isDegenerate :
    (finiteProjectionRangeCycle (Γ := Γ) (B := B) BC4lean.OperatorKTheory.FiniteProjection.zero).IsDegenerate := by
  constructor
  · intro a
    apply AdjointableMap.ext
    intro x
    apply Subtype.ext
    apply WithCStarModule.ext
    intro i
    exact Empty.elim i
  constructor
  · intro a
    apply AdjointableMap.ext
    intro x
    apply Subtype.ext
    apply WithCStarModule.ext
    intro i
    exact Empty.elim i
  constructor
  · intro a
    apply AdjointableMap.ext
    intro x
    apply Subtype.ext
    apply WithCStarModule.ext
    intro i
    exact Empty.elim i
  · intro g a
    apply AdjointableMap.ext
    intro x
    apply Subtype.ext
    apply WithCStarModule.ext
    intro i
    exact Empty.elim i

end FiniteProjectionCycle
end BC4lean.KKTheory
