import BC4lean.CliffordIntervalRangeFibre
import BC4lean.IntervalModuleFibreNorm

/-! # Clifford expansion commutes with arbitrary evaluated fibres

The map from the expanded arbitrary interval module to a pair of its genuine
odd fibres evaluates the two original vectors. Its inner-product formula and
surjectivity identify the completed fibre by an actual module unitary. That
same unitary intertwines the semilinear grading and all cycle data.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B X M : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

/-- The actual expanded interval carrier, with transported Clifford coefficients. -/
abbrev CliffordExpandedIntervalModule (B M : Type*) [NonUnitalCStarAlgebra B]
    {X : Type*} [TopologicalSpace X] [CompactSpace X] :=
  CoefficientChangedModule (continuousProductCoefficientEquiv (B := B) (X := X)).symm
    (CliffordPairModule C(X, B) M)

/-- Evaluate the two actual vectors in the expanded interval module. -/
def cliffordIntervalPairEvaluation (t : X) :
    CliffordExpandedIntervalModule (X := X) B M →L[ℂ]
      CliffordPairModule B (HilbertModuleFibre B M t) :=
  ({ toFun x := cliffordPairMk (hilbertModuleFibreMk (B := B) t x.1)
        (hilbertModuleFibreMk (B := B) t x.2)
     map_add' x y := by apply Prod.ext <;> exact map_add _ _ _
     map_smul' c x := by apply Prod.ext <;> exact map_smul _ _ _ } :
    CliffordExpandedIntervalModule (X := X) B M →ₗ[ℂ]
      CliffordPairModule B (HilbertModuleFibre B M t)).mkContinuous 1 (fun x => by
        change max ‖hilbertModuleFibreMk (B := B) t x.1‖
          ‖hilbertModuleFibreMk (B := B) t x.2‖ ≤ 1 * max ‖x.1‖ ‖x.2‖
        rw [one_mul]
        exact max_le_max (hilbertModuleFibreMk_norm_le t x.1) (hilbertModuleFibreMk_norm_le t x.2))

omit [T2Space X] [CompleteSpace M] in
@[simp] theorem cliffordIntervalPairEvaluation_apply (t : X)
    (x : CliffordExpandedIntervalModule (X := X) B M) :
    cliffordIntervalPairEvaluation t x =
      cliffordPairMk (hilbertModuleFibreMk (B := B) t x.1)
        (hilbertModuleFibreMk (B := B) t x.2) := rfl

omit [T2Space X] [CompleteSpace M] in
theorem cliffordIntervalPairEvaluation_inner (t : X)
    (x y : CliffordExpandedIntervalModule (X := X) B M) :
    ⟪cliffordIntervalPairEvaluation t x, cliffordIntervalPairEvaluation t y⟫_((B × B)ᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪x, y⟫_(C(X, B × B)ᵐᵒᵖ) t) := by
  apply MulOpposite.unop_injective
  apply Prod.ext
  · exact congrArg MulOpposite.unop (hilbertModuleFibre_inner_mk (B := B) t x.1 y.1)
  · exact congrArg MulOpposite.unop (hilbertModuleFibre_inner_mk (B := B) t x.2 y.2)

theorem cliffordIntervalPairEvaluation_surjective (t : X) :
    Function.Surjective (cliffordIntervalPairEvaluation (B := B) (M := M) t) := by
  intro y
  obtain ⟨x₁, hx₁⟩ := hilbertModuleFibreMk_surjective (B := B) (M := M) t y.1
  obtain ⟨x₂, hx₂⟩ := hilbertModuleFibreMk_surjective (B := B) (M := M) t y.2
  refine ⟨cliffordPairMk x₁ x₂, ?_⟩
  apply Prod.ext
  · exact hx₁
  · exact hx₂

/-- The completed Clifford fibre is the genuine product-coefficient pair
of the completed odd fibre. -/
def cliffordIntervalPairFibreEquiv (t : X) :
    HilbertModuleEquiv (B × B)
      (HilbertModuleFibre (B × B) (CliffordExpandedIntervalModule (X := X) B M) t)
      (CliffordPairModule B (HilbertModuleFibre B M t)) :=
  hilbertModuleFibreEquivOfEvaluation t (cliffordIntervalPairEvaluation t)
    (cliffordIntervalPairEvaluation_inner t) (cliffordIntervalPairEvaluation_surjective t)

@[simp] theorem cliffordIntervalPairFibreEquiv_mk (t : X)
    (x : CliffordExpandedIntervalModule (X := X) B M) :
    cliffordIntervalPairFibreEquiv t (hilbertModuleFibreMk (B := B × B) t x) =
      cliffordIntervalPairEvaluation t x :=
  hilbertModuleFibreEquivOfEvaluation_mk t _ _ _ x

section WholeCycle
variable {Γ A : Type*} [Group Γ] [NonUnitalCStarAlgebra A]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

private theorem cliffordIntervalExpansionFibre_grading_intertwine
    (c : OddKasparovCycle α (β.continuousSections (X := X)) M) (t : X)
    (z : HilbertModuleFibre (B × B) (CliffordExpandedIntervalModule (X := X) B M) t) :
    cliffordIntervalPairFibreEquiv (B := B) (X := X) (M := M) t ((c.cliffordIntervalExpansion.fibre t).grading.grading z) =
      (c.fibre t).cliffordExpansion.grading.grading (cliffordIntervalPairFibreEquiv (B := B) (X := X) (M := M) t z) := by
  let u : HilbertModuleEquiv (B × B)
      (HilbertModuleFibre (B × B) (CliffordExpandedIntervalModule (X := X) B M) t)
      (CliffordPairModule B (HilbertModuleFibre B M t)) :=
    cliffordIntervalPairFibreEquiv (B := B) (X := X) (M := M) t
  have hu (x : CliffordExpandedIntervalModule (X := X) B M) :
      u (hilbertModuleFibreMk (B := B × B) t x) = cliffordIntervalPairEvaluation t x :=
    cliffordIntervalPairFibreEquiv_mk (B := B) (X := X) (M := M) t x
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B × B)
    (M := CliffordExpandedIntervalModule (X := X) B M) t z
  calc
    u ((c.cliffordIntervalExpansion.fibre t).grading.grading
        (hilbertModuleFibreMk (B := B × B) t x)) =
      u (hilbertModuleFibreMk (B := B × B) t
        (c.cliffordIntervalExpansion.grading.grading x)) :=
      congrArg (fun y => u y) (c.cliffordIntervalExpansion.fibre_grading_mk t x)
    _ = cliffordIntervalPairEvaluation t
        (c.cliffordIntervalExpansion.grading.grading x) := hu _
    _ = (c.fibre t).cliffordExpansion.grading.grading
        (cliffordIntervalPairEvaluation t x) := rfl
    _ = (c.fibre t).cliffordExpansion.grading.grading
        (u (hilbertModuleFibreMk (B := B × B) t x)) :=
      congrArg (fun y => (c.fibre t).cliffordExpansion.grading.grading y) (hu x).symm

private theorem cliffordIntervalExpansionFibre_action_intertwine
    (c : OddKasparovCycle α (β.continuousSections (X := X)) M) (t : X) (g : Γ)
    (z : HilbertModuleFibre (B × B) (CliffordExpandedIntervalModule (X := X) B M) t) :
    cliffordIntervalPairFibreEquiv (B := B) (X := X) (M := M) t ((c.cliffordIntervalExpansion.fibre t).groupAction.action g z) =
      (c.fibre t).cliffordExpansion.groupAction.action g (cliffordIntervalPairFibreEquiv (B := B) (X := X) (M := M) t z) := by
  let u : HilbertModuleEquiv (B × B)
      (HilbertModuleFibre (B × B) (CliffordExpandedIntervalModule (X := X) B M) t)
      (CliffordPairModule B (HilbertModuleFibre B M t)) :=
    cliffordIntervalPairFibreEquiv (B := B) (X := X) (M := M) t
  have hu (x : CliffordExpandedIntervalModule (X := X) B M) :
      u (hilbertModuleFibreMk (B := B × B) t x) = cliffordIntervalPairEvaluation t x :=
    cliffordIntervalPairFibreEquiv_mk (B := B) (X := X) (M := M) t x
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B × B)
    (M := CliffordExpandedIntervalModule (X := X) B M) t z
  calc
    u ((c.cliffordIntervalExpansion.fibre t).groupAction.action g
        (hilbertModuleFibreMk (B := B × B) t x)) =
      u (hilbertModuleFibreMk (B := B × B) t
        (c.cliffordIntervalExpansion.groupAction.action g x)) :=
      congrArg (fun y => u y) (c.cliffordIntervalExpansion.fibre_action_mk t g x)
    _ = cliffordIntervalPairEvaluation t
        (c.cliffordIntervalExpansion.groupAction.action g x) := hu _
    _ = (c.fibre t).cliffordExpansion.groupAction.action g
        (cliffordIntervalPairEvaluation t x) := by
      apply Prod.ext <;> exact (c.fibre_action_mk t g _).symm
    _ = (c.fibre t).cliffordExpansion.groupAction.action g
        (u (hilbertModuleFibreMk (B := B × B) t x)) :=
      congrArg (fun y => (c.fibre t).cliffordExpansion.groupAction.action g y) (hu x).symm

-- The direct native fibre proof still exhausts the default 200000 heartbeats
-- when substituting a genuine fibre representative. Keep this budget local.
set_option maxHeartbeats 800000 in
private theorem cliffordIntervalExpansionFibre_representation_intertwine
    (c : OddKasparovCycle α (β.continuousSections (X := X)) M) (t : X) (a : A)
    (z : HilbertModuleFibre (B × B) (CliffordExpandedIntervalModule (X := X) B M) t) :
    cliffordIntervalPairFibreEquiv (B := B) (X := X) (M := M) t ((c.cliffordIntervalExpansion.fibre t).representation a z) =
      (c.fibre t).cliffordExpansion.representation a (cliffordIntervalPairFibreEquiv (B := B) (X := X) (M := M) t z) := by
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B × B)
    (M := CliffordExpandedIntervalModule (X := X) B M) t z
  rw [GradedKasparovCycle.fibre_representation_mk,
    cliffordIntervalPairFibreEquiv_mk, cliffordIntervalPairFibreEquiv_mk]
  change cliffordPairMk
      (hilbertModuleFibreMk (B := B) t (c.representation a x.1))
      (hilbertModuleFibreMk (B := B) t (c.representation a x.2)) =
    cliffordPairMk
      ((c.fibre t).representation a (hilbertModuleFibreMk (B := B) t x.1))
      ((c.fibre t).representation a (hilbertModuleFibreMk (B := B) t x.2))
  apply Prod.ext
  · exact (c.fibre_representation_mk t a x.1).symm
  · exact (c.fibre_representation_mk t a x.2).symm

private theorem cliffordIntervalExpansionFibre_operator_intertwine
    (c : OddKasparovCycle α (β.continuousSections (X := X)) M) (t : X)
    (z : HilbertModuleFibre (B × B) (CliffordExpandedIntervalModule (X := X) B M) t) :
    cliffordIntervalPairFibreEquiv (B := B) (X := X) (M := M) t ((c.cliffordIntervalExpansion.fibre t).operator z) =
      (c.fibre t).cliffordExpansion.operator (cliffordIntervalPairFibreEquiv (B := B) (X := X) (M := M) t z) := by
  let u : HilbertModuleEquiv (B × B)
      (HilbertModuleFibre (B × B) (CliffordExpandedIntervalModule (X := X) B M) t)
      (CliffordPairModule B (HilbertModuleFibre B M t)) :=
    cliffordIntervalPairFibreEquiv (B := B) (X := X) (M := M) t
  have hu (x : CliffordExpandedIntervalModule (X := X) B M) :
      u (hilbertModuleFibreMk (B := B × B) t x) = cliffordIntervalPairEvaluation t x :=
    cliffordIntervalPairFibreEquiv_mk (B := B) (X := X) (M := M) t x
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B × B)
    (M := CliffordExpandedIntervalModule (X := X) B M) t z
  calc
    u ((c.cliffordIntervalExpansion.fibre t).operator
        (hilbertModuleFibreMk (B := B × B) t x)) =
      u (hilbertModuleFibreMk (B := B × B) t (c.cliffordIntervalExpansion.operator x)) :=
      congrArg (fun y => u y) (c.cliffordIntervalExpansion.fibre_operator_mk t x)
    _ = cliffordIntervalPairEvaluation t (c.cliffordIntervalExpansion.operator x) := hu _
    _ = (c.fibre t).cliffordExpansion.operator (cliffordIntervalPairEvaluation t x) := by
      apply Prod.ext
      · exact (c.fibre_operator_mk t x.1).symm
      · change hilbertModuleFibreMk (B := B) t ((-c.operator) x.2) =
          (-((c.fibre t).operator)) (hilbertModuleFibreMk (B := B) t x.2)
        rw [AdjointableMap.coe_neg_apply, AdjointableMap.coe_neg_apply,
          map_neg, c.fibre_operator_mk]
    _ = (c.fibre t).cliffordExpansion.operator
        (u (hilbertModuleFibreMk (B := B × B) t x)) :=
      congrArg (fun y => (c.fibre t).cliffordExpansion.operator y) (hu x).symm

/-- The actual expansion fibre unitary intertwines the whole Clifford cycle. -/
def OddKasparovCycle.cliffordIntervalExpansionFibreIso
    (c : OddKasparovCycle α (β.continuousSections (X := X)) M) (t : X) :
    GradedKasparovCycleIso (c.cliffordIntervalExpansion.fibre t) (c.fibre t).cliffordExpansion := by
  exact
    { moduleEquiv := cliffordIntervalPairFibreEquiv (B := B) (X := X) (M := M) t
      grading_intertwine := cliffordIntervalExpansionFibre_grading_intertwine c t
      action_intertwine := cliffordIntervalExpansionFibre_action_intertwine c t
      representation_intertwine := cliffordIntervalExpansionFibre_representation_intertwine c t
      operator_intertwine := cliffordIntervalExpansionFibre_operator_intertwine c t }

end WholeCycle
end BC4lean.KKTheory
