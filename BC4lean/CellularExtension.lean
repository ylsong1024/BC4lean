import BC4lean.OrbitCellExtension
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-!
# Extension over equivariant CW complexes

The single-cell extension property is preserved by coproducts, pushouts and
sequential colimits. Thus maps into a target with contractible finite-subgroup
fixed points extend over a relative equivariant CW complex.
-/

namespace BC4lean.ProperActions

open CategoryTheory CategoryTheory.Limits

universe u

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
variable {X : Type u} [TopologicalSpace X] [MulAction Γ X] [ContinuousConstSMul Γ X]

/-- Each generating orbit cell lifts against the map from the target to a point. -/
theorem basicCell_hasLiftingProperty (h : FixedPointCriterion Γ X)
    (n : ℕ) (H : FiniteIsotropy Γ) :
    HasLiftingProperty (equivariantBasicCell n H) (terminal.from (topologicalAction Γ X)) := by
  constructor
  intro a b sq
  let : Finite H.val := H.property
  obtain ⟨F, hF⟩ := h.orbitCell_extends H.val n (EquivariantMap.ofActionHom a)
  refine ⟨⟨{ l := F.toActionHom, fac_left := ?_, fac_right := ?_ }⟩⟩
  · have hf := congrArg EquivariantMap.toActionHom hF
    exact hf.trans (EquivariantMap.actionHomEquiv.apply_symm_apply a)
  · exact terminalIsTerminal.hom_ext _ _

/-- The cellwise lifting property persists across the full relative CW structure. -/
theorem RelativeEquivariantCWComplex.hasLiftingProperty
    {A B : Action TopCat.{u} Γ} {i : A ⟶ B}
    (c : RelativeEquivariantCWComplex i) (h : FixedPointCriterion Γ X) :
    HasLiftingProperty i (terminal.from (topologicalAction Γ X)) := by
  let W := MorphismProperty.ofHoms (fun p : ℕ × FiniteIsotropy Γ =>
    equivariantBasicCell p.1 p.2)
  have hc : ∀ s : c.Cells, W (equivariantBasicCell s.j s.i) :=
    fun s => MorphismProperty.ofHoms.mk (s.j, s.i)
  have hr : W.rlp (terminal.from (topologicalAction Γ X)) := by
    intro A B f hf
    cases hf with
    | mk p => exact basicCell_hasLiftingProperty h p.1 p.2
  exact W.transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp ℕ i
    ⟨c.transfiniteCompositionOfShape' hc⟩ _ hr

/-- Maps into a target satisfying the fixed-point criterion extend over relative CW complexes. -/
theorem RelativeEquivariantCWComplex.extend
    {A B : Action TopCat.{u} Γ} {i : A ⟶ B}
    (c : RelativeEquivariantCWComplex i) (h : FixedPointCriterion Γ X)
    (f : A ⟶ topologicalAction Γ X) :
    ∃ F : B ⟶ topologicalAction Γ X, i ≫ F = f := by
  let := c.hasLiftingProperty h
  let sq : CommSq f i (terminal.from (topologicalAction Γ X)) (terminal.from B) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- Every equivariant CW complex admits a map into a target satisfying the fixed-point criterion. -/
theorem EquivariantCWComplex.nonempty_map
    {A : Action TopCat.{u} Γ} (c : EquivariantCWComplex A) (h : FixedPointCriterion Γ X) :
    Nonempty (A ⟶ topologicalAction Γ X) := by
  obtain ⟨F, _⟩ := c.extend h (initial.to _)
  exact ⟨F⟩

end BC4lean.ProperActions
