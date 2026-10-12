import BC4lean.ScalarKasparovK0IndexRightInverse
import BC4lean.GroupShrinkEvenBridge

/-! # Genuine module-universe compatibility of the scalar K₀ index

Actual countable generation and coefficient separability give the small
Hilbert-module model. Its whole raw cycle unitary preserves the Julia index.
The true full-homotopy universe equivalence therefore commutes with the index,
and transports the constructed forward map and its right inverse to any
chosen module universe.
-/

noncomputable section
universe uB uE v
namespace BC4lean.KKTheory
open BC4lean.OperatorKTheory

variable {B : Type uB} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]
local notation "α₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit ℂ)
local notation "β₁" => (CStarAlgebraAction.trivial : CStarAlgebraAction PUnit B)

theorem scalarKKOperatorK0Index_universe
    (z : KasparovHomotopyClass.{0, 0, uB, uE} α₁ β₁) :
    scalarKKOperatorK0Index
      (GroupShrinkEvenBridge.addEquivalence.{0, 0, uB, uE, v} z) = scalarKKOperatorK0Index z := by
  obtain ⟨c, rfl⟩ := KasparovHomotopyClass.mk_surjective z
  rw [GroupShrinkEvenBridge.addEquivalence_mk, scalarKKOperatorK0Index_mk,
    scalarKKOperatorK0Index_mk]
  exact (scalarKasparovOperatorK0Index_iso c.shrinkIso).symm

def nonunitalRelativeK0KasparovMapAtUniverse :
    OperatorK0 B →+ KasparovHomotopyClass.{0, 0, uB, uE} α₁ β₁ :=
  (GroupShrinkEvenBridge.addEquivalence.{0, 0, uB, uB, uE}).toAddMonoidHom.comp
    (nonunitalRelativeK0KasparovMap (B := B))

theorem nonunitalRelativeK0KasparovMapAtUniverse_rightInverse :
    Function.RightInverse (scalarKKOperatorK0Index (B := B))
      (nonunitalRelativeK0KasparovMapAtUniverse.{uB, uE} (B := B)) := by
  intro z
  let e := GroupShrinkEvenBridge.addEquivalence.{0, 0, uB, uB, uE}
    (α := α₁) (β := β₁)
  have hi : scalarKKOperatorK0Index (e.symm z) = scalarKKOperatorK0Index z := by
    have h := scalarKKOperatorK0Index_universe.{uB, uB, uE} (e.symm z)
    simpa only [e, AddEquiv.apply_symm_apply] using h.symm
  change e (nonunitalRelativeK0KasparovMap (scalarKKOperatorK0Index z)) = z
  rw [← hi]
  rw [nonunitalRelativeK0KasparovMap_scalarKKOperatorK0Index_rightInverse (e.symm z)]
  exact e.apply_symm_apply z

theorem scalarKKOperatorK0Index_injective :
    Function.Injective (scalarKKOperatorK0Index (B := B) :
      KasparovHomotopyClass.{0, 0, uB, uE} α₁ β₁ → OperatorK0 B) := by
  intro x y h
  have hx := nonunitalRelativeK0KasparovMapAtUniverse_rightInverse (B := B) x
  have hy := nonunitalRelativeK0KasparovMapAtUniverse_rightInverse (B := B) y
  calc
    x = nonunitalRelativeK0KasparovMapAtUniverse (scalarKKOperatorK0Index x) := hx.symm
    _ = nonunitalRelativeK0KasparovMapAtUniverse (scalarKKOperatorK0Index y) := congrArg _ h
    _ = y := hy

end BC4lean.KKTheory
