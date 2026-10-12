import BC4lean.CliffordTensorGrading

/-! # The positive order on the constructed Clifford C⋆ tensor

The order is pulled back through the proved coordinate star equivalence.
Finite sums of star squares transport in both directions, so this order is
a genuine star-ring order, with no positive cone postulated separately.
-/

noncomputable section
namespace BC4lean.KKTheory

private theorem starSquareClosure_map {D E : Type*}
    [NonUnitalCStarAlgebra D] [NonUnitalCStarAlgebra E]
    (e : D ≃⋆ₐ[ℂ] E) {p : D}
    (hp : p ∈ AddSubmonoid.closure (Set.range fun s : D => star s * s)) :
    e p ∈ AddSubmonoid.closure (Set.range fun s : E => star s * s) := by
  induction hp using AddSubmonoid.closure_induction with
  | mem p hp =>
    obtain ⟨s, rfl⟩ := hp
    apply AddSubmonoid.subset_closure
    exact ⟨e s, by simp only [map_mul, map_star]⟩
  | zero => simpa only [map_zero] using
      (AddSubmonoid.zero_mem (AddSubmonoid.closure (Set.range fun s : E => star s * s)))
  | add p q _ _ hp hq =>
    simpa only [map_add] using AddSubmonoid.add_mem _ hp hq

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

instance cliffordTensorPartialOrder : PartialOrder (CliffordTensor B) :=
  PartialOrder.lift cliffordTensorCoordinateStarAlgEquiv cliffordTensorCoordinateStarAlgEquiv.injective

instance cliffordTensorStarOrderedRing : StarOrderedRing (CliffordTensor B) where
  le_iff x y := by
    change cliffordTensorCoordinateStarAlgEquiv x ≤ cliffordTensorCoordinateStarAlgEquiv y ↔ _
    rw [StarOrderedRing.le_iff]
    constructor
    · rintro ⟨p, hp, hy⟩
      refine ⟨cliffordTensorCoordinateStarAlgEquiv.symm p,
        starSquareClosure_map cliffordTensorCoordinateStarAlgEquiv.symm hp, ?_⟩
      apply cliffordTensorCoordinateStarAlgEquiv.injective
      change cliffordTensorCoordinateStarAlgEquiv y =
        cliffordTensorCoordinateStarAlgEquiv
          (x + cliffordTensorCoordinateStarAlgEquiv.symm p)
      simpa only [map_add, StarAlgEquiv.apply_symm_apply] using hy
    · rintro ⟨p, hp, rfl⟩
      exact ⟨cliffordTensorCoordinateStarAlgEquiv p,
        starSquareClosure_map cliffordTensorCoordinateStarAlgEquiv hp, map_add _ _ _⟩

omit [StarOrderedRing B] in
@[simp] theorem cliffordTensorCoordinate_le_iff (x y : CliffordTensor B) :
    cliffordTensorCoordinateStarAlgEquiv x ≤ cliffordTensorCoordinateStarAlgEquiv y ↔ x ≤ y := Iff.rfl

end BC4lean.KKTheory
