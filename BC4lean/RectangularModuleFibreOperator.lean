import BC4lean.HilbertModuleFibreSum
import BC4lean.IntervalModuleFibreNorm

/-! # Actual rectangular maps on evaluated Hilbert-module fibres

A rectangular map is placed in a genuine off-diagonal sum-module block,
evaluated by the actual endomorphism fibre map, and extracted by the actual
fibre coordinate maps. This constructs its fibre map without assuming a
multiplier extension. Both adjoints and genuine rectangular compactness
descend through the proved block formula.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B X M N P : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, B)ᵐᵒᵖ M]
  [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]
  [NormedAddCommGroup N] [NormedSpace ℂ N] [SMul C(X, B)ᵐᵒᵖ N]
  [CStarModule C(X, B)ᵐᵒᵖ N] [CompleteSpace N]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [SMul C(X, B)ᵐᵒᵖ P]
  [CStarModule C(X, B)ᵐᵒᵖ P] [CompleteSpace P]

/-- The actual off-diagonal endomorphism on the sum module. -/
def rectangularModuleFibreBlock (T : AdjointableMap C(X, B) M N) :
    AdjointableMap C(X, B) (HilbertModuleSum C(X, B) M N) (HilbertModuleSum C(X, B) M N) :=
  ((sumInr (B := C(X, B)) (E := M)).comp T).comp sumFst

omit [T2Space X] [CompleteSpace M] [CompleteSpace N] in
@[simp] theorem rectangularModuleFibreBlock_apply (T : AdjointableMap C(X, B) M N)
    (z : HilbertModuleSum C(X, B) M N) :
    rectangularModuleFibreBlock T z = sumMk 0 (T z.fst) := rfl

/-- The genuine rectangular fibre map constructed from actual sum blocks. -/
def hilbertModuleFibreRectangularMap (t : X) (T : AdjointableMap C(X, B) M N) :
    AdjointableMap B (HilbertModuleFibre B M t) (HilbertModuleFibre B N t) :=
  ((hilbertModuleFibreSnd (B := B) (M := M) (N := N) t).comp
    (hilbertModuleFibreOperator t (rectangularModuleFibreBlock T))).comp
      (hilbertModuleFibreInl (B := B) (M := M) (N := N) t)

omit [T2Space X] in
@[simp] theorem hilbertModuleFibreRectangularMap_mk (t : X)
    (T : AdjointableMap C(X, B) M N) (x : M) :
    hilbertModuleFibreRectangularMap t T (hilbertModuleFibreMk (B := B) t x) =
      hilbertModuleFibreMk (B := B) t (T x) := by
  simp only [hilbertModuleFibreRectangularMap, AdjointableMap.comp_apply,
    hilbertModuleFibreInl_mk, hilbertModuleFibreOperator_mk, rectangularModuleFibreBlock_apply,
    sumMk_fst, hilbertModuleFibreSnd_mk, sumMk_snd]

/-- The constructed map has exactly the genuine descended adjoint. -/
@[simp] theorem hilbertModuleFibreRectangularMap_adjoint (t : X)
    (T : AdjointableMap C(X, B) M N) :
    (hilbertModuleFibreRectangularMap t T).adjoint = hilbertModuleFibreRectangularMap t T.adjoint := by
  ext z
  obtain ⟨y, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := N) t z
  rw [hilbertModuleFibreRectangularMap_mk]
  change ((hilbertModuleFibreInl t).adjoint.comp
    ((hilbertModuleFibreOperator t (rectangularModuleFibreBlock T)).adjoint.comp
      (hilbertModuleFibreSnd t).adjoint)) (hilbertModuleFibreMk (B := B) t y) = _
  rw [show (hilbertModuleFibreSnd (B := B) (M := M) (N := N) t).adjoint =
    hilbertModuleFibreInr t from AdjointableMap.adjoint_adjoint _]
  change (hilbertModuleFibreFst t).comp
    ((star (hilbertModuleFibreOperator t (rectangularModuleFibreBlock T))).comp
      (hilbertModuleFibreInr t)) (hilbertModuleFibreMk (B := B) t y) = _
  rw [← hilbertModuleFibreOperator_star]
  simp only [AdjointableMap.comp_apply, hilbertModuleFibreInr_mk, hilbertModuleFibreOperator_mk,
    rectangularModuleFibreBlock, AdjointableMap.star_eq_adjoint, AdjointableMap.adjoint_comp,
    sumInr_adjoint, sumFst_adjoint, sumInl_apply, sumSnd_apply, sumMk_snd,
    hilbertModuleFibreFst_mk, sumMk_fst]

@[simp] theorem hilbertModuleFibreRectangularMap_add (t : X)
    (S T : AdjointableMap C(X, B) M N) :
    hilbertModuleFibreRectangularMap t (S + T) =
      hilbertModuleFibreRectangularMap t S + hilbertModuleFibreRectangularMap t T := by
  ext z
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := M) t z
  simp only [hilbertModuleFibreRectangularMap_mk, AdjointableMap.coe_add_apply, map_add]

@[simp] theorem hilbertModuleFibreRectangularMap_sub (t : X)
    (S T : AdjointableMap C(X, B) M N) :
    hilbertModuleFibreRectangularMap t (S - T) =
      hilbertModuleFibreRectangularMap t S - hilbertModuleFibreRectangularMap t T := by
  ext z
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := M) t z
  simp only [hilbertModuleFibreRectangularMap_mk, AdjointableMap.coe_sub_apply, map_sub]

@[simp] theorem hilbertModuleFibreRectangularMap_comp (t : X)
    (S : AdjointableMap C(X, B) N P) (T : AdjointableMap C(X, B) M N) :
    hilbertModuleFibreRectangularMap t (S.comp T) =
      (hilbertModuleFibreRectangularMap t S).comp (hilbertModuleFibreRectangularMap t T) := by
  ext z
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := M) t z
  simp only [hilbertModuleFibreRectangularMap_mk, AdjointableMap.comp_apply]

/-- On an actual endomorphism the rectangular construction agrees with
the already constructed endomorphism fibre homomorphism. -/
@[simp] theorem hilbertModuleFibreRectangularMap_eq_operator (t : X)
    (T : AdjointableMap C(X, B) M M) :
    hilbertModuleFibreRectangularMap t T = hilbertModuleFibreOperator t T := by
  ext z
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := M) t z
  rw [hilbertModuleFibreRectangularMap_mk, hilbertModuleFibreOperator_mk]

omit [T2Space X] in
/-- Fibre evaluation preserves true rectangular module compactness:
the block is compact before evaluation, then both actual coordinate maps
preserve that compact map by the genuine rectangular ideal laws. -/
theorem IsModuleCompact.rectangular_fibre {T : AdjointableMap C(X, B) M N}
    (hT : IsModuleCompact T) (t : X) : IsModuleCompact (hilbertModuleFibreRectangularMap t T) := by
  have hblock : IsModuleCompact (rectangularModuleFibreBlock T) :=
    (hT.comp_left sumInr).comp_right sumFst
  exact ((hblock.fibre t).comp_left (hilbertModuleFibreSnd t)).comp_right (hilbertModuleFibreInl t)

@[simp] theorem hilbertModuleFibreRectangularMap_rankOne (t : X) (x : N) (y : M) :
    hilbertModuleFibreRectangularMap t (moduleRankOne (B := C(X, B)) x y) =
      moduleRankOne (B := B) (hilbertModuleFibreMk (B := B) t x) (hilbertModuleFibreMk (B := B) t y) := by
  ext z
  obtain ⟨w, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := M) t z
  simp only [hilbertModuleFibreRectangularMap_mk, moduleRankOne_apply,
    hilbertModuleFibreMk_op_smul, hilbertModuleFibre_inner_mk]

end BC4lean.KKTheory
