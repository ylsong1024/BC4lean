import BC4lean.IntervalModuleFibreNorm
import BC4lean.CStarHomClosedRange
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit

/-! # Compact operators and the genuine fibre kernel

Fibre evaluation on compact endomorphisms is an actual surjective complex
nonunital C⋆-homomorphism. Rank-one operators lift using the proved
surjectivity of the canonical module-fibre map, and the actual C⋆-homomorphism
has closed range.

Its kernel is the operator-norm closure of the rank-one span whose first
vector vanishes in the fibre. The proof uses the genuine approximate unit
of the existing closed C⋆-subalgebra of compact module operators. In
particular it does not restrict compact operators to arbitrary reducing
submodules.
-/

noncomputable section
namespace BC4lean.KKTheory

open Filter
open scoped Topology InnerProductSpace

variable {B X M : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [StarOrderedRing B] [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M]
  [CompleteSpace M]

/-- The compact-operator C⋆-algebra maps into the adjointable algebra of
the actual fibre by the previously constructed operator homomorphism. -/
def hilbertModuleCompactFibreOperatorHom (t : X) :
    CompactModuleOperator C(X, B) M →⋆ₙₐ[ℂ]
      AdjointableMap B (HilbertModuleFibre B M t) (HilbertModuleFibre B M t) :=
  (hilbertModuleFibreOperatorHom (B := B) (M := M) t).toNonUnitalStarAlgHom.comp
    (NonUnitalStarSubalgebraClass.subtype
      (compactModuleOperatorAlgebra (B := C(X, B)) (E := M)))

omit [T2Space X] in
@[simp] theorem hilbertModuleCompactFibreOperatorHom_apply (t : X)
    (T : CompactModuleOperator C(X, B) M) :
    hilbertModuleCompactFibreOperatorHom (B := B) t T =
      hilbertModuleFibreOperator (B := B) t (T : AdjointableMap C(X, B) M M) := rfl

/-- Evaluation is a genuine homomorphism between the existing compact
operator C⋆-algebras. Its codomain restriction is justified by compactness
preservation, already proved from norm closure and evaluated rank ones. -/
def hilbertModuleCompactFibreHom (t : X) :
    CompactModuleOperator C(X, B) M →⋆ₙₐ[ℂ]
      CompactModuleOperator B (HilbertModuleFibre B M t) :=
  NonUnitalStarAlgHom.codRestrict (hilbertModuleCompactFibreOperatorHom (B := B) t)
    (compactModuleOperatorAlgebra (B := B) (E := HilbertModuleFibre B M t))
    (fun T => IsModuleCompact.fibre T.property t)

omit [T2Space X] in
@[simp] theorem hilbertModuleCompactFibreHom_coe (t : X)
    (T : CompactModuleOperator C(X, B) M) :
    (hilbertModuleCompactFibreHom (B := B) t T :
        AdjointableMap B (HilbertModuleFibre B M t) (HilbertModuleFibre B M t)) =
      hilbertModuleFibreOperator (B := B) t (T : AdjointableMap C(X, B) M M) := rfl

/-- Every actual compact fibre operator lifts. Surjectivity is derived
from lifted rank ones and closed C⋆-homomorphism range. -/
theorem hilbertModuleCompactFibreHom_surjective (t : X) :
    Function.Surjective (hilbertModuleCompactFibreHom (B := B) (M := M) t) := by
  let φ := hilbertModuleCompactFibreOperatorHom (B := B) (M := M) t
  let R : Submodule ℂ
      (AdjointableMap B (HilbertModuleFibre B M t) (HilbertModuleFibre B M t)) :=
    (nonUnitalCStarHomCLM φ).range
  have hR : IsClosed (R : Set
      (AdjointableMap B (HilbertModuleFibre B M t) (HilbertModuleFibre B M t))) :=
    nonUnitalCStarHom_isClosed_range φ
  have hθ (ξ η : HilbertModuleFibre B M t) : moduleRankOne (B := B) ξ η ∈ R := by
    obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := M) t ξ
    obtain ⟨y, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := M) t η
    refine ⟨⟨moduleRankOne (B := C(X, B)) x y,
      moduleRankOne_mem_moduleCompact x y⟩, ?_⟩
    exact hilbertModuleFibreOperator_rankOne t x y
  intro T
  obtain ⟨S, hS⟩ := (moduleCompact_le_of_isClosed R hR hθ) T.property
  refine ⟨S, ?_⟩
  apply Subtype.ext
  exact hS

/-- A compact fibre operator has an actual lift attaining its norm. The
bound follows from the general proved CFC lifting theorem. -/
theorem exists_compactFibre_lift_norm_eq (t : X)
    (T : CompactModuleOperator B (HilbertModuleFibre B M t)) :
    ∃ S : CompactModuleOperator C(X, B) M,
      hilbertModuleCompactFibreHom (B := B) t S = T ∧ ‖S‖ = ‖T‖ :=
  nonUnitalCStarHom_exists_norm_eq_lift_of_surjective
    (hilbertModuleCompactFibreHom (B := B) (M := M) t)
    (hilbertModuleCompactFibreHom_surjective (B := B) (M := M) t) T

/-- Rank-one maps with first vector in the actual endpoint-null module. -/
def fibreNullFiniteRank (t : X) : Submodule ℂ (AdjointableMap C(X, B) M M) :=
  Submodule.span ℂ {T | ∃ x y : M,
    hilbertModuleFibreMk (B := B) t x = 0 ∧
      T = moduleRankOne (B := C(X, B)) x y}

/-- The genuine norm closure of the endpoint-null rank-one span. -/
def fibreNullCompact (t : X) : Submodule ℂ (AdjointableMap C(X, B) M M) :=
  (fibreNullFiniteRank (B := B) (M := M) t).topologicalClosure

omit [T2Space X] in
theorem fibreNullCompact_isClosed (t : X) :
    IsClosed (fibreNullCompact (B := B) (M := M) t :
      Set (AdjointableMap C(X, B) M M)) :=
  Submodule.isClosed_topologicalClosure _

omit [T2Space X] in
theorem moduleRankOne_mem_fibreNullCompact (t : X) (x y : M)
    (hx : hilbertModuleFibreMk (B := B) t x = 0) :
    moduleRankOne (B := C(X, B)) x y ∈ fibreNullCompact (B := B) t :=
  Submodule.le_topologicalClosure _
    (Submodule.subset_span ⟨x, y, hx, rfl⟩)

omit [T2Space X] in
/-- The endpoint-null rank-one closure consists of compact maps that
evaluate to zero. This inclusion uses the actual continuous fibre map. -/
theorem fibreNullCompact_le_compact_fibreKernel (t : X) :
    fibreNullCompact (B := B) (M := M) t ≤
      (moduleCompact C(X, B) M M) ⊓
        (hilbertModuleFibreOperatorCLM (B := B) (M := M) t).ker := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro T ⟨x, y, hx, rfl⟩
    refine ⟨moduleRankOne_mem_moduleCompact x y, ?_⟩
    change hilbertModuleFibreOperator (B := B) t
      (moduleRankOne (B := C(X, B)) x y) = 0
    rw [hilbertModuleFibreOperator_rankOne, hx]
    ext z
    change ⟪hilbertModuleFibreMk (B := B) t y, z⟫_(Bᵐᵒᵖ) •
      (0 : HilbertModuleFibre B M t) = 0
    apply module_inner_ext_left (B := B)
    intro w
    rw [CStarModule.inner_op_smul_left, CStarModule.inner_zero_left, zero_mul]
  · exact (moduleCompact_isClosed (B := C(X, B)) (E := M) (F := M)).inter
      (hilbertModuleFibreOperatorCLM (B := B) (M := M) t).isClosed_ker

omit [T2Space X] in
/-- If a compact operator evaluates to zero, left multiplication by it
sends every compact map into the endpoint-null rank-one closure. -/
theorem comp_mem_fibreNullCompact_of_fibre_eq_zero (t : X)
    (T : AdjointableMap C(X, B) M M)
    (hT : hilbertModuleFibreOperator (B := B) t T = 0)
    {S : AdjointableMap C(X, B) M M} (hS : IsModuleCompact S) :
    T.comp S ∈ fibreNullCompact (B := B) t := by
  let N := fibreNullCompact (B := B) (M := M) t
  let R : Submodule ℂ (AdjointableMap C(X, B) M M) :=
    N.comap (AdjointableMap.compLeftContinuousLinearMap T).toLinearMap
  have hR : IsClosed (R : Set (AdjointableMap C(X, B) M M)) :=
    (fibreNullCompact_isClosed (B := B) (M := M) t).preimage
      (AdjointableMap.compLeftContinuousLinearMap T).continuous
  have hθ (x y : M) : moduleRankOne (B := C(X, B)) x y ∈ R := by
    change T.comp (moduleRankOne (B := C(X, B)) x y) ∈ N
    rw [comp_moduleRankOne]
    apply moduleRankOne_mem_fibreNullCompact
    rw [← hilbertModuleFibreOperator_mk, hT, AdjointableMap.coe_zero_apply]
  exact (moduleCompact_le_of_isClosed R hR hθ) hS

omit [T2Space X] in
/-- The compact kernel is exactly the endpoint-null rank-one closure.
The nontrivial inclusion is obtained by multiplying the genuine compact
operator approximate unit, then taking its actual norm limit. -/
theorem compact_fibreKernel_eq_fibreNullCompact (t : X) :
    (moduleCompact C(X, B) M M) ⊓
        (hilbertModuleFibreOperatorCLM (B := B) (M := M) t).ker =
      fibreNullCompact (B := B) (M := M) t := by
  apply le_antisymm
  · intro T hT
    let K := CompactModuleOperator C(X, B) M
    let : PartialOrder K := CStarAlgebra.spectralOrder K
    let : StarOrderedRing K := CStarAlgebra.spectralOrderedRing K
    let k : K := ⟨T, hT.1⟩
    have hzero : hilbertModuleFibreOperator (B := B) t T = 0 := hT.2
    have hlim : Tendsto (fun e : K => ((k * e : K) : AdjointableMap C(X, B) M M))
        (CStarAlgebra.approximateUnit K) (𝓝 T) :=
      continuous_subtype_val.continuousAt.tendsto.comp
        ((CStarAlgebra.increasingApproximateUnit K).tendsto_mul_left k)
    apply (fibreNullCompact_isClosed (B := B) (M := M) t).mem_of_tendsto hlim
    exact Eventually.of_forall (fun e =>
      comp_mem_fibreNullCompact_of_fibre_eq_zero t T hzero e.property)
  · exact fibreNullCompact_le_compact_fibreKernel t

omit [T2Space X] in
/-- Membership form of the exact compact-kernel identification, suitable
for lifting the two endpoint-null summands in compact pullback gluing. -/
theorem mem_fibreNullCompact_iff (t : X)
    (T : AdjointableMap C(X, B) M M) :
    T ∈ fibreNullCompact (B := B) t ↔
      IsModuleCompact T ∧ hilbertModuleFibreOperator (B := B) t T = 0 := by
  rw [← compact_fibreKernel_eq_fibreNullCompact]
  rfl

end BC4lean.KKTheory
