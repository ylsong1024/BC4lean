import BC4lean.HilbertModuleEquiv
import BC4lean.CountablyGeneratedModule
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-! # The genuine range module of an adjointable projection

The fixed submodule of an adjointable map is closed and stable under the actual
right coefficient action. It inherits its coefficient-valued inner product and
norm from the ambient module. For a selfadjoint idempotent the ambient projection
corestricts to that module and is adjoint to its inclusion. A rectangular partial
isometry induces a unitary of these range modules; it is not treated as a unitary
of the ambient modules.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

/-- The fixed complex submodule, with its inherited ambient Hilbert norm. -/
def projectionFixedSubmodule (P : AdjointableMap B E E) : Submodule ℂ E where
  carrier := {x | P x = x}
  zero_mem' := by simp
  add_mem' hx hy := by
    change P (_ + _) = _ + _
    rw [P.toCLM.map_add, hx, hy]
  smul_mem' c x hx := by
    change P (c • x) = c • x
    rw [P.toCLM.map_smul, hx]

/-- The right Hilbert-module carrier on which the projection acts as identity. -/
abbrev ProjectionModule (P : AdjointableMap B E E) := projectionFixedSubmodule P

@[simp] theorem mem_projectionFixedSubmodule (P : AdjointableMap B E E) (x : E) :
    x ∈ projectionFixedSubmodule P ↔ P x = x := Iff.rfl

instance projectionModuleSMul (P : AdjointableMap B E E) : SMul Bᵐᵒᵖ (ProjectionModule P) where
  smul b x := ⟨b • (x : E), by
    change P (b • (x : E)) = b • (x : E)
    rw [P.map_op_smul, x.property]⟩

@[simp] theorem projectionModule_coe_op_smul (P : AdjointableMap B E E)
    (b : Bᵐᵒᵖ) (x : ProjectionModule P) : ((b • x : ProjectionModule P) : E) = b • (x : E) := rfl

instance projectionModuleCStarModule (P : AdjointableMap B E E) : CStarModule Bᵐᵒᵖ (ProjectionModule P) where
  inner x y := ⟪(x : E), (y : E)⟫_(Bᵐᵒᵖ)
  inner_add_right := CStarModule.inner_add_right
  inner_self_nonneg := CStarModule.inner_self_nonneg
  inner_self := by
    intro x
    constructor
    · intro h
      apply Subtype.ext
      exact CStarModule.inner_self.mp h
    · intro h
      rw [h]
      exact CStarModule.inner_zero_left
  inner_op_smul_right := CStarModule.inner_op_smul_right
  inner_smul_right_complex := CStarModule.inner_smul_right_complex
  star_inner x y := CStarModule.star_inner (x : E) (y : E)
  norm_eq_sqrt_norm_inner_self x := CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) (x : E)

@[simp] theorem projectionModule_inner (P : AdjointableMap B E E) (x y : ProjectionModule P) :
    ⟪x, y⟫_(Bᵐᵒᵖ) = ⟪(x : E), (y : E)⟫_(Bᵐᵒᵖ) := rfl

/-- The actual projection range is closed for the ambient norm topology. -/
theorem projectionFixedSubmodule_isClosed (P : AdjointableMap B E E) :
    IsClosed (projectionFixedSubmodule P : Set E) := isClosed_eq P.toCLM.continuous continuous_id

/-- Completeness is proved by closedness inside the complete ambient module. -/
instance projectionModuleCompleteSpace [CompleteSpace E] (P : AdjointableMap B E E) :
    CompleteSpace (ProjectionModule P) := (projectionFixedSubmodule_isClosed P).completeSpace_coe

/-- Corestricting an actual idempotent to its fixed module is a bounded linear map. -/
def projectionCorestrictCLM (P : AdjointableMap B E E) (hP : IsStarProjection P) :
    E →L[ℂ] ProjectionModule P := P.toCLM.codRestrict (projectionFixedSubmodule P) (fun x => by
      change P (P x) = P x
      exact congrArg (fun T : AdjointableMap B E E => T x) hP.isIdempotentElem.eq)

@[simp] theorem projectionCorestrictCLM_coe (P : AdjointableMap B E E) (hP : IsStarProjection P) (x : E) :
    ((projectionCorestrictCLM P hP x : ProjectionModule P) : E) = P x := rfl

@[simp] theorem projectionCorestrictCLM_op_smul (P : AdjointableMap B E E)
    (hP : IsStarProjection P) (b : Bᵐᵒᵖ) (x : E) :
    projectionCorestrictCLM P hP (b • x) = b • projectionCorestrictCLM P hP x := by
  apply Subtype.ext
  exact P.map_op_smul b x

/-- Inclusion of a projection range is adjointable, with the ambient projection as adjoint. -/
def projectionInclusion (P : AdjointableMap B E E) (hP : IsStarProjection P) :
    AdjointableMap B (ProjectionModule P) E where
  toCLM := (projectionFixedSubmodule P).subtypeL
  adjointCLM := projectionCorestrictCLM P hP
  adjoint_identity x y := by
    change ⟪(x : E), y⟫_(Bᵐᵒᵖ) = ⟪(x : E), P y⟫_(Bᵐᵒᵖ)
    have h := P.adjoint_identity (x : E) y
    change ⟪P (x : E), y⟫_(Bᵐᵒᵖ) = ⟪(x : E), P.adjoint y⟫_(Bᵐᵒᵖ) at h
    have hs : P.adjoint = P := by simpa only [AdjointableMap.star_eq_adjoint] using hP.isSelfAdjoint.star_eq
    rw [x.property, hs] at h
    exact h

@[simp] theorem projectionInclusion_apply (P : AdjointableMap B E E) (hP : IsStarProjection P)
    (x : ProjectionModule P) : projectionInclusion P hP x = (x : E) := rfl

/-- The ambient projection with its codomain correctly restricted. -/
def projectionCorestrict (P : AdjointableMap B E E) (hP : IsStarProjection P) :
    AdjointableMap B E (ProjectionModule P) := (projectionInclusion P hP).adjoint

@[simp] theorem projectionCorestrict_coe (P : AdjointableMap B E E) (hP : IsStarProjection P) (x : E) :
    ((projectionCorestrict P hP x : ProjectionModule P) : E) = P x := rfl

theorem projectionCorestrict_comp_inclusion (P : AdjointableMap B E E) (hP : IsStarProjection P) :
    (projectionCorestrict P hP).comp (projectionInclusion P hP) = AdjointableMap.id := by
  ext x
  exact x.property

theorem projectionInclusion_comp_corestrict (P : AdjointableMap B E E) (hP : IsStarProjection P) :
    (projectionInclusion P hP).comp (projectionCorestrict P hP) = P := by ext x; rfl

/-- Countable generation descends through an actual bounded surjective module projection. -/
theorem projectionModule_isCountablyGenerated (P : AdjointableMap B E E) (hP : IsStarProjection P)
    (hE : IsCountablyGeneratedModule B E) : IsCountablyGeneratedModule B (ProjectionModule P) := by
  obtain ⟨ξ, hξ⟩ := hE
  let L := projectionCorestrictCLM P hP
  refine ⟨fun n => L (ξ n), ?_⟩
  have hm : ∀ x ∈ moduleGeneratingSpan (B := B) ξ,
      L x ∈ moduleGeneratingSpan (B := B) (fun n => L (ξ n)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨n, b, rfl⟩
      rw [projectionCorestrictCLM_op_smul]
      exact smul_mem_moduleGeneratingSpan _ n b
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  have hsurj : Function.Surjective L := by
    intro x
    refine ⟨(x : E), ?_⟩
    apply Subtype.ext
    exact x.property
  exact (hsurj.denseRange.dense_image L.continuous hξ).mono (by
    rintro y ⟨x, hx, rfl⟩
    exact hm x hx)

variable [StarOrderedRing B]

/-- A compact projection has a compact range inclusion. -/
theorem projectionInclusion_isModuleCompact (P : AdjointableMap B E E) (hP : IsStarProjection P)
    (hc : IsModuleCompact P) : IsModuleCompact (projectionInclusion P hP) := by
  have h := hc.comp_right (projectionInclusion P hP)
  have heq : P.comp (projectionInclusion P hP) = projectionInclusion P hP := by
    ext x
    exact x.property
  rwa [heq] at h

/-- The identity on a compact projection range is compact, with both embeddings proved. -/
theorem projectionModule_identity_isModuleCompact (P : AdjointableMap B E E) (hP : IsStarProjection P)
    (hc : IsModuleCompact P) : IsModuleCompact (1 : AdjointableMap B (ProjectionModule P) (ProjectionModule P)) := by
  have h := (projectionInclusion_isModuleCompact P hP hc).comp_left (projectionCorestrict P hP)
  change IsModuleCompact (AdjointableMap.id : AdjointableMap B (ProjectionModule P) (ProjectionModule P))
  simpa only [projectionCorestrict_comp_inclusion] using h

omit [StarOrderedRing B] in
/-- A rectangular partial isometry is unitary only after restricting to its initial/final ranges. -/
def projectionRangeEquiv (P : AdjointableMap B E E) (Q : AdjointableMap B F F)
    (T : AdjointableMap B E F) (hP : T.adjoint.comp T = P) (hQ : T.comp T.adjoint = Q) :
    HilbertModuleEquiv B (ProjectionModule P) (ProjectionModule Q) where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun := fun x => ⟨T (x : E), by
            change Q (T (x : E)) = T (x : E)
            rw [← hQ, AdjointableMap.comp_apply, ← AdjointableMap.comp_apply T.adjoint T,
              hP, x.property]⟩
          invFun := fun y => ⟨T.adjoint (y : F), by
            change P (T.adjoint (y : F)) = T.adjoint (y : F)
            rw [← hP, AdjointableMap.comp_apply, ← AdjointableMap.comp_apply T T.adjoint,
              hQ, y.property]⟩
          left_inv := fun x => by
            apply Subtype.ext
            change T.adjoint (T (x : E)) = (x : E)
            rw [← AdjointableMap.comp_apply, hP, x.property]
          right_inv := fun y => by
            apply Subtype.ext
            change T (T.adjoint (y : F)) = (y : F)
            rw [← AdjointableMap.comp_apply, hQ, y.property]
          map_add' := fun x y => Subtype.ext (T.toCLM.map_add (x : E) (y : E))
          map_smul' := fun c x => Subtype.ext (T.toCLM.map_smul c (x : E)) }
      norm_map' x := by
        change ‖T (x : E)‖ = ‖(x : E)‖
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) (T (x : E)),
          CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) (x : E)]
        congr 2
        rw [T.adjoint_identity]
        change ⟪(x : E), T.adjoint (T (x : E))⟫_(Bᵐᵒᵖ) = ⟪(x : E), (x : E)⟫_(Bᵐᵒᵖ)
        rw [← AdjointableMap.comp_apply, hP, x.property] }
  inner_map x y := by
    change ⟪T (x : E), T (y : E)⟫_(Bᵐᵒᵖ) = ⟪(x : E), (y : E)⟫_(Bᵐᵒᵖ)
    rw [T.adjoint_identity]
    change ⟪(x : E), T.adjoint (T (y : E))⟫_(Bᵐᵒᵖ) = ⟪(x : E), (y : E)⟫_(Bᵐᵒᵖ)
    rw [← AdjointableMap.comp_apply, hP, y.property]

omit [StarOrderedRing B] in
@[simp] theorem projectionRangeEquiv_apply (P : AdjointableMap B E E) (Q : AdjointableMap B F F)
    (T : AdjointableMap B E F) (hP : T.adjoint.comp T = P) (hQ : T.comp T.adjoint = Q)
    (x : ProjectionModule P) : ((projectionRangeEquiv P Q T hP hQ x : ProjectionModule Q) : F) = T (x : E) := rfl

end BC4lean.KKTheory
