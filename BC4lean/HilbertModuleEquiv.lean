import BC4lean.CompactModuleOperator

/-! # Unitary isomorphisms and transport of Hilbert module operators

A module isomorphism is an actual complex-linear isometric equivalence preserving
the coefficient-valued inner product. Coefficient linearity follows from that
identity. The two module types may differ. Such equivalences transport
adjointable maps and preserve their operator norms and module compactness.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {B E F G H : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H]

/-- A unitary isomorphism of right Hilbert modules over the same coefficients. -/
structure HilbertModuleEquiv (B E F : Type*) [NonUnitalCStarAlgebra B] [PartialOrder B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F] where
  linearIsometryEquiv : E ≃ₗᵢ[ℂ] F
  inner_map : ∀ x y,
    ⟪linearIsometryEquiv x, linearIsometryEquiv y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ)

namespace HilbertModuleEquiv

instance instCoeFun : CoeFun (HilbertModuleEquiv B E F) (fun _ => E → F) :=
  ⟨fun u => u.linearIsometryEquiv⟩

@[ext] theorem ext {u v : HilbertModuleEquiv B E F} (h : ∀ x, u x = v x) : u = v := by
  have hlin : u.linearIsometryEquiv = v.linearIsometryEquiv := LinearIsometryEquiv.ext h
  cases u
  cases v
  cases hlin
  rfl

theorem injective (u : HilbertModuleEquiv B E F) : Function.Injective u :=
  u.linearIsometryEquiv.injective

theorem surjective (u : HilbertModuleEquiv B E F) : Function.Surjective u :=
  u.linearIsometryEquiv.surjective

@[simp] theorem map_zero (u : HilbertModuleEquiv B E F) : u 0 = 0 :=
  u.linearIsometryEquiv.map_zero
@[simp] theorem map_add (u : HilbertModuleEquiv B E F) (x y : E) :
    u (x + y) = u x + u y := u.linearIsometryEquiv.map_add x y
@[simp] theorem map_smul (u : HilbertModuleEquiv B E F) (c : ℂ) (x : E) :
    u (c • x) = c • u x := u.linearIsometryEquiv.map_smul c x
@[simp] theorem map_neg (u : HilbertModuleEquiv B E F) (x : E) :
    u (-x) = -u x := u.linearIsometryEquiv.map_neg x
@[simp] theorem map_sub (u : HilbertModuleEquiv B E F) (x y : E) :
    u (x - y) = u x - u y := u.linearIsometryEquiv.map_sub x y
@[simp] theorem norm_map (u : HilbertModuleEquiv B E F) (x : E) :
    ‖u x‖ = ‖x‖ := u.linearIsometryEquiv.norm_map x

/-- The identity unitary module isomorphism. -/
def refl : HilbertModuleEquiv B E E where
  linearIsometryEquiv := LinearIsometryEquiv.refl ℂ E
  inner_map _ _ := rfl
@[simp] theorem refl_apply (x : E) : (refl : HilbertModuleEquiv B E E) x = x := rfl

/-- The inverse unitary module isomorphism. -/
def symm (u : HilbertModuleEquiv B E F) : HilbertModuleEquiv B F E where
  linearIsometryEquiv := u.linearIsometryEquiv.symm
  inner_map x y := by
    simpa only [LinearIsometryEquiv.apply_symm_apply] using
      (u.inner_map (u.linearIsometryEquiv.symm x) (u.linearIsometryEquiv.symm y)).symm

@[simp] theorem apply_symm_apply (u : HilbertModuleEquiv B E F) (y : F) :
    u (u.symm y) = y := u.linearIsometryEquiv.apply_symm_apply y
@[simp] theorem symm_apply_apply (u : HilbertModuleEquiv B E F) (x : E) :
    u.symm (u x) = x := u.linearIsometryEquiv.symm_apply_apply x
@[simp] theorem symm_symm (u : HilbertModuleEquiv B E F) : u.symm.symm = u := by
  ext x
  rfl

/-- Composition of unitary module isomorphisms. -/
def trans (u : HilbertModuleEquiv B E F) (v : HilbertModuleEquiv B F G) :
    HilbertModuleEquiv B E G where
  linearIsometryEquiv := u.linearIsometryEquiv.trans v.linearIsometryEquiv
  inner_map x y := (v.inner_map (u x) (u y)).trans (u.inner_map x y)
@[simp] theorem trans_apply (u : HilbertModuleEquiv B E F)
    (v : HilbertModuleEquiv B F G) (x : E) : u.trans v x = v (u x) := rfl

/-- A unitary module isomorphism respects the actual right coefficient action. -/
@[simp] theorem map_op_smul (u : HilbertModuleEquiv B E F) (a : Bᵐᵒᵖ) (x : E) :
    u (a • x) = a • u x := by
  apply module_inner_ext_left (B := B)
  intro z
  obtain ⟨y, rfl⟩ := u.surjective z
  rw [u.inner_map, CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_left, u.inner_map]

/-- Moving a unitary across the inner product gives its inverse. -/
theorem inner_left (u : HilbertModuleEquiv B E F) (x : E) (y : F) :
    ⟪u x, y⟫_(Bᵐᵒᵖ) = ⟪x, u.symm y⟫_(Bᵐᵒᵖ) := by
  simpa only [apply_symm_apply] using u.inner_map x (u.symm y)

theorem inner_right (u : HilbertModuleEquiv B E F) (x : F) (y : E) :
    ⟪u.symm x, y⟫_(Bᵐᵒᵖ) = ⟪x, u y⟫_(Bᵐᵒᵖ) := by
  simpa only [apply_symm_apply] using (u.inner_map (u.symm x) y).symm

/-- The forward unitary is adjointable, with its inverse as adjoint. -/
def toAdjointable (u : HilbertModuleEquiv B E F) : AdjointableMap B E F where
  toCLM := u.linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  adjointCLM := u.symm.linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  adjoint_identity := u.inner_left
@[simp] theorem toAdjointable_apply (u : HilbertModuleEquiv B E F) (x : E) :
    u.toAdjointable x = u x := rfl
@[simp] theorem toAdjointable_adjoint (u : HilbertModuleEquiv B E F) :
    u.toAdjointable.adjoint = u.symm.toAdjointable := by ext x; rfl

/-- Transport a map by unitary isomorphisms of its source and target modules. -/
def transportMap (u : HilbertModuleEquiv B E F) (v : HilbertModuleEquiv B G H)
    (T : AdjointableMap B E G) : AdjointableMap B F H :=
  v.toAdjointable.comp (T.comp u.symm.toAdjointable)
@[simp] theorem transportMap_apply (u : HilbertModuleEquiv B E F)
    (v : HilbertModuleEquiv B G H) (T : AdjointableMap B E G) (x : F) :
    u.transportMap v T x = v (T (u.symm x)) := rfl
@[simp] theorem transportMap_adjoint (u : HilbertModuleEquiv B E F)
    (v : HilbertModuleEquiv B G H) (T : AdjointableMap B E G) :
    (u.transportMap v T).adjoint = v.transportMap u T.adjoint := by ext x; rfl
@[simp] theorem transportMap_symm (u : HilbertModuleEquiv B E F)
    (v : HilbertModuleEquiv B G H) (T : AdjointableMap B E G) :
    u.symm.transportMap v.symm (u.transportMap v T) = T := by
  ext x
  simp only [transportMap_apply, symm_apply_apply, apply_symm_apply]

/-- Transport of endomorphisms by conjugation with a unitary module isomorphism. -/
def transport (u : HilbertModuleEquiv B E F) (T : AdjointableMap B E E) :
    AdjointableMap B F F := u.transportMap u T
@[simp] theorem transport_apply (u : HilbertModuleEquiv B E F)
    (T : AdjointableMap B E E) (x : F) : u.transport T x = u (T (u.symm x)) := rfl
@[simp] theorem transport_symm (u : HilbertModuleEquiv B E F)
    (T : AdjointableMap B E E) : u.symm.transport (u.transport T) = T :=
  u.transportMap_symm u T
@[simp] theorem transport_symm_symm (u : HilbertModuleEquiv B E F)
    (T : AdjointableMap B F F) : u.transport (u.symm.transport T) = T := by
  simpa only [symm_symm] using u.symm.transport_symm T
@[simp] theorem transport_zero (u : HilbertModuleEquiv B E F) :
    u.transport (0 : AdjointableMap B E E) = 0 := by
  ext x
  simp only [transport_apply, AdjointableMap.coe_zero_apply, map_zero]
@[simp] theorem transport_add (u : HilbertModuleEquiv B E F)
    (S T : AdjointableMap B E E) : u.transport (S + T) = u.transport S + u.transport T := by
  ext x
  simp only [transport_apply, AdjointableMap.coe_add_apply, map_add]
@[simp] theorem transport_sub (u : HilbertModuleEquiv B E F)
    (S T : AdjointableMap B E E) : u.transport (S - T) = u.transport S - u.transport T := by
  ext x
  simp only [transport_apply, AdjointableMap.coe_sub_apply, map_sub]
@[simp] theorem transport_smul (u : HilbertModuleEquiv B E F)
    (c : ℂ) (T : AdjointableMap B E E) : u.transport (c • T) = c • u.transport T := by
  ext x
  simp only [transport_apply, AdjointableMap.coe_smul_apply, map_smul]
@[simp] theorem transport_mul (u : HilbertModuleEquiv B E F)
    (S T : AdjointableMap B E E) : u.transport (S * T) = u.transport S * u.transport T := by
  ext x
  simp only [transport_apply, AdjointableMap.mul_apply, symm_apply_apply]
@[simp] theorem transport_one (u : HilbertModuleEquiv B E F) :
    u.transport (1 : AdjointableMap B E E) = 1 := by
  ext x
  simp only [transport_apply, AdjointableMap.one_apply, apply_symm_apply]
@[simp] theorem transport_star (u : HilbertModuleEquiv B E F)
    (T : AdjointableMap B E E) : u.transport (star T) = star (u.transport T) := by
  exact (u.transportMap_adjoint u T).symm

/-- Transport is an actual complex star-algebra equivalence of operator algebras. -/
def transportStarAlgEquiv (u : HilbertModuleEquiv B E F) :
    AdjointableMap B E E ≃⋆ₐ[ℂ] AdjointableMap B F F where
  toFun := u.transport
  invFun := u.symm.transport
  left_inv := u.transport_symm
  right_inv := u.transport_symm_symm
  map_add' := u.transport_add
  map_mul' := u.transport_mul
  map_star' := u.transport_star
  map_smul' := u.transport_smul

/-- Transport preserves the actual operator norm. -/
theorem transportMap_norm_le (u : HilbertModuleEquiv B E F)
    (v : HilbertModuleEquiv B G H) (T : AdjointableMap B E G) :
    ‖u.transportMap v T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖v (T (u.symm x))‖ ≤ ‖T.toCLM‖ * ‖x‖
  rw [v.norm_map]
  simpa only [norm_map] using T.toCLM.le_opNorm (u.symm x)

theorem transportMap_norm (u : HilbertModuleEquiv B E F)
    (v : HilbertModuleEquiv B G H) (T : AdjointableMap B E G) :
    ‖u.transportMap v T‖ = ‖T‖ := by
  apply le_antisymm (u.transportMap_norm_le v T)
  have h := u.symm.transportMap_norm_le v.symm (u.transportMap v T)
  simpa only [transportMap_symm] using h

@[simp] theorem transport_norm (u : HilbertModuleEquiv B E F)
    (T : AdjointableMap B E E) : ‖u.transport T‖ = ‖T‖ := u.transportMap_norm u T

variable [StarOrderedRing B]

/-- Compact maps transport by the genuine cross-module composition ideal laws. -/
theorem transportMap_isModuleCompact (u : HilbertModuleEquiv B E F)
    (v : HilbertModuleEquiv B G H) {T : AdjointableMap B E G} (hT : IsModuleCompact T) :
    IsModuleCompact (u.transportMap v T) :=
  (hT.comp_right u.symm.toAdjointable).comp_left v.toAdjointable

@[simp] theorem transportMap_isModuleCompact_iff (u : HilbertModuleEquiv B E F)
    (v : HilbertModuleEquiv B G H) (T : AdjointableMap B E G) :
    IsModuleCompact (u.transportMap v T) ↔ IsModuleCompact T := by
  constructor
  · intro hT
    have h := u.symm.transportMap_isModuleCompact v.symm hT
    simpa only [transportMap_symm] using h
  · exact u.transportMap_isModuleCompact v

@[simp] theorem transport_isModuleCompact_iff (u : HilbertModuleEquiv B E F)
    (T : AdjointableMap B E E) : IsModuleCompact (u.transport T) ↔ IsModuleCompact T :=
  u.transportMap_isModuleCompact_iff u T

end HilbertModuleEquiv
end BC4lean.KKTheory
