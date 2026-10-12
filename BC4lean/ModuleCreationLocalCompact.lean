import BC4lean.ModuleTensorCompact
import BC4lean.HilbertModuleCoefficientApproximateUnit

/-! # Actual creation-local compactness and its closed operator algebra

A second-module operator which is compact after left coefficient
localization becomes compact after any actual creation map. This uses the
proved strong coefficient approximate unit and operator-norm continuity of
creation. Endomorphisms compact on all creation ranges, together with their
adjoints, form a closed non-unital star algebra. They annihilate the genuine
induced first-factor compact operators on both sides modulo module compacts.
-/

noncomputable section
namespace BC4lean.KKTheory

open Filter
open scoped InnerProductSpace Topology

variable {B C E F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

/-- The genuine coefficient approximate unit proves compactness after
creation from localized compactness of a second-module operator. -/
theorem moduleCreationMap_comp_isModuleCompact_of_left_local
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x : E) (T : AdjointableMap C F F)
    (hT : ∀ b, IsModuleCompact ((φ b).comp T)) :
    IsModuleCompact ((moduleCreationMap φ x).comp T) := by
  have hlim := (AdjointableMap.compRightContinuousLinearMap T).continuous.tendsto
    (moduleCreationMap φ x) |>.comp
      ((moduleCreationContinuousLinearMap (E := E) φ).continuous.tendsto x |>.comp
        (tendsto_coefficient_approximateUnit_smul (D := Bᵐᵒᵖ) x))
  apply moduleCompact_isClosed.mem_of_tendsto hlim
  apply Eventually.of_forall
  intro b
  change IsModuleCompact ((moduleCreationMap φ (b • x)).comp T)
  rw [show b = MulOpposite.op (MulOpposite.unop b) from (MulOpposite.op_unop b).symm,
    moduleCreationMap_balance, AdjointableMap.comp_assoc]
  exact (hT (MulOpposite.unop b)).comp_left (moduleCreationMap φ x)

/-- Right-local compactness of an operator and its adjoint supplies the
left-local compactness used by the actual creation theorem. -/
theorem moduleCreationMap_comp_isModuleCompact_of_local
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) (x : E) (T : AdjointableMap C F F)
    (hT : ∀ b, IsModuleCompact (T * φ b))
    (hTstar : ∀ b, IsModuleCompact (star T * φ b)) :
    IsModuleCompact ((moduleCreationMap φ x).comp T) := by
  have hlocal : ∀ b, IsModuleCompact (T * φ b) ∧
      IsModuleCompact (star T * φ b) := fun b => ⟨hT b, hTstar b⟩
  apply moduleCreationMap_comp_isModuleCompact_of_left_local φ x T
  intro b
  have h := ((hlocal (star b)).2).adjoint
  change IsModuleCompact (star (star T * φ (star b))) at h
  have hmul : φ b * T = (φ b).comp T := by ext y; rfl
  rw [← hmul]
  simpa only [star_mul, map_star, star_star] using h

/-- An actual tensor endomorphism is creation-locally compact when it and
its adjoint are compact on every actual creation range. -/
def IsCreationLocallyCompact
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (T : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ)) : Prop :=
  ∀ x : E, IsModuleCompact (T.comp (moduleCreationMap φ x)) ∧
    IsModuleCompact (T.adjoint.comp (moduleCreationMap φ x))

namespace IsCreationLocallyCompact

variable {φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F}
  {S T : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ)}

theorem of_compact (hT : IsModuleCompact T) : IsCreationLocallyCompact φ T :=
  fun x => ⟨hT.comp_right (moduleCreationMap φ x),
    hT.adjoint.comp_right (moduleCreationMap φ x)⟩

theorem of_selfadjoint (hT : IsSelfAdjoint T)
    (hcomp : ∀ x : E, IsModuleCompact (T.comp (moduleCreationMap φ x))) :
    IsCreationLocallyCompact φ T := by
  intro x
  refine ⟨hcomp x, ?_⟩
  change IsModuleCompact ((star T).comp (moduleCreationMap φ x))
  rw [hT.star_eq]
  exact hcomp x

theorem adjoint (hT : IsCreationLocallyCompact φ T) : IsCreationLocallyCompact φ T.adjoint :=
  fun x => ⟨(hT x).2, by simpa only [AdjointableMap.adjoint_adjoint] using (hT x).1⟩

theorem add (hS : IsCreationLocallyCompact φ S) (hT : IsCreationLocallyCompact φ T) :
    IsCreationLocallyCompact φ (S + T) := by
  intro x
  let L : AdjointableMap C (InteriorModuleTensor (E := E) φ)
      (InteriorModuleTensor (E := E) φ) →L[ℂ]
      AdjointableMap C F (InteriorModuleTensor (E := E) φ) :=
    AdjointableMap.compRightContinuousLinearMap (moduleCreationMap φ x)
  constructor
  · change IsModuleCompact (L (S + T))
    rw [map_add]
    exact ((hS x).1).add ((hT x).1)
  · change IsModuleCompact ((AdjointableMap.add S T).adjoint.comp (moduleCreationMap φ x))
    rw [AdjointableMap.adjoint_add]
    change IsModuleCompact (L (S.adjoint + T.adjoint))
    rw [map_add]
    exact ((hS x).2).add ((hT x).2)

theorem mul (hS : IsCreationLocallyCompact φ S) (hT : IsCreationLocallyCompact φ T) :
    IsCreationLocallyCompact φ (S * T) := by
  intro x
  constructor
  · change IsModuleCompact (S.comp (T.comp (moduleCreationMap φ x)))
    exact ((hT x).1).comp_left S
  · change IsModuleCompact (T.adjoint.comp (S.adjoint.comp (moduleCreationMap φ x)))
    exact ((hS x).2).comp_left T.adjoint

theorem smul (hT : IsCreationLocallyCompact φ T) (c : ℂ) :
    IsCreationLocallyCompact φ (c • T) := by
  intro x
  let L : AdjointableMap C (InteriorModuleTensor (E := E) φ)
      (InteriorModuleTensor (E := E) φ) →L[ℂ]
      AdjointableMap C F (InteriorModuleTensor (E := E) φ) :=
    AdjointableMap.compRightContinuousLinearMap (moduleCreationMap φ x)
  constructor
  · change IsModuleCompact (L (c • T))
    rw [map_smul]
    exact ((hT x).1).smul c
  · change IsModuleCompact ((AdjointableMap.smul c T).adjoint.comp (moduleCreationMap φ x))
    rw [AdjointableMap.adjoint_smul]
    change IsModuleCompact (L (star c • T.adjoint))
    rw [map_smul]
    exact ((hT x).2).smul (star c)

/-- Creation-local compactness annihilates genuine induced first-factor
module compacts on the left. -/
theorem mul_tensorCompact (hT : IsCreationLocallyCompact φ T)
    {K : AdjointableMap B E E} (hK : IsModuleCompact K) :
    IsModuleCompact (T * interiorModuleTensorOperator φ K) := by
  let L := (AdjointableMap.compLeftContinuousLinearMap T).comp
    (interiorModuleTensorOperatorCLM (E := E) φ)
  let V := (moduleCompact C (InteriorModuleTensor (E := E) φ)
    (InteriorModuleTensor (E := E) φ)).comap L.toLinearMap
  have hV : IsClosed (V : Set (AdjointableMap B E E)) := moduleCompact_isClosed.preimage L.continuous
  have hθ : ∀ x y : E, moduleRankOne (B := B) x y ∈ V := by
    intro x y
    change IsModuleCompact (T.comp (interiorModuleTensorOperator φ (moduleRankOne x y)))
    rw [interiorModuleTensorOperator_rankOne, ← AdjointableMap.comp_assoc]
    exact ((hT x).1).comp_right _
  exact moduleCompact_le_of_isClosed V hV hθ hK

/-- The adjoint creation condition supplies the corresponding right
annihilation of actual induced first-factor compacts. -/
theorem tensorCompact_mul (hT : IsCreationLocallyCompact φ T)
    {K : AdjointableMap B E E} (hK : IsModuleCompact K) :
    IsModuleCompact (interiorModuleTensorOperator φ K * T) := by
  have h := (hT.adjoint.mul_tensorCompact hK.adjoint).adjoint
  change IsModuleCompact ((T.adjoint.comp
    (interiorModuleTensorOperator φ K.adjoint)).adjoint) at h
  have hmul : interiorModuleTensorOperator φ K * T =
      (interiorModuleTensorOperator φ K).comp T := by ext y; rfl
  rw [hmul]
  simpa only [AdjointableMap.adjoint_comp, AdjointableMap.adjoint_adjoint,
    interiorModuleTensorOperator_adjoint] using h

end IsCreationLocallyCompact

/-- The concrete creation-local operators form a genuine non-unital star
subalgebra of actual tensor endomorphisms. -/
def creationLocallyCompactAlgebra
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    NonUnitalStarSubalgebra ℂ
      (AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ)) where
  carrier := {T | IsCreationLocallyCompact φ T}
  zero_mem' := IsCreationLocallyCompact.of_compact IsModuleCompact.zero
  add_mem' := fun hS hT => hS.add hT
  mul_mem' := fun hS hT => hS.mul hT
  smul_mem' := fun c _ hT => hT.smul c
  star_mem' := fun hT => hT.adjoint

/-- Both families of rectangular compact conditions are closed in the
actual operator norm. -/
theorem creationLocallyCompactAlgebra_isClosed
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    IsClosed (creationLocallyCompactAlgebra (E := E) φ : Set
      (AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ))) := by
  change IsClosed {T : AdjointableMap C (InteriorModuleTensor (E := E) φ)
    (InteriorModuleTensor (E := E) φ) |
      ∀ x : E, IsModuleCompact (T.comp (moduleCreationMap φ x)) ∧
        IsModuleCompact (T.adjoint.comp (moduleCreationMap φ x))}
  simp only [Set.ofPred_forall, Set.ofPred_and]
  apply isClosed_iInter
  intro x
  let L : AdjointableMap C (InteriorModuleTensor (E := E) φ)
      (InteriorModuleTensor (E := E) φ) →L[ℂ]
      AdjointableMap C F (InteriorModuleTensor (E := E) φ) :=
    AdjointableMap.compRightContinuousLinearMap (moduleCreationMap φ x)
  exact (moduleCompact_isClosed.preimage L.continuous).inter
    (moduleCompact_isClosed.preimage
      (L.continuous.comp AdjointableMap.adjointContinuousLinearMap.continuous))

end BC4lean.KKTheory
