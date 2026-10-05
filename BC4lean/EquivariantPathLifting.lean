import BC4lean.DiskPathLifting
import BC4lean.CellularExtension
import Mathlib.Topology.ContinuousMap.Algebra

/-! # Equivariant path evaluation and lifting across orbit cells -/

noncomputable section
open scoped unitInterval

namespace BC4lean.ProperActions

universe u v

variable {Γ : Type u} {X : Type v} [Group Γ] [TopologicalSpace X]
variable [MulAction Γ X] [ContinuousConstSMul Γ X]

/-- Evaluation of an equivariant path at a fixed time. -/
def pathEvaluation (t : I) : EquivariantMap Γ C(I,X) X where
  toFun p := p t
  continuous_toFun := continuous_eval_const t
  map_smul' _ _ := rfl

/-- A path fixed by H is a continuous path in the H-fixed-point space. -/
def fixedPathMap (H : Subgroup Γ) :
    C(FixedPointSpace H C(I,X), C(I,FixedPointSpace H X)) where
  toFun p :=
    ⟨fun t => ⟨p.1 t, fun h => congrArg (fun q : C(I,X) => q t) (p.2 h)⟩,
      p.1.continuous.subtype_mk _⟩
  continuous_toFun := ContinuousMap.continuous_of_continuous_uncurry _
    (((continuous_subtype_val.comp continuous_fst).eval continuous_snd).subtype_mk _)

/-- A path in the fixed-point space gives an H-fixed path. -/
def pathFixedMap (H : Subgroup Γ) :
    C(C(I,FixedPointSpace H X), FixedPointSpace H C(I,X)) where
  toFun p := ⟨⟨fun t => (p t).1, continuous_subtype_val.comp p.continuous⟩,
    fun h => ContinuousMap.ext (fun t => (p t).2 h)⟩
  continuous_toFun :=
    (ContinuousMap.continuous_postcomp ⟨Subtype.val, continuous_subtype_val⟩).subtype_mk _

@[simp] theorem pathFixedMap_fixedPathMap (H : Subgroup Γ) (p : FixedPointSpace H C(I,X)) :
    pathFixedMap H (fixedPathMap H p) = p := by
  apply Subtype.ext
  exact ContinuousMap.ext (fun _ => rfl)

@[simp] theorem fixedPathMap_pathFixedMap (H : Subgroup Γ) (p : C(I,FixedPointSpace H X)) :
    fixedPathMap H (pathFixedMap H p) = p := by
  exact ContinuousMap.ext (fun _ => rfl)

variable [TopologicalSpace Γ] [DiscreteTopology Γ]

/-- Lift a family of boundary paths with prescribed disk endpoints across an orbit cell. -/
theorem orbitCell_path_lifting (H : Subgroup Γ) [ContractibleSpace (FixedPointSpace H X)]
    (n : ℕ) (a : EquivariantMap Γ (OrbitCell H (TopCat.diskBoundary.{u} n)) C(I,X))
    (f₀ f₁ : EquivariantMap Γ (OrbitCell H (TopCat.disk.{u} n)) X)
    (h₀ : (pathEvaluation 0).comp a = f₀.comp (OrbitCell.boundaryInclusion H n))
    (h₁ : (pathEvaluation 1).comp a = f₁.comp (OrbitCell.boundaryInclusion H n)) :
    ∃ F : EquivariantMap Γ (OrbitCell H (TopCat.disk.{u} n)) C(I,X),
      F.comp (OrbitCell.boundaryInclusion H n) = a ∧
      (pathEvaluation 0).comp F = f₀ ∧ (pathEvaluation 1).comp F = f₁ := by
  let a' := (fixedPathMap H).comp (cellEvaluation H a)
  obtain ⟨v, hv, hzero, hone⟩ := contractible_disk_path_lifting n a'
    (cellEvaluation H f₀) (cellEvaluation H f₁)
    (fun s => Subtype.ext (congrArg (fun f => f (QuotientGroup.mk 1,s)) h₀))
    (fun s => Subtype.ext (congrArg (fun f => f (QuotientGroup.mk 1,s)) h₁))
  let F := cellFromFixed H ((pathFixedMap H).comp v)
  have he : cellEvaluation H F = (pathFixedMap H).comp v :=
    (orbitCellMapEquiv H).apply_symm_apply _
  refine ⟨F, ?_, ?_, ?_⟩
  · apply (orbitCellMapEquiv H).injective
    change cellEvaluation H (F.comp (OrbitCell.map H (TopCat.diskBoundaryInclusion n).hom)) =
      cellEvaluation H a
    rw [cellEvaluation_comp, he]
    apply ContinuousMap.ext
    intro s
    change pathFixedMap H (v ((TopCat.diskBoundaryInclusion n) s)) = cellEvaluation H a s
    rw [hv]
    exact pathFixedMap_fixedPathMap H _
  · apply (orbitCellMapEquiv H).injective
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    have hx := congrArg (fun p : FixedPointSpace H C(I,X) => p.1 0)
      (ContinuousMap.congr_fun he x)
    exact hx.trans (congrArg Subtype.val (hzero x))
  · apply (orbitCellMapEquiv H).injective
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    have hx := congrArg (fun p : FixedPointSpace H C(I,X) => p.1 1)
      (ContinuousMap.congr_fun he x)
    exact hx.trans (congrArg Subtype.val (hone x))

end BC4lean.ProperActions
