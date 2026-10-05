import BC4lean.CocompactPieces

/-! # Continuous equivariant inclusions of invariant subspaces -/
namespace BC4lean.ProperActions
variable {Γ X : Type*} [Group Γ] [TopologicalSpace X] [MulAction Γ X]

namespace InvariantSubset
/-- Inclusion between invariant subsets, with their induced actions and topologies. -/
def inclusionMap {S T : InvariantSubset Γ X} (h : S ≤ T) : EquivariantMap Γ S T where
  toFun x := ⟨x.val, h x.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _
  map_smul' _ _ := rfl

@[simp] theorem inclusionMap_coe {S T : InvariantSubset Γ X} (h : S ≤ T) (x : S) :
    (inclusionMap h x : X) = (x : X) := rfl

@[simp] theorem inclusionMap_refl (S : InvariantSubset Γ X) :
    inclusionMap (le_refl S) = EquivariantMap.id := by
  ext x
  rfl

@[simp] theorem inclusionMap_comp {S T U : InvariantSubset Γ X}
    (hST : S ≤ T) (hTU : T ≤ U) :
    (inclusionMap hTU).comp (inclusionMap hST) = inclusionMap (hST.trans hTU) := by
  ext x
  rfl

@[simp] theorem inclusion_comp_inclusionMap {S T : InvariantSubset Γ X} (h : S ≤ T) :
    T.inclusion.comp (inclusionMap h) = S.inclusion := by
  ext x
  rfl

theorem inclusionMap_injective {S T : InvariantSubset Γ X} (h : S ≤ T) :
    Function.Injective (inclusionMap h) := by
  intro x y he
  exact Subtype.ext (congrArg (fun z : T => (z : X)) he)
/-- A three-subspace chain gives the same map by direct or successive inclusion. -/
example (S T U : InvariantSubset Γ X) (hST : S ≤ T) (hTU : T ≤ U) (x : S) :
    inclusionMap hTU (inclusionMap hST x) = inclusionMap (hST.trans hTU) x := rfl
end InvariantSubset

namespace CocompactPiece
/-- Inclusion of cocompact pieces uses the induced invariant-subspace actions. -/
def inclusionMap {S T : CocompactPiece Γ X} (h : S ≤ T) :
    EquivariantMap Γ S.toInvariantSubset T.toInvariantSubset :=
  InvariantSubset.inclusionMap h

@[simp] theorem inclusionMap_coe {S T : CocompactPiece Γ X} (h : S ≤ T)
    (x : S.toInvariantSubset) : (inclusionMap h x : X) = (x : X) := rfl

@[simp] theorem inclusionMap_refl (S : CocompactPiece Γ X) :
    inclusionMap (le_refl S) = EquivariantMap.id := by
  ext x
  rfl

@[simp] theorem inclusionMap_comp {S T U : CocompactPiece Γ X}
    (hST : S ≤ T) (hTU : T ≤ U) :
    (inclusionMap hTU).comp (inclusionMap hST) = inclusionMap (hST.trans hTU) := by
  ext x
  rfl

@[simp] theorem inclusion_comp_inclusionMap {S T : CocompactPiece Γ X} (h : S ≤ T) :
    T.toInvariantSubset.inclusion.comp (inclusionMap h) = S.toInvariantSubset.inclusion := by
  ext x
  rfl
end CocompactPiece
end BC4lean.ProperActions
