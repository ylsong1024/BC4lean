import BC4lean.CliffordExternalOddModule
import BC4lean.GradedMatrixMoritaEquivariant

/-! # The genuine group action on the odd external Clifford tensor

The action is the actual completed interior tensor action. Its equality
with the original pair action tensored with the trivial Clifford action
is proved on complete row coordinates by coefficient approximate units.
The coefficient automorphism remains arbitrary and need not fix an
individual member of the chosen approximate unit.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordExternalOddAction
open scoped TensorProduct Topology
open CliffordExternalOddCoordinates MatrixHilbertModuleCoordinateEmbedding
open GradedMatrixMoritaEquivariant

variable {Γ C H : Type*} [Group Γ]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H]
  [CStarModule Cᵐᵒᵖ H] [actionComplete : CompleteSpace H]
  {β : CStarAlgebraAction Γ C}

local instance cliffordExternalOddActionLocalInstance1 : CompleteSpace (HilbertModuleSum C H H) := hilbertModuleSum_complete

def action (U : EquivariantHilbertModule β H) :
    EquivariantHilbertModule (matrixAction β) (ExternalModule (C := C) (H := H)) :=
  (U.sum U).interiorTensor (rowAction β) (rowRepresentation_equivariant β)

theorem rowAction_element (g : Γ) (j : Fin 2) (a : Cᵐᵒᵖ) :
    (rowAction β).action g (rowElement j a) =
      rowElement j (opStarAlgEquiv (β.automorphism g) a) := by
  apply Subtype.ext
  apply MulOpposite.unop_injective
  change matrixEquiv (β.automorphism g) (entryMatrix 0 j (MulOpposite.unop a)) =
    entryMatrix 0 j (β.automorphism g (MulOpposite.unop a))
  ext r s
  change β.automorphism g (if r = 0 ∧ s = j then MulOpposite.unop a else 0) =
    if r = 0 ∧ s = j then β.automorphism g (MulOpposite.unop a) else 0
  by_cases h : r = 0 ∧ s = j <;> simp [h]

theorem action_coordinate (U : EquivariantHilbertModule β H)
    (g : Γ) (j : Fin 2) (x : HilbertModuleSum C H H) :
    (action U).action g (coordinate j x) = coordinate j ((U.sum U).action g x) := by
  have hφ : ModuleTensorRepresentationEquivariant
      (GradedMatrixMoritaRow.leftAction (B := C)) β (rowAction β) := by
    intro h b v
    exact rowRepresentation_equivariant β h b v
  have hunit := tendsto_coefficient_approximateUnit_smul (D := Cᵐᵒᵖ) x
  have hleft := (((action U).action g).continuous.tendsto
      ((coordinate (C := C) (H := HilbertModuleSum C H H)) j x)).comp
    ((((coordinate (C := C) (H := HilbertModuleSum C H H)) j).continuous.tendsto x).comp
      hunit)
  have hright := (((coordinate (C := C) (H := HilbertModuleSum C H H)) j).continuous.tendsto
      ((U.sum U).action g x)).comp
    ((((U.sum U).action g).continuous.tendsto x).comp hunit)
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  exact Filter.Eventually.of_forall fun a => by
    change (coordinate (C := C) (H := HilbertModuleSum C H H)) j
        ((U.sum U).action g (a • x)) =
      (action U).action g
        ((coordinate (C := C) (H := HilbertModuleSum C H H)) j (a • x))
    rw [(U.sum U).map_op_smul, coordinate_smul, coordinate_smul]
    change interiorModuleTensorMk (E := HilbertModuleSum C H H)
        (GradedMatrixMoritaRow.leftAction (B := C)) ((U.sum U).action g x)
          (rowElement j (opStarAlgEquiv (β.automorphism g) a)) =
      ((U.sum U).interiorTensor (rowAction β) hφ).action g
        (interiorModuleTensorMk (E := HilbertModuleSum C H H)
          (GradedMatrixMoritaRow.leftAction (B := C)) x (rowElement j a))
    rw [EquivariantHilbertModule.interiorTensor_action_mk
      (φ := GradedMatrixMoritaRow.leftAction (B := C))
      (U.sum U) (rowAction β) hφ g x (rowElement j a), rowAction_element]

theorem action_coordinateSum (U : EquivariantHilbertModule β H)
    (g : Γ) (x : RowCoordinates (C := C) (H := H)) :
    (action U).action g (coordinateSum x) =
      coordinateSum ((U.sum U).action g x.1, (U.sum U).action g x.2) := by
  simp only [coordinateSum_apply, map_add, action_coordinate]

theorem action_rotation (U : EquivariantHilbertModule β H)
    (g : Γ) (x : HilbertModuleSum C H H) :
    (U.sum U).action g (CliffordOddPauliRotation.hilbertEquiv x) =
      CliffordOddPauliRotation.hilbertEquiv ((U.sum U).action g x) := by
  apply Prod.ext <;>
    simp only [EquivariantHilbertModule.sum_action_apply,
      CliffordOddPauliRotation.hilbertEquiv_apply, sumMk_fst, sumMk_snd, map_add, map_smul]

theorem action_rotation_symm (U : EquivariantHilbertModule β H)
    (g : Γ) (x : HilbertModuleSum C H H) :
    (U.sum U).action g (CliffordOddPauliRotation.hilbertEquiv.symm x) =
      CliffordOddPauliRotation.hilbertEquiv.symm ((U.sum U).action g x) := by
  apply CliffordOddPauliRotation.hilbertEquiv.injective
  rw [← action_rotation, HilbertModuleEquiv.apply_symm_apply,
    HilbertModuleEquiv.apply_symm_apply]

omit actionComplete in
theorem pureColumns_action [CompleteSpace H] (U : EquivariantHilbertModule β H)
    (g : Γ) (y : CliffordPairModule C H) (z : CliffordOne) :
    ((U.sum U).action g (pureColumns y z).1,
      (U.sum U).action g (pureColumns y z).2) =
        pureColumns (cliffordPairMk (U.action g y.1) (U.action g y.2)) z := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [pureColumns, EquivariantHilbertModule.sum_action_apply,
      cliffordPairMk, sumMk_fst, sumMk_snd, map_smul]

set_option maxHeartbeats 1200000 in
/-- The actual completed action is the original group action tensored with Cl₁. -/
theorem coordinates_action_tmul (U : EquivariantHilbertModule β H)
    (g : Γ) (y : CliffordPairModule C H) (z : CliffordOne) :
    (action U).action g (coordinates (y ⊗ₜ[ℂ] z)) =
      coordinates ((cliffordPairMk (U.action g y.1) (U.action g y.2)) ⊗ₜ[ℂ] z) := by
  rw [coordinates_apply, action_coordinateSum, coordinates_apply,
    rowCoordinates_tmul, rowCoordinates_tmul,
    action_rotation_symm, action_rotation_symm]
  have h := pureColumns_action (C := C) (H := H) U g y z
  let R : HilbertModuleSum C H H → HilbertModuleSum C H H :=
    (CliffordOddPauliRotation.hilbertEquiv (C := C) (H := H)).symm
  have hrot :
      (R ((U.sum U).action g (pureColumns y z).1),
        R ((U.sum U).action g (pureColumns y z).2)) =
      (R (pureColumns (cliffordPairMk (U.action g y.1) (U.action g y.2)) z).1,
        R (pureColumns (cliffordPairMk (U.action g y.1) (U.action g y.2)) z).2) :=
    congrArg (fun p : RowCoordinates (C := C) (H := H) => (R p.1, R p.2)) h
  apply congrArg (coordinateSum (C := C) (H := HilbertModuleSum C H H))
  exact hrot

end BC4lean.KKTheory.CliffordExternalOddAction
