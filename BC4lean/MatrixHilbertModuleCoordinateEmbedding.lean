import BC4lean.GradedMatrixMoritaRow
import BC4lean.RightStandardModuleTensor
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.Algebra.LinearMapCompletion

/-! # Coordinates in the genuine matrix-coefficient row tensor

For a complete right C-module H, each matrix coordinate embeds H into
H ⊗_C Row₂(C). The construction first maps the actual balanced tensor
H ⊗_C C into the row tensor, descends through its null radical, and extends
its proved corner-valued isometry to the completion. The nonunital right
tensor unit then supplies the embeddings of H itself.

The cross-coordinate pairing is the corresponding off-diagonal matrix
entry. Consequently the sum of both coordinates is a complex Banach-space
equivalence, with the full matrix Gram form recorded explicitly. No identity
element of C, coefficient-linear grading of H, or Morita equivalence is
assumed.
-/

noncomputable section
namespace BC4lean.KKTheory.MatrixHilbertModuleCoordinateEmbedding
open scoped InnerProductSpace

variable {C : Type*} [NonUnitalCStarAlgebra C]

/-- A single entry in the actual C⋆ matrix algebra. -/
def entryMatrix (j k : Fin 2) (c : C) : GradedMatrixMoritaMatrix C :=
  CStarMatrix.ofMatrix fun r s => if r = j ∧ s = k then c else 0

@[simp] theorem entryMatrix_apply (j k r s : Fin 2) (c : C) :
    entryMatrix j k c r s = if r = j ∧ s = k then c else 0 := rfl

@[simp] theorem entryMatrix_zero (j k : Fin 2) : entryMatrix j k (0 : C) = 0 := by
  ext r s
  simp [entryMatrix_apply]

@[simp] theorem entryMatrix_add (j k : Fin 2) (c d : C) :
    entryMatrix j k (c + d) = entryMatrix j k c + entryMatrix j k d := by
  ext r s
  by_cases h : r = j ∧ s = k <;> simp [entryMatrix_apply, h]

@[simp] theorem entryMatrix_smul (j k : Fin 2) (z : ℂ) (c : C) :
    entryMatrix j k (z • c) = z • entryMatrix j k c := by
  ext r s
  by_cases h : r = j ∧ s = k <;> simp [entryMatrix_apply, h]

def diagonalEntryHom (j : Fin 2) : C →⋆ₙₐ[ℂ] GradedMatrixMoritaMatrix C where
  toFun := entryMatrix j j
  map_zero' := entryMatrix_zero j j
  map_add' := entryMatrix_add j j
  map_smul' := entryMatrix_smul j j
  map_mul' c d := by
    ext r s
    fin_cases j <;> fin_cases r <;> fin_cases s <;>
      simp [entryMatrix_apply, CStarMatrix.mul_apply]
  map_star' c := by
    ext r s
    fin_cases j <;> fin_cases r <;> fin_cases s <;>
      simp [entryMatrix_apply, CStarMatrix.star_apply]

theorem diagonalEntryHom_injective (j : Fin 2) :
    Function.Injective (diagonalEntryHom (C := C) j) := by
  intro c d h
  simpa [diagonalEntryHom, entryMatrix_apply] using
    congrArg (fun M : GradedMatrixMoritaMatrix C => M j j) h

variable [PartialOrder C] [StarOrderedRing C]

@[simp] theorem norm_diagonalEntry (j : Fin 2) (c : C) :
    ‖entryMatrix j j c‖ = ‖c‖ :=
  NonUnitalStarAlgHom.norm_map (diagonalEntryHom j) (diagonalEntryHom_injective j) c

omit [PartialOrder C] [StarOrderedRing C] in
theorem entryMatrix_star_mul_self (j k : Fin 2) (c : C) :
    star (entryMatrix j k c) * entryMatrix j k c = entryMatrix k k (star c * c) := by
  ext r s
  fin_cases j <;> fin_cases k <;> fin_cases r <;> fin_cases s <;>
    simp [entryMatrix_apply, CStarMatrix.star_apply, CStarMatrix.mul_apply]

@[simp] theorem norm_entryMatrix (j k : Fin 2) (c : C) :
    ‖entryMatrix j k c‖ = ‖c‖ := by
  have hs : ‖entryMatrix j k c‖ * ‖entryMatrix j k c‖ = ‖c‖ * ‖c‖ := by
    rw [← CStarRing.norm_star_mul_self, entryMatrix_star_mul_self,
      norm_diagonalEntry, CStarRing.norm_star_mul_self]
  nlinarith [norm_nonneg (entryMatrix j k c), norm_nonneg c]

/-- The off-diagonal insertion is continuous as well as complex linear. -/
def entryCLM (j k : Fin 2) : C →L[ℂ] GradedMatrixMoritaMatrix C :=
  LinearMap.mkContinuous
    { toFun := entryMatrix j k
      map_add' := entryMatrix_add j k
      map_smul' := entryMatrix_smul j k }
    1 (fun c => by simp)

/-- The same genuine entry map in the right-module opposite convention. -/
def coefficientEntry (j k : Fin 2) : Cᵐᵒᵖ →L[ℂ] (GradedMatrixMoritaMatrix C)ᵐᵒᵖ :=
  LinearMap.mkContinuous
    { toFun := fun c => MulOpposite.op (entryMatrix j k (MulOpposite.unop c))
      map_add' c d := by simp [MulOpposite.unop_add, MulOpposite.op_add]
      map_smul' z c := by simp [MulOpposite.unop_smul, MulOpposite.op_smul] }
    1 (fun c => by simp [MulOpposite.norm_op, ← MulOpposite.norm_unop c])

@[simp] theorem coefficientEntry_apply (j k : Fin 2) (c : Cᵐᵒᵖ) :
    coefficientEntry j k c = MulOpposite.op (entryMatrix j k (MulOpposite.unop c)) := rfl

@[simp] theorem norm_coefficientEntry (j k : Fin 2) (c : Cᵐᵒᵖ) :
    ‖coefficientEntry j k c‖ = ‖c‖ := by
  simp [coefficientEntry_apply, MulOpposite.norm_op, MulOpposite.norm_unop]

/-- The first row having coefficient a in precisely column j. -/
def rowElement (j : Fin 2) (a : Cᵐᵒᵖ) : GradedMatrixMoritaRow C :=
  ⟨MulOpposite.op (entryMatrix 0 j (MulOpposite.unop a)), by
    intro k
    simp [entryMatrix_apply]⟩

@[simp] theorem matrix_rowElement (j : Fin 2) (a : Cᵐᵒᵖ) :
    GradedMatrixMoritaRow.matrix (rowElement j a) = entryMatrix 0 j (MulOpposite.unop a) := rfl

def rowElementLinear (j : Fin 2) : Cᵐᵒᵖ →ₗ[ℂ] GradedMatrixMoritaRow C where
  toFun := rowElement j
  map_add' a b := by
    apply Subtype.ext
    simp [rowElement, MulOpposite.unop_add, MulOpposite.op_add]
  map_smul' z a := by
    apply Subtype.ext
    simp [rowElement, MulOpposite.unop_smul, MulOpposite.op_smul]

theorem rowElement_leftAction (j : Fin 2) (c : C) (a : Cᵐᵒᵖ) :
    rowElement j (standardLeftMul c a) = GradedMatrixMoritaRow.leftAction c (rowElement j a) := by
  apply Subtype.ext
  apply MulOpposite.unop_injective
  change entryMatrix 0 j (c * MulOpposite.unop a) =
    GradedMatrixMoritaMatrix.corner c * entryMatrix 0 j (MulOpposite.unop a)
  ext r s
  fin_cases j <;> fin_cases r <;> fin_cases s <;>
    simp [entryMatrix_apply, GradedMatrixMoritaMatrix.corner, CStarMatrix.ofMatrix_apply, CStarMatrix.mul_apply]

/-- Every genuine row is the sum of its two coordinate rows. -/
theorem rowElement_decomposition (r : GradedMatrixMoritaRow C) :
    r = rowElement 0 (MulOpposite.op (GradedMatrixMoritaRow.matrix r 0 0)) +
      rowElement 1 (MulOpposite.op (GradedMatrixMoritaRow.matrix r 0 1)) := by
  apply Subtype.ext
  apply MulOpposite.unop_injective
  change GradedMatrixMoritaRow.matrix r =
    entryMatrix 0 0 (GradedMatrixMoritaRow.matrix r 0 0) +
      entryMatrix 0 1 (GradedMatrixMoritaRow.matrix r 0 1)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [entryMatrix_apply, GradedMatrixMoritaRow.matrix_second_row]

@[simp] theorem rowElement_parity_zero (a : Cᵐᵒᵖ) :
    GradedMatrixMoritaRow.parity (rowElement 0 a) = rowElement 0 a := by
  apply Subtype.ext
  apply MulOpposite.unop_injective
  change GradedMatrixMoritaMatrix.parity (entryMatrix 0 0 (MulOpposite.unop a)) =
    entryMatrix 0 0 (MulOpposite.unop a)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [entryMatrix_apply, GradedMatrixMoritaMatrix.parity, CStarMatrix.ofMatrix_apply]

@[simp] theorem rowElement_parity_one (a : Cᵐᵒᵖ) :
    GradedMatrixMoritaRow.parity (rowElement 1 a) = -rowElement 1 a := by
  apply Subtype.ext
  apply MulOpposite.unop_injective
  change GradedMatrixMoritaMatrix.parity (entryMatrix 0 1 (MulOpposite.unop a)) =
    -entryMatrix 0 1 (MulOpposite.unop a)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [entryMatrix_apply, GradedMatrixMoritaMatrix.parity, CStarMatrix.ofMatrix_apply]

section Tensor

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [SMul Cᵐᵒᵖ H] [CStarModule Cᵐᵒᵖ H]

abbrev SourceBalanced := BalancedModuleTensor (E := H) (standardLeftMul (B := C))
abbrev TargetBalanced := BalancedModuleTensor (E := H) (GradedMatrixMoritaRow.leftAction (B := C))

def balancedBilinear (j : Fin 2) : H →ₗ[ℂ] Cᵐᵒᵖ →ₗ[ℂ] TargetBalanced (C := C) (H := H) where
  toFun x := ((moduleTensorMk (E := H)) (GradedMatrixMoritaRow.leftAction (B := C)) x).comp (rowElementLinear j)
  map_add' x y := by
    ext a
    change (moduleTensorMk (E := H)) (GradedMatrixMoritaRow.leftAction (B := C))
      (x + y) (rowElement j a) =
      (moduleTensorMk (E := H)) (GradedMatrixMoritaRow.leftAction (B := C)) x (rowElement j a) +
        (moduleTensorMk (E := H)) (GradedMatrixMoritaRow.leftAction (B := C)) y (rowElement j a)
    simp only [map_add, LinearMap.add_apply]
  map_smul' z x := by
    ext a
    change (moduleTensorMk (E := H)) (GradedMatrixMoritaRow.leftAction (B := C))
      (z • x) (rowElement j a) =
      z • (moduleTensorMk (E := H)) (GradedMatrixMoritaRow.leftAction (B := C)) x (rowElement j a)
    simp only [map_smul, LinearMap.smul_apply]

omit [CStarModule Cᵐᵒᵖ H] in
theorem balancedBilinear_balance (j : Fin 2) (c : C) (x : H) (a : Cᵐᵒᵖ) :
    (balancedBilinear (C := C) (H := H)) j (MulOpposite.op c • x) a = (balancedBilinear (C := C) (H := H)) j x ((standardLeftMul (B := C)) c a) := by
  change (moduleTensorMk (E := H)) (GradedMatrixMoritaRow.leftAction (B := C)) (MulOpposite.op c • x) (rowElement j a) =
    (moduleTensorMk (E := H)) (GradedMatrixMoritaRow.leftAction (B := C)) x (rowElement j ((standardLeftMul (B := C)) c a))
  rw [moduleTensorMk_balance, rowElement_leftAction]

def balancedMap (j : Fin 2) : SourceBalanced (C := C) (H := H) →ₗ[ℂ]
    TargetBalanced (C := C) (H := H) :=
  (moduleTensorLift (E := H)) (standardLeftMul (B := C)) ((balancedBilinear (C := C) (H := H)) j) ((balancedBilinear_balance (C := C) (H := H)) j)

omit [CStarModule Cᵐᵒᵖ H] in
@[simp] theorem balancedMap_mk (j : Fin 2) (x : H) (a : Cᵐᵒᵖ) :
    (balancedMap (C := C) (H := H)) j ((moduleTensorMk (E := H)) (standardLeftMul (B := C)) x a) =
      (moduleTensorMk (E := H)) (GradedMatrixMoritaRow.leftAction (B := C)) x (rowElement j a) := rfl

/-- In particular the mixed pairing is the actual (j,k) matrix entry. -/
theorem pure_cross_inner (j k : Fin 2) (x y : H) (a b : Cᵐᵒᵖ) :
    (moduleTensorPureInner (E := H)) (GradedMatrixMoritaRow.leftAction (B := C)) x (rowElement j a) y (rowElement k b) =
      coefficientEntry j k ((moduleTensorPureInner (E := H)) (standardLeftMul (B := C)) x a y b) := by
  apply MulOpposite.unop_injective
  change star (entryMatrix 0 j (MulOpposite.unop a)) *
      (GradedMatrixMoritaMatrix.corner (MulOpposite.unop ⟪x, y⟫_(Cᵐᵒᵖ)) *
        entryMatrix 0 k (MulOpposite.unop b)) =
    entryMatrix j k (star (MulOpposite.unop a) *
      (MulOpposite.unop ⟪x, y⟫_(Cᵐᵒᵖ) * MulOpposite.unop b))
  ext r s
  fin_cases j <;> fin_cases k <;> fin_cases r <;> fin_cases s <;>
    simp [entryMatrix_apply, GradedMatrixMoritaMatrix.corner, CStarMatrix.ofMatrix_apply, CStarMatrix.star_apply,
      CStarMatrix.mul_apply, Fin.sum_univ_two]

/-- The whole balanced sesquilinear form, including both localities. -/
theorem balancedMap_cross_inner (j k : Fin 2)
    (u v : SourceBalanced (C := C) (H := H)) :
    (moduleTensorInner (E := H)) (GradedMatrixMoritaRow.leftAction (B := C)) ((balancedMap (C := C) (H := H)) j u) ((balancedMap (C := C) (H := H)) k v) =
      coefficientEntry j k ((moduleTensorInner (E := H)) (standardLeftMul (B := C)) u v) := by
  revert v
  refine moduleTensor_induction (E := H) (standardLeftMul (B := C)) u ?_ ?_ ?_
  · intro v
    simp
  · intro x a v
    refine moduleTensor_induction (E := H) (standardLeftMul (B := C)) v ?_ ?_ ?_
    · simp
    · intro y b
      simpa only [(balancedMap_mk (C := C) (H := H)), moduleTensorInner_mk_mk] using
        (pure_cross_inner (C := C) (H := H)) j k x y a b
    · intro v w hv hw
      simp only [map_add, hv, hw]
  · intro u w hu hw v
    simp only [map_add, LinearMap.add_apply, hu, hw]

variable [CompleteSpace H]

abbrev SourcePre := PreHilbertModuleTensor (E := H) (standardLeftMul (B := C))
abbrev TargetPre := PreHilbertModuleTensor (E := H) (GradedMatrixMoritaRow.leftAction (B := C))
abbrev SourceTensor := InteriorModuleTensor (E := H) (standardLeftMul (B := C))
abbrev TargetTensor := InteriorModuleTensor (E := H) (GradedMatrixMoritaRow.leftAction (B := C))

theorem balancedMap_null (j : Fin 2) :
    moduleTensorNull (E := H) (standardLeftMul (B := C)) ≤
      ((moduleTensorNull (E := H)) (GradedMatrixMoritaRow.leftAction (B := C))).comap ((balancedMap (C := C) (H := H)) j) := by
  intro u hu
  apply ((mem_moduleTensorNull_iff (E := H)) (GradedMatrixMoritaRow.leftAction (B := C)) ((balancedMap (C := C) (H := H)) j u)).mpr
  rw [(balancedMap_cross_inner (C := C) (H := H)), ((mem_moduleTensorNull_iff (E := H)) (standardLeftMul (B := C)) u).mp hu, map_zero]

/-- Descent through the two actual null quotients. -/
def preMap (j : Fin 2) : SourcePre (C := C) (H := H) →ₗ[ℂ] TargetPre (C := C) (H := H) :=
  ((moduleTensorNull (E := H)) (standardLeftMul (B := C))).mapQ ((moduleTensorNull (E := H)) (GradedMatrixMoritaRow.leftAction (B := C)))
    ((balancedMap (C := C) (H := H)) j) ((balancedMap_null (C := C) (H := H)) j)

theorem preMap_cross_inner (j k : Fin 2) (u v : SourcePre (C := C) (H := H)) :
    ⟪(preMap (C := C) (H := H)) j u, (preMap (C := C) (H := H)) k v⟫_((GradedMatrixMoritaMatrix C)ᵐᵒᵖ) =
      coefficientEntry j k ⟪u, v⟫_(Cᵐᵒᵖ) := by
  induction u using Submodule.Quotient.induction_on with
  | H u =>
    induction v using Submodule.Quotient.induction_on with
    | H v => exact (balancedMap_cross_inner (C := C) (H := H)) j k u v

def preIsometry (j : Fin 2) : SourcePre (C := C) (H := H) →ₗᵢ[ℂ] TargetPre (C := C) (H := H) where
  toLinearMap := (preMap (C := C) (H := H)) j
  norm_map' u := by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := (GradedMatrixMoritaMatrix C)ᵐᵒᵖ),
      (preMap_cross_inner (C := C) (H := H)), norm_coefficientEntry,
      ← CStarModule.norm_eq_sqrt_norm_inner_self (A := Cᵐᵒᵖ)]

/-- Completion in the genuine row Hilbert module, from the proved pre-isometry. -/
def completedCLM (j : Fin 2) : SourceTensor (C := C) (H := H) →L[ℂ] TargetTensor (C := C) (H := H) :=
  (((moduleTensorToCompletion (E := H)) (GradedMatrixMoritaRow.leftAction (B := C))).toContinuousLinearMap.comp
    ((preIsometry (C := C) (H := H)) j).toContinuousLinearMap).fromCompletion

@[simp] theorem completedCLM_coe (j : Fin 2) (u : SourcePre (C := C) (H := H)) :
    (completedCLM (C := C) (H := H)) j ((moduleTensorToCompletion (E := H)) (standardLeftMul (B := C)) u) =
      (moduleTensorToCompletion (E := H)) (GradedMatrixMoritaRow.leftAction (B := C)) ((preMap (C := C) (H := H)) j u) :=
  ContinuousLinearMap.fromCompletion_apply_coe _ u

theorem completedCLM_norm (j : Fin 2) (u : SourceTensor (C := C) (H := H)) :
    ‖(completedCLM (C := C) (H := H)) j u‖ = ‖u‖ := by
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih u =>
    change ‖(completedCLM (C := C) (H := H)) j ((moduleTensorToCompletion (E := H)) (standardLeftMul (B := C)) u)‖ =
      ‖(moduleTensorToCompletion (E := H)) (standardLeftMul (B := C)) u‖
    rw [(completedCLM_coe (C := C) (H := H)),
      (moduleTensorToCompletion (E := H) (GradedMatrixMoritaRow.leftAction (B := C))).norm_map]
    change ‖preIsometry (C := C) (H := H) j u‖ =
      ‖moduleTensorToCompletion (E := H) (standardLeftMul (B := C)) u‖
    rw [(preIsometry (C := C) (H := H) j).norm_map,
      (moduleTensorToCompletion (E := H) (standardLeftMul (B := C))).norm_map]

def completedIsometry (j : Fin 2) : SourceTensor (C := C) (H := H) →ₗᵢ[ℂ]
    TargetTensor (C := C) (H := H) where
  toLinearMap := ((completedCLM (C := C) (H := H)) j).toLinearMap
  norm_map' := (completedCLM_norm (C := C) (H := H)) j

@[simp] theorem completedIsometry_mk (j : Fin 2) (x : H) (a : Cᵐᵒᵖ) :
    (completedIsometry (C := C) (H := H)) j ((interiorModuleTensorMk (E := H)) (standardLeftMul (B := C)) x a) =
      (interiorModuleTensorMk (E := H)) (GradedMatrixMoritaRow.leftAction (B := C)) x (rowElement j a) :=
  (completedCLM_coe (C := C) (H := H)) j (preModuleTensorMk (standardLeftMul (B := C)) x a)

theorem completedIsometry_cross_inner (j k : Fin 2)
    (u v : SourceTensor (C := C) (H := H)) :
    ⟪(completedIsometry (C := C) (H := H)) j u, (completedIsometry (C := C) (H := H)) k v⟫_((GradedMatrixMoritaMatrix C)ᵐᵒᵖ) =
      coefficientEntry j k ⟪u, v⟫_(Cᵐᵒᵖ) := by
  induction u, v using UniformSpace.Completion.induction_on₂ with
  | hp =>
    apply isClosed_eq
    · exact (CStarModule.continuous_inner (A := (GradedMatrixMoritaMatrix C)ᵐᵒᵖ)
        (E := TargetTensor (C := C) (H := H))).comp
        ((((completedCLM (C := C) (H := H)) j).continuous.comp continuous_fst).prodMk
          (((completedCLM (C := C) (H := H)) k).continuous.comp continuous_snd))
    · exact (coefficientEntry j k).continuous.comp
        (CStarModule.continuous_inner (A := Cᵐᵒᵖ) (E := SourceTensor (C := C) (H := H)))
  | ih u v =>
    change ⟪(completedCLM (C := C) (H := H)) j ((moduleTensorToCompletion (E := H)) (standardLeftMul (B := C)) u),
      (completedCLM (C := C) (H := H)) k ((moduleTensorToCompletion (E := H)) (standardLeftMul (B := C)) v)⟫_
        ((GradedMatrixMoritaMatrix C)ᵐᵒᵖ) =
      coefficientEntry j k ⟪(moduleTensorToCompletion (E := H)) (standardLeftMul (B := C)) u,
        (moduleTensorToCompletion (E := H)) (standardLeftMul (B := C)) v⟫_(Cᵐᵒᵖ)
    rw [(completedCLM_coe (C := C) (H := H)), (completedCLM_coe (C := C) (H := H))]
    change ⟪hilbertModuleToCompletion (E := TargetPre (C := C) (H := H))
      (preMap (C := C) (H := H) j u),
      hilbertModuleToCompletion (E := TargetPre (C := C) (H := H))
        (preMap (C := C) (H := H) k v)⟫_((GradedMatrixMoritaMatrix C)ᵐᵒᵖ) =
      coefficientEntry j k ⟪hilbertModuleToCompletion (E := SourcePre (C := C) (H := H)) u,
        hilbertModuleToCompletion (E := SourcePre (C := C) (H := H)) v⟫_(Cᵐᵒᵖ)
    rw [hilbertModuleToCompletion_inner, hilbertModuleToCompletion_inner,
      (preMap_cross_inner (C := C) (H := H))]

/-- The genuine coordinate embedding of H, using the nonunital right tensor unit. -/
def coordinate (j : Fin 2) : H →ₗᵢ[ℂ] TargetTensor (C := C) (H := H) :=
  ((completedIsometry (C := C) (H := H)) j).comp
    (rightStandardInteriorModuleTensorHilbertEquiv (B := C) (E := H)).symm.linearIsometryEquiv.toLinearIsometry

@[simp] theorem coordinate_smul (j : Fin 2) (a : Cᵐᵒᵖ) (x : H) :
    (coordinate (C := C) (H := H)) j (a • x) = (interiorModuleTensorMk (E := H)) (GradedMatrixMoritaRow.leftAction (B := C)) x (rowElement j a) := by
  rw [← rightStandardInteriorModuleTensorHilbertEquiv_mk x a]
  change (completedIsometry (C := C) (H := H)) j ((rightStandardInteriorModuleTensorHilbertEquiv (B := C)
    (E := H)).symm (rightStandardInteriorModuleTensorHilbertEquiv
      ((interiorModuleTensorMk (E := H)) (standardLeftMul (B := C)) x a))) = _
  rw [HilbertModuleEquiv.symm_apply_apply, (completedIsometry_mk (C := C) (H := H))]

/-- Full matrix coefficient pairing, with no omitted off-diagonal terms. -/
theorem coordinate_inner (j k : Fin 2) (x y : H) :
    ⟪(coordinate (C := C) (H := H)) j x, (coordinate (C := C) (H := H)) k y⟫_((GradedMatrixMoritaMatrix C)ᵐᵒᵖ) =
      coefficientEntry j k ⟪x, y⟫_(Cᵐᵒᵖ) := by
  change ⟪(completedIsometry (C := C) (H := H)) j ((rightStandardInteriorModuleTensorHilbertEquiv (B := C)
    (E := H)).symm x), (completedIsometry (C := C) (H := H)) k ((rightStandardInteriorModuleTensorHilbertEquiv
      (B := C) (E := H)).symm y)⟫_((GradedMatrixMoritaMatrix C)ᵐᵒᵖ) = _
  rw [(completedIsometry_cross_inner (C := C) (H := H)), HilbertModuleEquiv.inner_map]

theorem coordinate_inner_matrix (j k : Fin 2) (x y : H) :
    MulOpposite.unop ⟪(coordinate (C := C) (H := H)) j x, (coordinate (C := C) (H := H)) k y⟫_((GradedMatrixMoritaMatrix C)ᵐᵒᵖ) =
      entryMatrix j k (MulOpposite.unop ⟪x, y⟫_(Cᵐᵒᵖ)) := by
  rw [(coordinate_inner (C := C) (H := H)), coefficientEntry_apply, MulOpposite.unop_op]

def coordinateSum : H × H →L[ℂ] TargetTensor (C := C) (H := H) :=
  ((coordinate (C := C) (H := H)) 0).toContinuousLinearMap.coprod ((coordinate (C := C) (H := H)) 1).toContinuousLinearMap

@[simp] theorem coordinateSum_apply (x : H × H) :
    (coordinateSum (C := C) (H := H)) x = (coordinate (C := C) (H := H)) 0 x.1 + (coordinate (C := C) (H := H)) 1 x.2 := rfl

/-- The complete matrix Gram form of the coordinate sum. -/
theorem coordinateSum_inner_matrix (x y : H × H) :
    MulOpposite.unop ⟪(coordinateSum (C := C) (H := H)) x, (coordinateSum (C := C) (H := H)) y⟫_((GradedMatrixMoritaMatrix C)ᵐᵒᵖ) =
      CStarMatrix.ofMatrix !![MulOpposite.unop ⟪x.1, y.1⟫_(Cᵐᵒᵖ),
        MulOpposite.unop ⟪x.1, y.2⟫_(Cᵐᵒᵖ);
        MulOpposite.unop ⟪x.2, y.1⟫_(Cᵐᵒᵖ), MulOpposite.unop ⟪x.2, y.2⟫_(Cᵐᵒᵖ)] := by
  rw [coordinateSum_apply (C := C) (H := H), coordinateSum_apply (C := C) (H := H),
    CStarModule.inner_add_left (A := (GradedMatrixMoritaMatrix C)ᵐᵒᵖ)
      (E := TargetTensor (C := C) (H := H)),
    CStarModule.inner_add_right (A := (GradedMatrixMoritaMatrix C)ᵐᵒᵖ)
      (E := TargetTensor (C := C) (H := H)),
    CStarModule.inner_add_right (A := (GradedMatrixMoritaMatrix C)ᵐᵒᵖ)
      (E := TargetTensor (C := C) (H := H))]
  simp only [MulOpposite.unop_add, coordinate_inner_matrix (C := C) (H := H)]
  ext r s
  fin_cases r <;> fin_cases s <;> simp [entryMatrix_apply, CStarMatrix.ofMatrix_apply]

theorem norm_le_coordinateSum (x : H × H) : ‖x‖ ≤ ‖(coordinateSum (C := C) (H := H)) x‖ := by
  have h0 : ‖x.1‖ ^ 2 ≤ ‖(coordinateSum (C := C) (H := H)) x‖ ^ 2 := by
    have he : (MulOpposite.unop ⟪(coordinateSum (C := C) (H := H)) x, (coordinateSum (C := C) (H := H)) x⟫_
        ((GradedMatrixMoritaMatrix C)ᵐᵒᵖ)) 0 0 = MulOpposite.unop ⟪x.1, x.1⟫_(Cᵐᵒᵖ) := by
      rw [(coordinateSum_inner_matrix (C := C) (H := H))]
      rfl
    have hb := CStarMatrix.norm_entry_le_norm
      (M := MulOpposite.unop ⟪(coordinateSum (C := C) (H := H)) x, (coordinateSum (C := C) (H := H)) x⟫_
        ((GradedMatrixMoritaMatrix C)ᵐᵒᵖ)) (i := 0) (j := 0)
    rw [he, MulOpposite.norm_unop, MulOpposite.norm_unop] at hb
    simpa only [CStarModule.norm_sq_eq Cᵐᵒᵖ,
      CStarModule.norm_sq_eq ((GradedMatrixMoritaMatrix C)ᵐᵒᵖ)] using hb
  have h1 : ‖x.2‖ ^ 2 ≤ ‖(coordinateSum (C := C) (H := H)) x‖ ^ 2 := by
    have he : (MulOpposite.unop ⟪(coordinateSum (C := C) (H := H)) x, (coordinateSum (C := C) (H := H)) x⟫_
        ((GradedMatrixMoritaMatrix C)ᵐᵒᵖ)) 1 1 = MulOpposite.unop ⟪x.2, x.2⟫_(Cᵐᵒᵖ) := by
      rw [(coordinateSum_inner_matrix (C := C) (H := H))]
      rfl
    have hb := CStarMatrix.norm_entry_le_norm
      (M := MulOpposite.unop ⟪(coordinateSum (C := C) (H := H)) x, (coordinateSum (C := C) (H := H)) x⟫_
        ((GradedMatrixMoritaMatrix C)ᵐᵒᵖ)) (i := 1) (j := 1)
    rw [he, MulOpposite.norm_unop, MulOpposite.norm_unop] at hb
    simpa only [CStarModule.norm_sq_eq Cᵐᵒᵖ,
      CStarModule.norm_sq_eq ((GradedMatrixMoritaMatrix C)ᵐᵒᵖ)] using hb
  rw [Prod.norm_def, max_le_iff]
  constructor <;> nlinarith [norm_nonneg x.1, norm_nonneg x.2, norm_nonneg ((coordinateSum (C := C) (H := H)) x)]

theorem coordinateSum_antilipschitz :
    AntilipschitzWith 1 (coordinateSum (C := C) (H := H)) :=
  AntilipschitzWith.of_le_mul_dist fun x y => by
    simpa only [dist_eq_norm, map_sub, NNReal.coe_one, one_mul] using (norm_le_coordinateSum (C := C) (H := H)) (x - y)

/-- Every actual elementary row tensor has both coordinates, even without a unit in C. -/
theorem pure_coordinate_decomposition (x : H) (r : GradedMatrixMoritaRow C) :
    (interiorModuleTensorMk (E := H)) (GradedMatrixMoritaRow.leftAction (B := C)) x r =
      (coordinateSum (C := C) (H := H)) (MulOpposite.op (GradedMatrixMoritaRow.matrix r 0 0) • x,
        MulOpposite.op (GradedMatrixMoritaRow.matrix r 0 1) • x) := by
  rw [(coordinateSum_apply (C := C) (H := H)), (coordinate_smul (C := C) (H := H)), (coordinate_smul (C := C) (H := H)),
    ← map_add, ← rowElement_decomposition]

theorem coordinateSum_surjective :
    Function.Surjective (coordinateSum (C := C) (H := H)) := by
  have hc : IsClosed ((coordinateSum (C := C) (H := H)).range : Set (TargetTensor (C := C) (H := H))) := by
    change IsClosed (Set.range (coordinateSum (C := C) (H := H)))
    exact (coordinateSum_antilipschitz (C := C) (H := H)).isClosed_range (coordinateSum (C := C) (H := H)).uniformContinuous
  have hs : Submodule.span ℂ
      (Set.range fun p : H × GradedMatrixMoritaRow C =>
        (interiorModuleTensorMk (E := H)) (GradedMatrixMoritaRow.leftAction (B := C)) p.1 p.2) ≤
        (coordinateSum (C := C) (H := H)).range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, r⟩, rfl⟩
    exact ⟨(MulOpposite.op (GradedMatrixMoritaRow.matrix r 0 0) • x,
      MulOpposite.op (GradedMatrixMoritaRow.matrix r 0 1) • x),
      ((pure_coordinate_decomposition (C := C) (H := H)) x r).symm⟩
  intro z
  exact (hc.closure_subset_iff.mpr hs)
    (((interiorModuleTensor_span_dense (E := H)) (GradedMatrixMoritaRow.leftAction (B := C))) z)

/-- The complex Banach-coordinate equivalence; its Hilbert form is the matrix Gram form above. -/
def coordinateEquiv : (H × H) ≃L[ℂ] TargetTensor (C := C) (H := H) :=
  ContinuousLinearEquiv.ofBijective (coordinateSum (C := C) (H := H))
    (LinearMap.ker_eq_bot.mpr (coordinateSum_antilipschitz (C := C) (H := H)).injective)
    (LinearMap.range_eq_top.mpr (coordinateSum_surjective (C := C) (H := H)))

@[simp] theorem coordinateEquiv_apply (x : H × H) :
    (coordinateEquiv (C := C) (H := H)) x = (coordinate (C := C) (H := H)) 0 x.1 + (coordinate (C := C) (H := H)) 1 x.2 := rfl

end Tensor
end BC4lean.KKTheory.MatrixHilbertModuleCoordinateEmbedding
