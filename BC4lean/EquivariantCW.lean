import BC4lean.ProperOrbitCells
import Mathlib.Topology.CWComplex.Abstract.Basic
import Mathlib.CategoryTheory.Action.Limits

/-! # Equivariant cell attachments

This module realizes the orbit boundary inclusions in `Action TopCat Γ`
and specializes Mathlib's relative cell complex structure to them. The cells
have finite isotropy. Properness of arbitrary cellular colimits and the
universal proper-space existence and mapping theorems are separate results;
they are not fields or axioms of the definitions below.
-/

open CategoryTheory CategoryTheory.Limits

namespace BC4lean.ProperActions

universe u v

/-- Bundle an action with continuous translations as an action in `TopCat`. -/
def topologicalAction (Γ : Type u) (X : Type v) [Group Γ] [TopologicalSpace X]
    [MulAction Γ X] [ContinuousConstSMul Γ X] : Action TopCat.{v} Γ where
  V := TopCat.of X
  ρ :=
    { toFun := fun g => TopCat.ofHom ⟨fun x => g • x, continuous_const_smul g⟩
      map_one' := by
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro x
        exact one_smul Γ x
      map_mul' := by
        intro g h
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro x
        exact mul_smul g h x }

namespace EquivariantMap

variable {Γ : Type u} {X Y Z : Type v} [Group Γ]
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable [MulAction Γ X] [MulAction Γ Y] [MulAction Γ Z]
variable [ContinuousConstSMul Γ X] [ContinuousConstSMul Γ Y] [ContinuousConstSMul Γ Z]

/-- A bundled continuous equivariant map gives a morphism of topological actions. -/
def toActionHom (f : EquivariantMap Γ X Y) :
    topologicalAction Γ X ⟶ topologicalAction Γ Y where
  hom := TopCat.ofHom f.toContinuousMap
  comm g := by ext x; exact f.map_smul g x

@[simp] theorem toActionHom_apply (f : EquivariantMap Γ X Y) (x : X) :
    f.toActionHom.hom x = f x := rfl

@[simp] theorem toActionHom_id :
    (id (Γ := Γ) (X := X)).toActionHom = 𝟙 (topologicalAction Γ X) := rfl

@[simp] theorem toActionHom_comp (g : EquivariantMap Γ Y Z) (f : EquivariantMap Γ X Y) :
    (g.comp f).toActionHom = f.toActionHom ≫ g.toActionHom := rfl

/-- Recover the pointwise equivariant-map API from a categorical morphism. -/
def ofActionHom (f : topologicalAction Γ X ⟶ topologicalAction Γ Y) :
    EquivariantMap Γ X Y where
  toContinuousMap := f.hom.hom
  map_smul' g x := congrArg (fun k : TopCat.of X ⟶ TopCat.of Y => k x) (f.comm g)

/-- The categorical and pointwise descriptions have exactly the same morphisms. -/
def actionHomEquiv :
    EquivariantMap Γ X Y ≃ (topologicalAction Γ X ⟶ topologicalAction Γ Y) where
  toFun := toActionHom
  invFun := ofActionHom
  left_inv f := by ext x; rfl
  right_inv f := by apply Action.Hom.ext; rfl

end EquivariantMap

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]

namespace OrbitCell

/-- Map the parameter of an orbit cell, leaving its coset coordinate unchanged. -/
def map {D E : Type v} [TopologicalSpace D] [TopologicalSpace E]
    (H : Subgroup Γ) (f : C(D, E)) : EquivariantMap Γ (OrbitCell H D) (OrbitCell H E) where
  toFun p := (p.1, f p.2)
  continuous_toFun := continuous_fst.prodMk (f.continuous.comp continuous_snd)
  map_smul' _ _ := rfl

omit [DiscreteTopology Γ] in
@[simp] theorem map_apply {D E : Type v} [TopologicalSpace D] [TopologicalSpace E]
    (H : Subgroup Γ) (f : C(D, E)) (p : OrbitCell H D) :
    map H f p = (p.1, f p.2) := rfl

/-- The orbit boundary inclusion Γ/H × ∂Dⁿ → Γ/H × Dⁿ. -/
noncomputable def boundaryInclusion (H : Subgroup Γ) (n : ℕ) :
    EquivariantMap Γ (OrbitCell H (TopCat.diskBoundary.{u} n))
      (OrbitCell H (TopCat.disk.{u} n)) :=
  map H (TopCat.diskBoundaryInclusion n).hom

omit [DiscreteTopology Γ] in
/-- Orbit boundary inclusions are injective, including in dimension zero. -/
theorem boundaryInclusion_injective (H : Subgroup Γ) (n : ℕ) :
    Function.Injective (boundaryInclusion H n) := by
  intro x y h
  change (x.1, (TopCat.diskBoundaryInclusion n) x.2) =
    (y.1, (TopCat.diskBoundaryInclusion n) y.2) at h
  apply Prod.ext
  · exact congrArg (fun p : (Γ ⧸ H) × TopCat.disk.{u} n => p.1) h
  · exact (TopCat.mono_iff_injective (TopCat.diskBoundaryInclusion n)).mp
      inferInstance (congrArg Prod.snd h)

/-- The disk orbit cell with finite isotropy is topologically proper. -/
theorem disk_proper (H : Subgroup Γ) [Finite H] (n : ℕ) :
    ProperSMul Γ (OrbitCell H (TopCat.disk.{u} n)) := by
  let : T2Space (TopCat.disk.{u} n) := by
    change T2Space (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
    exact Homeomorph.ulift.{u, 0}.symm.t2Space
  exact proper H _

/-- The boundary orbit cell with finite isotropy is topologically proper. -/
theorem boundary_proper (H : Subgroup Γ) [Finite H] (n : ℕ) :
    ProperSMul Γ (OrbitCell H (TopCat.diskBoundary.{u} n)) := by
  let : T2Space (TopCat.diskBoundary.{u} n) := by
    change T2Space (ULift (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))
    exact Homeomorph.ulift.{u, 0}.symm.t2Space
  exact proper H _

end OrbitCell

/-- Finite isotropy subgroups indexing the allowed orbit cells. -/
def FiniteIsotropy (Γ : Type u) [Group Γ] := {H : Subgroup Γ // Finite H}

/-- Generating boundary maps, with dimension indexed by the skeletal stage. -/
noncomputable def equivariantBasicCell (n : ℕ) (H : FiniteIsotropy Γ) :
    topologicalAction Γ (OrbitCell H.val (TopCat.diskBoundary.{u} n)) ⟶
      topologicalAction Γ (OrbitCell H.val (TopCat.disk.{u} n)) :=
  (OrbitCell.boundaryInclusion H.val n).toActionHom

/-- Relative equivariant CW data, attaching n-dimensional finite-isotropy orbit
cells at stage n. This definition includes actual pushout and colimit witnesses. -/
abbrev RelativeEquivariantCWComplex {X Y : Action TopCat.{u} Γ} (f : X ⟶ Y) :=
  HomotopicalAlgebra.RelativeCellComplex.{u} (equivariantBasicCell (Γ := Γ)) f

/-- An equivariant CW structure starting from the empty action. Finite isotropy
is imposed on the cell family, not assumed as a properness conclusion. -/
abbrev EquivariantCWComplex (X : Action TopCat.{u} Γ) :=
  RelativeEquivariantCWComplex (initial.to X)

/-- Relative equivariant CW structures include an attachment at every finite stage. -/
def RelativeEquivariantCWComplex.attachment {X Y : Action TopCat.{u} Γ} {f : X ⟶ Y}
    (c : RelativeEquivariantCWComplex f) (n : ℕ) :=
  c.attachCells n (not_isMax n)

/-- Maps out of a cellular object are determined on the initial subspace and cells. -/
theorem RelativeEquivariantCWComplex.hom_ext
    {X Y Z : Action TopCat.{u} Γ} {f : X ⟶ Y}
    (c : RelativeEquivariantCWComplex f) {φ ψ : Y ⟶ Z}
    (h₀ : f ≫ φ = f ≫ ψ)
    (h : ∀ γ : HomotopicalAlgebra.RelativeCellComplex.Cells c, γ.ι ≫ φ = γ.ι ≫ ψ) :
    φ = ψ :=
  HomotopicalAlgebra.RelativeCellComplex.hom_ext c h₀ h

end BC4lean.ProperActions
