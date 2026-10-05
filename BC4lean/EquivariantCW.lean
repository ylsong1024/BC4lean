import BC4lean.ProperOrbitCells
import Mathlib.Topology.CWComplex.Abstract.Basic
import Mathlib.CategoryTheory.Action.Limits
import Mathlib.CategoryTheory.Types.Monomorphisms
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

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


/-- Forget both topology and action, retaining the underlying set. -/
abbrev underlyingAction : Action TopCat.{u} Γ ⥤ Type u :=
  Action.forget TopCat Γ ⋙ forget TopCat

private instance : PreservesWellOrderContinuousOfShape ℕ (underlyingAction (Γ := Γ)) where

private noncomputable def underlyingAttachment
    {α : Type u} {A B : α → Action TopCat.{u} Γ}
    {g : ∀ a, A a ⟶ B a} {X Y : Action TopCat.{u} Γ} {f : X ⟶ Y}
    (c : HomotopicalAlgebra.AttachCells.{u} g f) :
    HomotopicalAlgebra.AttachCells.{u}
      (fun a => (underlyingAction (Γ := Γ)).map (g a))
      ((underlyingAction (Γ := Γ)).map f) where
  ι := c.ι
  π := c.π
  cofan₁ := Cofan.mk _ (fun i => (underlyingAction (Γ := Γ)).map (c.cofan₁.inj i))
  cofan₂ := Cofan.mk _ (fun i => (underlyingAction (Γ := Γ)).map (c.cofan₂.inj i))
  isColimit₁ := isColimitCofanMkObjOfIsColimit _ _ _ c.isColimit₁
  isColimit₂ := isColimitCofanMkObjOfIsColimit _ _ _ c.isColimit₂
  m := (underlyingAction (Γ := Γ)).map c.m
  hm i := by simpa only [Functor.map_comp, cofan_mk_inj] using congrArg ((underlyingAction (Γ := Γ)).map) (c.hm i)
  g₁ := (underlyingAction (Γ := Γ)).map c.g₁
  g₂ := (underlyingAction (Γ := Γ)).map c.g₂
  isPushout := c.isPushout.map _

/-- A finite-isotropy orbit-cell attachment never identifies pre-existing points. -/
theorem orbitCellAttachment_injective
    {A B : Action TopCat.{u} Γ} {i : A ⟶ B} {n : ℕ}
    (c : HomotopicalAlgebra.AttachCells.{u} (equivariantBasicCell (Γ := Γ) n) i) :
    Function.Injective i.hom := by
  let a := underlyingAttachment c
  have hc : (MorphismProperty.monomorphisms (Type u)).coproducts.pushouts
      ((underlyingAction (Γ := Γ)).map i) := by
    apply MorphismProperty.pushouts_monotone
      (MorphismProperty.coproducts_monotone (b := MorphismProperty.monomorphisms (Type u)) ?_)
      _ a.pushouts_coproducts
    intro X Y f hf
    cases hf with
    | mk H =>
      exact (CategoryTheory.mono_iff_injective _).mpr
        (OrbitCell.boundaryInclusion_injective H.val n)
  have hp : (MorphismProperty.monomorphisms (Type u)).coproducts.pushouts ≤
      (MorphismProperty.monomorphisms (Type u)).pushouts :=
    MorphismProperty.pushouts_monotone (MorphismProperty.monomorphisms (Type u)).coproducts_le
  exact (CategoryTheory.mono_iff_injective _).mp
    (MorphismProperty.pushouts_le _ (hp _ hc))

private noncomputable def underlyingCellularSequence
    {A B : Action TopCat.{u} Γ} {i : A ⟶ B}
    (c : RelativeEquivariantCWComplex i) :
    (MorphismProperty.monomorphisms (Type u)).TransfiniteCompositionOfShape ℕ
      ((underlyingAction (Γ := Γ)).map i) where
  toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape.map underlyingAction
  map_mem n _ := (CategoryTheory.mono_iff_injective _).mpr
    (orbitCellAttachment_injective (c.attachment n))

/-- The inclusion underlying any relative equivariant CW structure is injective. -/
theorem RelativeEquivariantCWComplex.injective
    {A B : Action TopCat.{u} Γ} {i : A ⟶ B}
    (c : RelativeEquivariantCWComplex i) : Function.Injective i.hom := by
  exact (CategoryTheory.mono_iff_injective _).mp
    ((MorphismProperty.monomorphisms (Type u)).transfiniteCompositionsOfShape_le ℕ _
      (underlyingCellularSequence c).mem)

/-- Every skeletal transition is injective, including non-adjacent stages. -/
theorem RelativeEquivariantCWComplex.skeletonMap_injective
    {A B : Action TopCat.{u} Γ} {i : A ⟶ B}
    (c : RelativeEquivariantCWComplex i) {m n : ℕ} (h : m ≤ n) :
    Function.Injective (c.F.map (homOfLE h)).hom := by
  exact (CategoryTheory.mono_iff_injective _).mp
    ((underlyingCellularSequence c).mem_map (homOfLE h))

/-- No points in a skeleton become identified in the final CW colimit. -/
theorem RelativeEquivariantCWComplex.skeletonInclusion_injective
    {A B : Action TopCat.{u} Γ} {i : A ⟶ B}
    (c : RelativeEquivariantCWComplex i) (n : ℕ) :
    Function.Injective (c.incl.app n).hom := by
  exact (CategoryTheory.mono_iff_injective _).mp
    ((underlyingCellularSequence c).mem_incl_app n)

omit [DiscreteTopology Γ] in
/-- Orbit-cell boundaries are closed subspaces of the disks, even for infinite Γ/H. -/
theorem OrbitCell.boundaryInclusion_isClosedEmbedding (H : Subgroup Γ) (n : ℕ) :
    Topology.IsClosedEmbedding (boundaryInclusion H n) := by
  let : T2Space (TopCat.disk.{u} n) := by
    change T2Space (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
    exact Homeomorph.ulift.{u, 0}.symm.t2Space
  have hd : Topology.IsClosedEmbedding (TopCat.diskBoundaryInclusion.{u} n) :=
    (TopCat.diskBoundaryInclusion n).hom.continuous.isClosedEmbedding
      ((TopCat.mono_iff_injective _).mp inferInstance)
  exact Topology.IsClosedEmbedding.id.prodMap hd

/-- Every point of a relative CW colimit comes from a finite skeletal stage. -/
theorem RelativeEquivariantCWComplex.exists_skeleton_preimage
    {A B : Action TopCat.{u} Γ} {i : A ⟶ B}
    (c : RelativeEquivariantCWComplex i) (x : B.V) :
    ∃ (n : ℕ) (y : (c.F.obj n).V), (c.incl.app n).hom y = x := by
  exact Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (underlyingAction (Γ := Γ)) c.isColimit) x

/-- The CW colimit topology detects open sets on all finite skeleta. -/
theorem RelativeEquivariantCWComplex.isOpen_iff
    {A B : Action TopCat.{u} Γ} {i : A ⟶ B}
    (c : RelativeEquivariantCWComplex i) (s : Set B.V) :
    IsOpen s ↔ ∀ n : ℕ, IsOpen ((c.incl.app n).hom ⁻¹' s) := by
  exact TopCat.isOpen_iff_of_isColimit _
    (isColimitOfPreserves (Action.forget TopCat Γ) c.isColimit) s

/-- The CW colimit topology detects closed sets on all finite skeleta. -/
theorem RelativeEquivariantCWComplex.isClosed_iff
    {A B : Action TopCat.{u} Γ} {i : A ⟶ B}
    (c : RelativeEquivariantCWComplex i) (s : Set B.V) :
    IsClosed s ↔ ∀ n : ℕ, IsClosed ((c.incl.app n).hom ⁻¹' s) := by
  exact TopCat.isClosed_iff_of_isColimit _
    (isColimitOfPreserves (Action.forget TopCat Γ) c.isColimit) s

/-- Continuity out of a relative CW colimit is tested on its finite skeleta. -/
theorem RelativeEquivariantCWComplex.continuous_iff
    {A B : Action TopCat.{u} Γ} {i : A ⟶ B}
    (c : RelativeEquivariantCWComplex i) {Z : Type v} [TopologicalSpace Z] (f : B.V → Z) :
    Continuous f ↔ ∀ n : ℕ, Continuous (f ∘ (c.incl.app n).hom) := by
  exact TopCat.continuous_iff_of_isColimit _
    (isColimitOfPreserves (Action.forget TopCat Γ) c.isColimit) f

end BC4lean.ProperActions

universe u

namespace BC4lean.ProperActions

/-- Closed embeddings are preserved by topological pushout. -/
theorem pushout_isClosedEmbedding
    {A B X Y : TopCat.{u}} {a : A ⟶ X} {m : A ⟶ B} {f : X ⟶ Y} {g : B ⟶ Y}
    (sq : IsPushout a m f g) (hm : Topology.IsClosedEmbedding m) :
    Topology.IsClosedEmbedding f := by
  have sqt := sq.flip.map (forget TopCat)
  have hinj : Function.Injective f := by
    let : Mono ((forget TopCat).map m) := (mono_iff_injective _).mpr hm.injective
    exact (mono_iff_injective _).mp
      (Types.pushoutCocone_inr_mono_of_isColimit sqt.isColimit)
  refine .of_continuous_injective_isClosedMap f.hom.continuous hinj ?_
  intro s hs
  have he : g ⁻¹' (f '' s) = m '' (a ⁻¹' s) := by
    ext b
    constructor
    · rintro ⟨x, hx, hxb⟩
      obtain ⟨z, hzb, hzx⟩ :=
        (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit sqt.isColimit hm.injective b x).mp hxb.symm
      change a z = x at hzx
      exact ⟨z, by change a z ∈ s; rw [hzx]; exact hx, hzb⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨a z, hz, ConcreteCategory.congr_hom sq.w z⟩
  apply (TopCat.isClosed_iff_of_isColimit _ sq.isColimit (f '' s)).mpr
  intro j
  rcases j with _ | (_ | _)
  · change IsClosed ((a ≫ f) ⁻¹' (f '' s))
    simpa only [TopCat.coe_comp, Set.preimage_comp, hinj.preimage_image] using
      hs.preimage a.hom.continuous
  · change IsClosed (f ⁻¹' (f '' s))
    simpa only [hinj.preimage_image] using hs
  · change IsClosed (g ⁻¹' (f '' s))
    rw [he]
    exact hm.isClosedMap _ (hs.preimage a.hom.continuous)

end BC4lean.ProperActions

namespace BC4lean.ProperActions

/-- A coproduct of closed embeddings is a closed embedding. -/
theorem coproduct_isClosedEmbedding
    {ι : Type u} {A B : ι → TopCat.{u}} {c₁ : Cofan A} {c₂ : Cofan B}
    (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂)
    (f : ∀ j, A j ⟶ B j) (hf : ∀ j, Topology.IsClosedEmbedding (f j))
    (m : c₁.pt ⟶ c₂.pt) (hm : ∀ j, c₁.inj j ≫ m = f j ≫ c₂.inj j) :
    Topology.IsClosedEmbedding m := by
  let d₁ : Cofan (fun j => (forget TopCat).obj (A j)) :=
    Cofan.mk _ (fun j => (forget TopCat).map (c₁.inj j))
  let d₂ : Cofan (fun j => (forget TopCat).obj (B j)) :=
    Cofan.mk _ (fun j => (forget TopCat).map (c₂.inj j))
  have hd₁ : IsColimit d₁ := isColimitCofanMkObjOfIsColimit _ _ _ hc₁
  have hd₂ : IsColimit d₂ := isColimitCofanMkObjOfIsColimit _ _ _ hc₂
  have hm' (j : ι) (x : A j) : m (c₁.inj j x) = c₂.inj j (f j x) :=
    ConcreteCategory.congr_hom (hm j) x
  have hinj : Function.Injective m := by
    intro x y hxy
    obtain ⟨j, z, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit hd₁ x
    obtain ⟨k, w, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit hd₁ y
    change m (c₁.inj j z) = m (c₁.inj k w) at hxy
    rw [hm', hm'] at hxy
    obtain rfl := Cofan.eq_of_inj_apply_eq_of_isColimit hd₂ _ _ hxy
    have h := Cofan.inj_injective_of_isColimit hd₂ j hxy
    exact congrArg (c₁.inj j) ((hf j).injective h)
  refine .of_continuous_injective_isClosedMap m.hom.continuous hinj ?_
  intro s hs
  apply (TopCat.isClosed_iff_of_isColimit _ hc₂ (m '' s)).mpr
  rintro ⟨j⟩
  have he : c₂.inj j ⁻¹' (m '' s) = f j '' (c₁.inj j ⁻¹' s) := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      obtain ⟨k, z, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit hd₁ x
      change m (c₁.inj k z) = c₂.inj j y at hxy
      rw [hm'] at hxy
      obtain rfl := Cofan.eq_of_inj_apply_eq_of_isColimit hd₂ _ _ hxy
      exact ⟨z, hx, Cofan.inj_injective_of_isColimit hd₂ k hxy⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨c₁.inj j x, hx, hm' j x⟩
  change IsClosed (c₂.inj j ⁻¹' (m '' s))
  rw [he]
  exact (hf j).isClosedMap _ (hs.preimage (c₁.inj j).hom.continuous)

end BC4lean.ProperActions

namespace BC4lean.ProperActions
variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]

/-- An orbit-cell attachment includes the previous stage as a closed subspace. -/
theorem orbitCellAttachment_isClosedEmbedding
    {A B : Action TopCat.{u} Γ} {i : A ⟶ B} {n : ℕ}
    (c : HomotopicalAlgebra.AttachCells.{u} (equivariantBasicCell (Γ := Γ) n) i) :
    Topology.IsClosedEmbedding i.hom := by
  apply pushout_isClosedEmbedding (c.isPushout.map (Action.forget TopCat Γ))
  let d₁ : Cofan (fun j => (topologicalAction Γ
      (OrbitCell (c.π j).val (TopCat.diskBoundary.{u} n))).V) :=
    Cofan.mk c.cofan₁.pt.V (fun j => (c.cofan₁.inj j).hom)
  let d₂ : Cofan (fun j => (topologicalAction Γ
      (OrbitCell (c.π j).val (TopCat.disk.{u} n))).V) :=
    Cofan.mk c.cofan₂.pt.V (fun j => (c.cofan₂.inj j).hom)
  have hd₁ : IsColimit d₁ := isColimitCofanMkObjOfIsColimit (Action.forget TopCat Γ) _ _ c.isColimit₁
  have hd₂ : IsColimit d₂ := isColimitCofanMkObjOfIsColimit (Action.forget TopCat Γ) _ _ c.isColimit₂
  apply coproduct_isClosedEmbedding hd₁ hd₂
    (fun j => (equivariantBasicCell n (c.π j)).hom)
    (fun j => OrbitCell.boundaryInclusion_isClosedEmbedding (c.π j).val n) c.m.hom
  intro j
  simpa only [d₁, d₂, cofan_mk_inj, Action.comp_hom] using congrArg Action.Hom.hom (c.hm j)

set_option backward.isDefEq.respectTransparency false in
/-- All finite skeletal transitions are closed embeddings. -/
theorem RelativeEquivariantCWComplex.skeletonMap_isClosedEmbedding
    {A B : Action TopCat.{u} Γ} {i : A ⟶ B}
    (c : RelativeEquivariantCWComplex i) {m n : ℕ} (h : m ≤ n) :
    Topology.IsClosedEmbedding (c.F.map (homOfLE h)).hom := by
  induction n, h using Nat.le_induction with
  | base => simpa using (Topology.IsClosedEmbedding.id (X := (c.F.obj m).V))
  | succ n h ih =>
    have hn : Topology.IsClosedEmbedding (c.F.map (homOfLE (Nat.le_succ n))).hom := by
      exact orbitCellAttachment_isClosedEmbedding (c.attachment n)
    have he := hn.comp ih
    have heq : (c.F.map (homOfLE (Nat.le_succ n))).hom ∘
        (c.F.map (homOfLE h)).hom =
        (c.F.map (homOfLE (Nat.le.step h))).hom := by
      funext x
      exact (ConcreteCategory.congr_hom
        (congrArg Action.Hom.hom (c.F.map_comp (homOfLE h) (homOfLE (Nat.le_succ n)))) x).symm
    rw [heq] at he
    exact he

/-- Each finite skeleton embeds as a closed subspace of the final CW colimit. -/
theorem RelativeEquivariantCWComplex.skeletonInclusion_isClosedEmbedding
    {A B : Action TopCat.{u} Γ} {i : A ⟶ B}
    (c : RelativeEquivariantCWComplex i) (n : ℕ) :
    Topology.IsClosedEmbedding (c.incl.app n).hom := by
  have hn := c.skeletonInclusion_injective n
  refine .of_continuous_injective_isClosedMap (c.incl.app n).hom.hom.continuous hn ?_
  intro s hs
  apply (c.isClosed_iff _).mpr
  intro m
  have hnat {j k : ℕ} (h : j ≤ k) (x : (c.F.obj j).V) :
      (c.incl.app k).hom ((c.F.map (homOfLE h)).hom x) = (c.incl.app j).hom x := by
    exact ConcreteCategory.congr_hom (congrArg Action.Hom.hom (c.incl.naturality (homOfLE h))) x
  rcases le_total m n with h | h
  · have he : (c.incl.app m).hom ⁻¹' ((c.incl.app n).hom '' s) =
        (c.F.map (homOfLE h)).hom ⁻¹' s := by
      ext x
      constructor
      · rintro ⟨y, hy, hxy⟩
        have heq := hn (hxy.trans (hnat h x).symm)
        change (c.F.map (homOfLE h)).hom x ∈ s
        rw [← heq]
        exact hy
      · intro hx
        exact ⟨_, hx, hnat h x⟩
    rw [he]
    exact hs.preimage (c.F.map (homOfLE h)).hom.hom.continuous
  · have he : (c.incl.app m).hom ⁻¹' ((c.incl.app n).hom '' s) =
        (c.F.map (homOfLE h)).hom '' s := by
      ext x
      constructor
      · rintro ⟨y, hy, hxy⟩
        exact ⟨y, hy, (c.skeletonInclusion_injective m) ((hnat h y).trans hxy)⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, (hnat h y).symm⟩
    rw [he]
    exact (c.skeletonMap_isClosedEmbedding h).isClosedMap s hs


/-- The initial subspace of a relative equivariant CW complex is closed embedded. -/
theorem RelativeEquivariantCWComplex.isClosedEmbedding
    {A B : Action TopCat.{u} Γ} {i : A ⟶ B}
    (c : RelativeEquivariantCWComplex i) : Topology.IsClosedEmbedding i.hom := by
  have h := (c.skeletonInclusion_isClosedEmbedding 0).comp
    (TopCat.homeoOfIso ((Action.forget TopCat Γ).mapIso c.isoBot.symm)).isClosedEmbedding
  change Topology.IsClosedEmbedding ((c.incl.app 0).hom ∘ c.isoBot.inv.hom) at h
  have hf := congrArg Action.Hom.hom c.fac
  change c.isoBot.inv.hom ≫ (c.incl.app 0).hom = i.hom at hf
  change Topology.IsClosedEmbedding (c.isoBot.inv.hom ≫ (c.incl.app 0).hom) at h
  rwa [hf] at h

end BC4lean.ProperActions

open CategoryTheory CategoryTheory.Limits
open scoped Topology
universe v
namespace BC4lean.ProperActions

/-- Continuous real functions separate distinct points. -/
def RealSeparatesPoints (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ x y : X, x ≠ y → ∃ f : C(X, ℝ), f x ≠ f y

theorem RealSeparatesPoints.t2Space {X : Type*} [TopologicalSpace X]
    (h : RealSeparatesPoints X) : T2Space X := by
  constructor
  intro x y hxy
  obtain ⟨f, hf⟩ := h x y hxy
  exact separated_by_continuous f.continuous hf

/-- Normality of a disjoint union follows componentwise. -/
theorem normalSpace_sigma {ι : Type*} {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, NormalSpace (X i)] : NormalSpace (Σ i, X i) := by
  classical
  constructor
  intro s t hs ht hd
  have hi (i : ι) := normal_separation
    (hs.preimage (continuous_sigmaMk (i := i)))
    (ht.preimage (continuous_sigmaMk (i := i))) (hd.preimage (Sigma.mk i))
  choose U V hU hV hsU htV hUV using hi
  refine ⟨{x | x.2 ∈ U x.1}, {x | x.2 ∈ V x.1}, ?_, ?_, ?_, ?_, ?_⟩
  · exact isOpen_sigma_iff.mpr hU
  · exact isOpen_sigma_iff.mpr hV
  · rintro ⟨i,x⟩ hx; exact hsU i hx
  · rintro ⟨i,x⟩ hx; exact htV i hx
  · exact Set.disjoint_left.mpr (fun ⟨i,x⟩ hx hy => Set.disjoint_left.mp (hUV i) hx hy)

set_option backward.isDefEq.respectTransparency false in
/-- A discrete family of copies of a normal space is normal. -/
theorem normalSpace_discrete_prod {D X : Type*} [TopologicalSpace D] [DiscreteTopology D]
    [TopologicalSpace X] [NormalSpace X] : NormalSpace (D × X) := by
  let e : (Σ _ : D, X) ≃ₜ D × X :=
    { toFun := fun p => (p.1,p.2)
      invFun := fun p => ⟨p.1,p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_sigma (fun _ => continuous_const.prodMk continuous_id)
      continuous_invFun := by
        apply continuous_prod_of_discrete_left.mpr
        intro d
        change Continuous (fun x : X => (⟨d,x⟩ : Σ _ : D, X))
        exact @continuous_sigmaMk D (fun _ : D => X) (fun _ => inferInstance) d }
  let := normalSpace_sigma (X := fun _ : D => X)
  exact e.normalSpace

/-- Glue real-valued functions across a topological pushout. -/
theorem pushout_glue_real
    {A B X Y : TopCat.{u}} {a : A ⟶ X} {m : A ⟶ B} {f : X ⟶ Y} {g : B ⟶ Y}
    (sq : IsPushout a m f g) (p : C(X, ℝ)) (q : C(B, ℝ))
    (h : ∀ z, p (a z) = q (m z)) :
    ∃ F : C(Y, ℝ), (∀ x, F (f x) = p x) ∧ ∀ b, F (g b) = q b := by
  let P : X ⟶ TopCat.of (ULift.{u} ℝ) := TopCat.ofHom ⟨fun x => ⟨p x⟩, continuous_uliftUp.comp p.continuous⟩
  let Q : B ⟶ TopCat.of (ULift.{u} ℝ) := TopCat.ofHom ⟨fun x => ⟨q x⟩, continuous_uliftUp.comp q.continuous⟩
  have hh : a ≫ P = m ≫ Q := by ext x; exact h x
  let F := sq.desc P Q hh
  refine ⟨⟨fun y => (F y).down, continuous_uliftDown.comp F.hom.continuous⟩, ?_, ?_⟩
  · intro x
    exact congrArg ULift.down (ConcreteCategory.congr_hom (sq.inl_desc P Q hh) x)
  · intro x
    exact congrArg ULift.down (ConcreteCategory.congr_hom (sq.inr_desc P Q hh) x)

/-- A real-valued function extends across attachment along a closed embedding into a normal space. -/
theorem pushout_extend_real
    {A B X Y : TopCat.{u}} [NormalSpace B]
    {a : A ⟶ X} {m : A ⟶ B} {f : X ⟶ Y} {g : B ⟶ Y}
    (sq : IsPushout a m f g) (hm : Topology.IsClosedEmbedding m) (p : C(X, ℝ)) :
    ∃ F : C(Y, ℝ), ∀ x, F (f x) = p x := by
  obtain ⟨q, hq⟩ := (p.comp a.hom).exists_extension' hm
  obtain ⟨F, hF, _⟩ := pushout_glue_real sq p q (fun z => (congrFun hq z).symm)
  exact ⟨F, hF⟩

/-- Normal attached spaces preserve separation by real-valued functions. -/
theorem pushout_realSeparatesPoints
    {A B X Y : TopCat.{u}} [NormalSpace B] [T1Space B]
    {a : A ⟶ X} {m : A ⟶ B} {f : X ⟶ Y} {g : B ⟶ Y}
    (sq : IsPushout a m f g) (hm : Topology.IsClosedEmbedding m)
    (hX : RealSeparatesPoints X) : RealSeparatesPoints Y := by
  intro x y hxy
  have repr : ∀ z : Y, (∃ w : X, f w = z) ∨ ∃ b : B, g b = z ∧ b ∉ Set.range m :=
    Types.eq_or_eq_of_isPushout' (sq.map (forget TopCat))
  have new_sep (b : B) (hb : b ∉ Set.range m) (z : Y) (hbz : g b ≠ z) :
      ∃ F : C(Y, ℝ), F (g b) ≠ F z := by
    obtain ⟨w, rfl⟩ | ⟨b', rfl, _⟩ := repr z
    · obtain ⟨q, hq0, hq1, _⟩ := exists_continuous_zero_one_of_isClosed
        hm.isClosed_range (isClosed_singleton (x := b)) (Set.disjoint_singleton_right.mpr hb)
      obtain ⟨F, hF, hG⟩ := pushout_glue_real sq (ContinuousMap.const _ 0) q
        (fun t => (hq0 ⟨t, rfl⟩).symm)
      refine ⟨F, ?_⟩
      rw [hG, hF, hq1 (Set.mem_singleton b)]
      norm_num
    · have hbb : b ≠ b' := fun h => hbz (congrArg g h)
      have hd : Disjoint (Set.range m ∪ {b'}) {b} := by
        apply Set.disjoint_singleton_right.mpr
        simpa only [Set.mem_union, Set.mem_singleton_iff, not_or] using And.intro hb hbb
      obtain ⟨q, hq0, hq1, _⟩ := exists_continuous_zero_one_of_isClosed
        (hm.isClosed_range.union isClosed_singleton) isClosed_singleton hd
      obtain ⟨F, _, hG⟩ := pushout_glue_real sq (ContinuousMap.const _ 0) q
        (fun t => (hq0 (Or.inl ⟨t, rfl⟩)).symm)
      refine ⟨F, ?_⟩
      rw [hG, hG, hq1 (Set.mem_singleton b), hq0 (Or.inr (Set.mem_singleton b'))]
      norm_num
  obtain ⟨x', rfl⟩ | ⟨b, rfl, hb⟩ := repr x
  · obtain ⟨y', rfl⟩ | ⟨b, rfl, hb⟩ := repr y
    · obtain ⟨p, hp⟩ := hX x' y' (fun h => hxy (congrArg f h))
      obtain ⟨F, hF⟩ := pushout_extend_real sq hm p
      exact ⟨F, by simpa only [hF] using hp⟩
    · obtain ⟨F, hF⟩ := new_sep b hb _ (Ne.symm hxy)
      exact ⟨F, Ne.symm hF⟩
  · exact new_sep b hb y hxy

end BC4lean.ProperActions

namespace BC4lean.ProperActions

private theorem cofan_normal {ι : Type u} {A : ι → TopCat.{u}}
    (c : Cofan A) (hc : IsColimit c) [∀ j, NormalSpace (A j)] : NormalSpace c.pt := by
  let : NormalSpace (TopCat.sigmaCofan A).pt := by
    change NormalSpace (Σ j, A j)
    exact normalSpace_sigma
  exact (TopCat.homeoOfIso (hc.coconePointUniqueUpToIso (TopCat.sigmaCofanIsColimit A))).symm.normalSpace

private theorem cofan_t2 {ι : Type u} {A : ι → TopCat.{u}}
    (c : Cofan A) (hc : IsColimit c) [∀ j, T2Space (A j)] : T2Space c.pt := by
  let : T2Space (TopCat.sigmaCofan A).pt := by
    change T2Space (Σ j, A j)
    infer_instance
  exact (TopCat.homeoOfIso (hc.coconePointUniqueUpToIso (TopCat.sigmaCofanIsColimit A))).symm.t2Space

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]

private theorem orbitAttachment_topology
    {A B : Action TopCat.{u} Γ} {i : A ⟶ B} {n : ℕ}
    (c : HomotopicalAlgebra.AttachCells.{u} (equivariantBasicCell (Γ := Γ) n) i) :
    Topology.IsClosedEmbedding c.m.hom ∧ NormalSpace c.cofan₂.pt.V ∧ T2Space c.cofan₂.pt.V := by
  let d₁ : Cofan (fun j => (topologicalAction Γ
      (OrbitCell (c.π j).val (TopCat.diskBoundary.{u} n))).V) :=
    Cofan.mk c.cofan₁.pt.V (fun j => (c.cofan₁.inj j).hom)
  let d₂ : Cofan (fun j => (topologicalAction Γ
      (OrbitCell (c.π j).val (TopCat.disk.{u} n))).V) :=
    Cofan.mk c.cofan₂.pt.V (fun j => (c.cofan₂.inj j).hom)
  have hd₁ : IsColimit d₁ := isColimitCofanMkObjOfIsColimit (Action.forget TopCat Γ) _ _ c.isColimit₁
  have hd₂ : IsColimit d₂ := isColimitCofanMkObjOfIsColimit (Action.forget TopCat Γ) _ _ c.isColimit₂
  have hm : Topology.IsClosedEmbedding c.m.hom := by
    apply coproduct_isClosedEmbedding hd₁ hd₂
      (fun j => (equivariantBasicCell n (c.π j)).hom)
      (fun j => OrbitCell.boundaryInclusion_isClosedEmbedding (c.π j).val n) c.m.hom
    intro j
    simpa only [d₁, d₂, cofan_mk_inj, Action.comp_hom] using congrArg Action.Hom.hom (c.hm j)
  let : T2Space (TopCat.disk.{u} n) := by
    change T2Space (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
    exact Homeomorph.ulift.{u,0}.symm.t2Space
  let : NormalSpace (TopCat.disk.{u} n) := inferInstance
  let hnormal (j : c.ι) : NormalSpace ((topologicalAction Γ (OrbitCell (c.π j).val (TopCat.disk.{u} n))).V) := by
    let : DiscreteTopology (Γ ⧸ (c.π j).val) := QuotientGroup.discreteTopology (isOpen_discrete _)
    exact normalSpace_discrete_prod
  let ht2 (j : c.ι) : T2Space ((topologicalAction Γ (OrbitCell (c.π j).val (TopCat.disk.{u} n))).V) :=
    inferInstanceAs (T2Space (OrbitCell (c.π j).val (TopCat.disk.{u} n)))
  exact ⟨hm, cofan_normal d₂ hd₂, cofan_t2 d₂ hd₂⟩

/-- Continuous real-valued functions extend over any orbit-cell attachment. -/
theorem orbitCellAttachment_extend_real
    {A B : Action TopCat.{u} Γ} {i : A ⟶ B} {n : ℕ}
    (c : HomotopicalAlgebra.AttachCells.{u} (equivariantBasicCell (Γ := Γ) n) i)
    (p : C(A.V, ℝ)) : ∃ F : C(B.V, ℝ), ∀ x, F (i.hom x) = p x := by
  obtain ⟨hm, hnormal, _⟩ := orbitAttachment_topology c
  let : NormalSpace ((Action.forget TopCat Γ).obj c.cofan₂.pt) := hnormal
  exact pushout_extend_real (c.isPushout.map (Action.forget TopCat Γ)) hm p

/-- Separation by real-valued functions survives an orbit-cell attachment. -/
theorem orbitCellAttachment_realSeparatesPoints
    {A B : Action TopCat.{u} Γ} {i : A ⟶ B} {n : ℕ}
    (c : HomotopicalAlgebra.AttachCells.{u} (equivariantBasicCell (Γ := Γ) n) i)
    (h : RealSeparatesPoints A.V) : RealSeparatesPoints B.V := by
  obtain ⟨hm, hnormal, ht2⟩ := orbitAttachment_topology c
  let : NormalSpace ((Action.forget TopCat Γ).obj c.cofan₂.pt) := hnormal
  let : T2Space ((Action.forget TopCat Γ).obj c.cofan₂.pt) := ht2
  exact pushout_realSeparatesPoints (c.isPushout.map (Action.forget TopCat Γ)) hm h

private theorem realTerminal_lifting {A B : TopCat.{u}} {i : A ⟶ B}
    (h : ∀ p : C(A, ℝ), ∃ F : C(B, ℝ), ∀ x, F (i x) = p x) :
    HasLiftingProperty i (terminal.from (TopCat.of (ULift.{u} ℝ))) := by
  constructor
  intro a b _
  let p : C(A, ℝ) := ⟨fun x => (a x).down, continuous_uliftDown.comp a.hom.continuous⟩
  obtain ⟨F, hF⟩ := h p
  let L : B ⟶ TopCat.of (ULift.{u} ℝ) :=
    TopCat.ofHom ⟨fun x => ⟨F x⟩, continuous_uliftUp.comp F.continuous⟩
  refine ⟨⟨{ l := L, fac_left := ?_, fac_right := terminalIsTerminal.hom_ext _ _ }⟩⟩
  ext x
  exact hF x

private instance : PreservesWellOrderContinuousOfShape ℕ (Action.forget TopCat.{u} Γ) where

private noncomputable def realExtensionSequence
    {A B : Action TopCat.{u} Γ} {i : A ⟶ B} (c : RelativeEquivariantCWComplex i) :
    (MorphismProperty.ofHoms (fun _ : Unit => terminal.from (TopCat.of (ULift.{u} ℝ)))).llp.TransfiniteCompositionOfShape
      ℕ i.hom where
  toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape.map (Action.forget TopCat Γ)
  map_mem n _ := by
    intro X Y q hq
    cases hq with
    | mk z => exact realTerminal_lifting (orbitCellAttachment_extend_real (c.attachment n))

/-- A continuous real function on any skeleton extends to the entire relative CW complex. -/
theorem RelativeEquivariantCWComplex.skeleton_extend_real
    {A B : Action TopCat.{u} Γ} {i : A ⟶ B} (c : RelativeEquivariantCWComplex i)
    (n : ℕ) (p : C((c.F.obj n).V, ℝ)) :
    ∃ F : C(B.V, ℝ), ∀ x, F ((c.incl.app n).hom x) = p x := by
  have hl := (realExtensionSequence c).mem_incl_app n
  have : HasLiftingProperty (c.incl.app n).hom (terminal.from (TopCat.of (ULift.{u} ℝ))) :=
    hl _ (MorphismProperty.ofHoms.mk ())
  let P : (c.F.obj n).V ⟶ TopCat.of (ULift.{u} ℝ) :=
    TopCat.ofHom ⟨fun x => ⟨p x⟩, continuous_uliftUp.comp p.continuous⟩
  let sq : CommSq P (c.incl.app n).hom (terminal.from _) (terminal.from B.V) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  refine ⟨⟨fun x => (sq.lift x).down, continuous_uliftDown.comp sq.lift.hom.continuous⟩, ?_⟩
  intro x
  exact congrArg ULift.down (ConcreteCategory.congr_hom sq.fac_left x)

end BC4lean.ProperActions

namespace BC4lean.ProperActions

/-- An injective continuous map pulls back point-separating real functions. -/
theorem RealSeparatesPoints.of_injective_continuous
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : RealSeparatesPoints Y) {f : X → Y} (hi : Function.Injective f) (hc : Continuous f) :
    RealSeparatesPoints X := by
  intro x y hxy
  obtain ⟨p, hp⟩ := h (f x) (f y) (hi.ne hxy)
  exact ⟨p.comp ⟨f, hc⟩, hp⟩

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]

set_option backward.isDefEq.respectTransparency false in
/-- Each skeleton inherits point separation from the initial subspace. -/
theorem RelativeEquivariantCWComplex.skeleton_realSeparatesPoints
    {A B : Action TopCat.{u} Γ} {i : A ⟶ B} (c : RelativeEquivariantCWComplex i)
    (hA : RealSeparatesPoints A.V) (n : ℕ) : RealSeparatesPoints (c.F.obj n).V := by
  induction n with
  | zero =>
    let e := TopCat.homeoOfIso ((Action.forget TopCat Γ).mapIso c.isoBot)
    exact hA.of_injective_continuous e.injective e.continuous
  | succ n hn => exact orbitCellAttachment_realSeparatesPoints (c.attachment n) hn

/-- Point-separating real functions on the skeleta extend to the final relative CW space. -/
theorem RelativeEquivariantCWComplex.realSeparatesPoints
    {A B : Action TopCat.{u} Γ} {i : A ⟶ B} (c : RelativeEquivariantCWComplex i)
    (hA : RealSeparatesPoints A.V) : RealSeparatesPoints B.V := by
  intro x y hxy
  obtain ⟨m, xm, hxm⟩ := c.exists_skeleton_preimage x
  obtain ⟨n, yn, hyn⟩ := c.exists_skeleton_preimage y
  let k := max m n
  let xk := (c.F.map (homOfLE (le_max_left m n))).hom xm
  let yk := (c.F.map (homOfLE (le_max_right m n))).hom yn
  have hx : (c.incl.app k).hom xk = x := by
    have h := ConcreteCategory.congr_hom
      (congrArg Action.Hom.hom (c.incl.naturality (homOfLE (le_max_left m n)))) xm
    exact h.trans hxm
  have hy : (c.incl.app k).hom yk = y := by
    have h := ConcreteCategory.congr_hom
      (congrArg Action.Hom.hom (c.incl.naturality (homOfLE (le_max_right m n)))) yn
    exact h.trans hyn
  have hne : xk ≠ yk := fun h => hxy (hx.symm.trans ((congrArg (c.incl.app k).hom h).trans hy))
  obtain ⟨p, hp⟩ := c.skeleton_realSeparatesPoints hA k xk yk hne
  obtain ⟨F, hF⟩ := c.skeleton_extend_real k p
  refine ⟨F, ?_⟩
  rw [← hx, ← hy, hF, hF]
  exact hp

/-- Absolute equivariant CW spaces have enough continuous real functions to separate points. -/
theorem EquivariantCWComplex.realSeparatesPoints
    {A : Action TopCat.{u} Γ} (c : EquivariantCWComplex A) : RealSeparatesPoints A.V := by
  apply RelativeEquivariantCWComplex.realSeparatesPoints c
  have hinit := initialIsInitial.isInitialObj (underlyingAction (Γ := Γ))
  let : IsEmpty ((⊥_ (Action TopCat.{u} Γ)).V) :=
    (Types.initial_iff_empty _).mp ⟨hinit⟩
  intro x
  exact isEmptyElim x

/-- Hausdorffness follows from the categorical equivariant CW data, without an extra premise. -/
theorem EquivariantCWComplex.t2Space
    {A : Action TopCat.{u} Γ} (c : EquivariantCWComplex A) : T2Space A.V :=
  c.realSeparatesPoints.t2Space

end BC4lean.ProperActions
