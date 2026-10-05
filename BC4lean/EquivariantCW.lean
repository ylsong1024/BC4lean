import BC4lean.ProperOrbitCells
import Mathlib.Topology.CWComplex.Abstract.Basic
import Mathlib.CategoryTheory.Action.Limits
import Mathlib.CategoryTheory.Types.Monomorphisms

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
