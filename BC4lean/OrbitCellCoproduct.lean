import BC4lean.EquivariantCW

/-! # Explicit coproducts of orbit cells -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace BC4lean.ProperActions
universe u
variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]

/-- Disjoint union of homogeneous orbit cells with a common parameter space. -/
def SigmaOrbitCells {ι : Type u} (p : ι → FiniteIsotropy Γ)
    (D : Type u) [TopologicalSpace D] := Σ i, OrbitCell (p i).val D

namespace SigmaOrbitCells
variable {ι : Type u} (p : ι → FiniteIsotropy Γ)
variable {D E : Type u} [TopologicalSpace D] [TopologicalSpace E]

instance : TopologicalSpace (SigmaOrbitCells p D) :=
  inferInstanceAs (TopologicalSpace (Σ i, OrbitCell (p i).val D))

instance : MulAction Γ (SigmaOrbitCells p D) where
  smul g x := ⟨x.1, g • x.2⟩
  one_smul x := congrArg (Sigma.mk x.1) (one_smul Γ x.2)
  mul_smul g h x := congrArg (Sigma.mk x.1) (mul_smul g h x.2)

instance : ContinuousConstSMul Γ (SigmaOrbitCells p D) where
  continuous_const_smul g := continuous_sigma (fun i =>
    (@continuous_sigmaMk ι (fun j => OrbitCell (p j).val D)
      (fun _j => inferInstance) i).comp (continuous_const_smul g))

/-- The inclusion of a component in the orbit-cell coproduct. -/
def inclusion (i : ι) : EquivariantMap Γ (OrbitCell (p i).val D) (SigmaOrbitCells p D) where
  toFun x := ⟨i, x⟩
  continuous_toFun := @continuous_sigmaMk ι (fun j => OrbitCell (p j).val D)
    (fun _j => inferInstance) i
  map_smul' _ _ := rfl

/-- Apply the same parameter map on each component. -/
def map (f : C(D, E)) : EquivariantMap Γ (SigmaOrbitCells p D) (SigmaOrbitCells p E) where
  toFun x := ⟨x.1, OrbitCell.map (p x.1).val f x.2⟩
  continuous_toFun := continuous_sigma (fun i =>
    (@continuous_sigmaMk ι (fun j => OrbitCell (p j).val E)
      (fun _j => inferInstance) i).comp (OrbitCell.map (p i).val f).continuous)
  map_smul' g x := congrArg (Sigma.mk x.1) ((OrbitCell.map (p x.1).val f).map_smul g x.2)

omit [DiscreteTopology Γ] in
@[simp] theorem map_inclusion (f : C(D, E)) (i : ι) :
    (map p f).comp (inclusion p i) =
      (inclusion p i).comp (OrbitCell.map (p i).val f) := by
  ext x
  rfl

/-- Assemble a continuous equivariant family out of the disjoint union. -/
def fold {X : Type u} [TopologicalSpace X] [MulAction Γ X]
    (f : ∀ i, EquivariantMap Γ (OrbitCell (p i).val D) X) :
    EquivariantMap Γ (SigmaOrbitCells p D) X where
  toFun x := f x.1 x.2
  continuous_toFun := continuous_sigma (fun i => (f i).continuous)
  map_smul' g x := (f x.1).map_smul g x.2

omit [DiscreteTopology Γ] in
@[simp] theorem fold_inclusion {X : Type u} [TopologicalSpace X] [MulAction Γ X]
    (f : ∀ i, EquivariantMap Γ (OrbitCell (p i).val D) X) (i : ι) :
    (fold p f).comp (inclusion p i) = f i := by
  ext x
  rfl

end SigmaOrbitCells

variable {ι : Type u} (p : ι → FiniteIsotropy Γ) (D : Type u) [TopologicalSpace D]

/-- Explicit coproduct cocone of topological Γ-actions. -/
def orbitCellCofan : Cofan (fun i => topologicalAction Γ (OrbitCell (p i).val D)) :=
  Cofan.mk (topologicalAction Γ (SigmaOrbitCells p D))
    (fun i => (SigmaOrbitCells.inclusion p i).toActionHom)

/-- The explicit disjoint union has the full categorical coproduct property. -/
def orbitCellCofan_isColimit : IsColimit (orbitCellCofan p D) := by
  refine Cofan.IsColimit.mk (orbitCellCofan p D) (fun s => ?_) ?_ ?_
  · change topologicalAction Γ (SigmaOrbitCells p D) ⟶ s.pt
    exact {
      hom := TopCat.ofHom ⟨fun x => (s.inj x.1).hom x.2,
        continuous_sigma (fun i => (s.inj i).hom.hom.continuous)⟩
      comm := fun g => by
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro x
        exact ConcreteCategory.congr_hom (s.inj x.1 |>.comm g) x.2 }
  · intro s i
    apply Action.Hom.ext
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rfl
  · intro s m hm
    apply Action.Hom.ext
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro ⟨i,x⟩
    have he := ConcreteCategory.congr_hom (congrArg Action.Hom.hom (hm i)) x
    change m.hom ⟨i, x⟩ = (s.inj i).hom x at he
    exact he

end BC4lean.ProperActions
