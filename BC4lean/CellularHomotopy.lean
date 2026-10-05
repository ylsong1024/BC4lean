import BC4lean.EquivariantPathLifting

/-! # Homotopy uniqueness for maps from equivariant CW complexes -/

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

namespace BC4lean.ProperActions

universe u

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
variable {X : Type u} [TopologicalSpace X] [MulAction Γ X] [ContinuousConstSMul Γ X]

/-- The equivariant map recording both endpoints of a path. -/
def pathEndpointPair : EquivariantMap Γ C(I,X) (X × X) where
  toFun p := (p 0, p 1)
  continuous_toFun := (continuous_eval_const 0).prodMk (continuous_eval_const 1)
  map_smul' _ _ := rfl

/-- Contractible fixed-point targets lift orbit cells against path endpoint evaluation. -/
theorem basicCell_path_hasLiftingProperty (h : FixedPointCriterion Γ X)
    (n : ℕ) (H : FiniteIsotropy Γ) :
    HasLiftingProperty (equivariantBasicCell n H) (pathEndpointPair (Γ := Γ) (X := X)).toActionHom := by
  constructor
  intro a b sq
  let : ContractibleSpace (FixedPointSpace H.val X) := h.1 H.val H.property
  let a' := EquivariantMap.ofActionHom a
  let b' := EquivariantMap.ofActionHom b
  let f₀ : EquivariantMap Γ (OrbitCell H.val (TopCat.disk.{u} n)) X :=
    { toFun := fun x => (b' x).1,
      continuous_toFun := continuous_fst.comp b'.continuous,
      map_smul' := fun g x => congrArg Prod.fst (b'.map_smul g x) }
  let f₁ : EquivariantMap Γ (OrbitCell H.val (TopCat.disk.{u} n)) X :=
    { toFun := fun x => (b' x).2,
      continuous_toFun := continuous_snd.comp b'.continuous,
      map_smul' := fun g x => congrArg Prod.snd (b'.map_smul g x) }
  obtain ⟨F, hi, h₀, h₁⟩ := orbitCell_path_lifting H.val n a' f₀ f₁
    (EquivariantMap.ext fun x => congrArg (fun k => (k.hom x).1) sq.w)
    (EquivariantMap.ext fun x => congrArg (fun k => (k.hom x).2) sq.w)
  refine ⟨⟨{ l := F.toActionHom, fac_left := ?_, fac_right := ?_ }⟩⟩
  · exact (congrArg EquivariantMap.toActionHom hi).trans
      (EquivariantMap.actionHomEquiv.apply_symm_apply a)
  · apply Action.Hom.ext
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact Prod.ext (congrArg (fun f => f x) h₀) (congrArg (fun f => f x) h₁)

/-- Path endpoint lifting extends from cells to every relative equivariant CW structure. -/
theorem RelativeEquivariantCWComplex.path_hasLiftingProperty
    {A B : Action TopCat.{u} Γ} {i : A ⟶ B}
    (c : RelativeEquivariantCWComplex i) (h : FixedPointCriterion Γ X) :
    HasLiftingProperty i (pathEndpointPair (Γ := Γ) (X := X)).toActionHom := by
  let W := MorphismProperty.ofHoms (fun p : ℕ × FiniteIsotropy Γ => equivariantBasicCell p.1 p.2)
  have hc : ∀ s : c.Cells, W (equivariantBasicCell s.j s.i) :=
    fun s => MorphismProperty.ofHoms.mk (s.j, s.i)
  have hr : W.rlp (pathEndpointPair (Γ := Γ) (X := X)).toActionHom := by
    intro A B f hf
    cases hf with
    | mk p => exact basicCell_path_hasLiftingProperty h p.1 p.2
  exact W.transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp ℕ i
    ⟨c.transfiniteCompositionOfShape' hc⟩ _ hr

variable {A : Type u} [TopologicalSpace A] [MulAction Γ A] [ContinuousConstSMul Γ A]

/-- Any two maps from an equivariant CW complex into a fixed-point-criterion target are homotopic. -/
theorem EquivariantCWComplex.homotopic (c : EquivariantCWComplex (topologicalAction Γ A))
    (h : FixedPointCriterion Γ X) (f g : EquivariantMap Γ A X) : EquivariantlyHomotopic f g := by
  let b : EquivariantMap Γ A (X × X) :=
    { toFun := fun x => (f x, g x), continuous_toFun := f.continuous.prodMk g.continuous,
      map_smul' := fun a x => Prod.ext (f.map_smul a x) (g.map_smul a x) }
  let := c.path_hasLiftingProperty h
  let sq : CommSq (initial.to (topologicalAction Γ C(I,X)))
      (initial.to (topologicalAction Γ A)) (pathEndpointPair (Γ := Γ) (X := X)).toActionHom
      b.toActionHom := ⟨initialIsInitial.hom_ext _ _⟩
  let F := EquivariantMap.ofActionHom sq.lift
  have he (x : A) : (F x 0, F x 1) = (f x, g x) :=
    congrArg (fun k => k.hom x) sq.fac_right
  refine ⟨{ toHomotopy :=
    { toFun := fun p => F p.2 p.1,
      continuous_toFun := (F.continuous.comp continuous_snd).eval continuous_fst,
      map_zero_left := fun x => congrArg Prod.fst (he x),
      map_one_left := fun x => congrArg Prod.snd (he x) }, prop' := ?_ }⟩
  intro t a x
  exact congrArg (fun p : C(I,X) => p t) (F.map_smul a x)

/-- The fixed-point criterion implies the homotopy-terminal mapping property for CW sources. -/
theorem EquivariantCWComplex.homotopyTerminal (c : EquivariantCWComplex (topologicalAction Γ A))
    (h : FixedPointCriterion Γ X) : HomotopyTerminalFor Γ A X := by
  obtain ⟨f⟩ := c.nonempty_map h
  exact ⟨⟨EquivariantMap.ofActionHom f⟩, c.homotopic h⟩

/-- Two equivariant CW spaces satisfying the fixed-point criterion are equivariantly homotopy equivalent. -/
theorem EquivariantCWComplex.fixedPointCriterion_unique
    (cA : EquivariantCWComplex (topologicalAction Γ A))
    (cX : EquivariantCWComplex (topologicalAction Γ X))
    (hA : FixedPointCriterion Γ A) (hX : FixedPointCriterion Γ X) :
    Nonempty (EquivariantHomotopyEquiv Γ A X) :=
  homotopyTerminal_unique (cA.homotopyTerminal hX) (cX.homotopyTerminal hA)
    (cA.homotopyTerminal hA) (cX.homotopyTerminal hX)

end BC4lean.ProperActions
