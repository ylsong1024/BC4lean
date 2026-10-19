import BC4lean.BaumConnesProperty
import BC4lean.AssemblyCofinalIndex

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Invariance of actual assembly injectivity, surjectivity and bijectivity

All public transport statements use the concrete Chapter 6 comparison
equivalences and Chapter 7 assembly naturality proofs. No assembly compatibility
or bijectivity conclusion is supplied as an extra public hypothesis. Universal
proper-model comparison retains the existing common group/space universe;
homotopy comparison permits a separate group universe. Cofinal comparisons
retain the full upper-bound condition, not merely a pointwise cover.
-/

noncomputable section
universe uA uB uC uΓ uX uJ uL
namespace BC4lean.Assembly
open ProperActions

private theorem injective_iff_of_equiv
    {A : Type uA} {B : Type uB} {C : Type uC}
    (f : A → C) (g : B → C) (e : A ≃ B)
    (h : ∀ x, g (e x) = f x) :
    Function.Injective f ↔ Function.Injective g := by
  constructor
  · intro hf b₁ b₂ hb
    obtain ⟨a₁, rfl⟩ := e.surjective b₁
    obtain ⟨a₂, rfl⟩ := e.surjective b₂
    apply congrArg e
    apply hf
    exact (h a₁).symm.trans (hb.trans (h a₂))
  · intro hg a₁ a₂ ha
    apply e.injective
    apply hg
    exact (h a₁).trans (ha.trans (h a₂).symm)

private theorem surjective_iff_of_equiv
    {A : Type uA} {B : Type uB} {C : Type uC}
    (f : A → C) (g : B → C) (e : A ≃ B)
    (h : ∀ x, g (e x) = f x) :
    Function.Surjective f ↔ Function.Surjective g := by
  constructor
  · intro hf c
    obtain ⟨a, ha⟩ := hf c
    exact ⟨e a, (h a).trans ha⟩
  · intro hg c
    obtain ⟨b, hb⟩ := hg c
    obtain ⟨a, ha⟩ := e.surjective b
    exact ⟨a, (h a).symm.trans ((congrArg g ha).trans hb)⟩

private theorem bijective_iff_of_equiv
    {A : Type uA} {B : Type uB} {C : Type uC}
    (f : A → C) (g : B → C) (e : A ≃ B)
    (h : ∀ x, g (e x) = f x) :
    Function.Bijective f ↔ Function.Bijective g :=
  and_congr (injective_iff_of_equiv f g e h) (surjective_iff_of_equiv f g e h)

section ProperSpaces
variable (Γ : Type uΓ) [Group Γ] [Countable Γ]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  (X : Type uX) [TopologicalSpace X] [MulAction Γ X]
  [ContinuousConstSMul Γ X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [ProperSMul Γ X]

/-- Bijectivity of assembly on a chosen proper space. Universality is not part
of this definition; its comparison with Baum–Connes is proved separately. -/
def modelAssemblyProperty : Prop :=
  ∀ p : Bool, Function.Bijective (assemblyHom Γ X p)

section Homotopy
variable (Y : Type uX) [TopologicalSpace Y] [MulAction Γ Y]
  [ContinuousConstSMul Γ Y] [LocallyCompactSpace Y] [T2Space Y]
  [SecondCountableTopology Y] [ProperSMul Γ Y]

/-- Actual equivariant homotopy comparison preserves assembly injectivity. -/
theorem assemblyHom_injective_iff_homotopyEquiv (p : Bool)
    (e : EquivariantHomotopyEquiv Γ X Y) :
    Function.Injective (assemblyHom Γ X p) ↔
      Function.Injective (assemblyHom Γ Y p) :=
  injective_iff_of_equiv (assemblyHom Γ X p) (assemblyHom Γ Y p)
    (TopologicalKHomology.homotopyEquiv p e).toEquiv
    (assemblyHom_homotopyEquiv Γ X Y p e)

/-- Actual equivariant homotopy comparison preserves assembly surjectivity. -/
theorem assemblyHom_surjective_iff_homotopyEquiv (p : Bool)
    (e : EquivariantHomotopyEquiv Γ X Y) :
    Function.Surjective (assemblyHom Γ X p) ↔
      Function.Surjective (assemblyHom Γ Y p) :=
  surjective_iff_of_equiv (assemblyHom Γ X p) (assemblyHom Γ Y p)
    (TopologicalKHomology.homotopyEquiv p e).toEquiv
    (assemblyHom_homotopyEquiv Γ X Y p e)

/-- Actual equivariant homotopy comparison preserves assembly bijectivity. -/
theorem assemblyHom_bijective_iff_homotopyEquiv (p : Bool)
    (e : EquivariantHomotopyEquiv Γ X Y) :
    Function.Bijective (assemblyHom Γ X p) ↔
      Function.Bijective (assemblyHom Γ Y p) :=
  bijective_iff_of_equiv (assemblyHom Γ X p) (assemblyHom Γ Y p)
    (TopologicalKHomology.homotopyEquiv p e).toEquiv
    (assemblyHom_homotopyEquiv Γ X Y p e)

/-- Both assembly degrees are invariant under an actual equivariant homotopy
equivalence of the indicated proper spaces. -/
theorem modelAssemblyProperty_iff_homotopyEquiv
    (e : EquivariantHomotopyEquiv Γ X Y) :
    modelAssemblyProperty Γ X ↔ modelAssemblyProperty Γ Y := by
  constructor
  · intro h p
    exact (assemblyHom_bijective_iff_homotopyEquiv Γ X Y p e).mp (h p)
  · intro h p
    exact (assemblyHom_bijective_iff_homotopyEquiv Γ X Y p e).mpr (h p)

end Homotopy

section Cofinal
variable {J : Type uJ} [Preorder J] [Nonempty J] [IsDirectedOrder J]

/-- The actual assembly map on a monotone restricted system is bijective in
both degrees. Its comparison with the full system requires genuine cofinality. -/
def indexedAssemblyProperty (φ : J →o CocompactPiece Γ X) : Prop :=
  ∀ p : Bool, Function.Bijective (indexedAssemblyHom Γ X p φ)

/-- Genuine cofinal restriction preserves assembly injectivity. -/
theorem indexedAssemblyHom_injective_iff_cofinalIndex (p : Bool)
    (φ : J →o CocompactPiece Γ X) (hφ : ∀ S, ∃ j, S ≤ φ j) :
    Function.Injective (indexedAssemblyHom Γ X p φ) ↔
      Function.Injective (assemblyHom Γ X p) :=
  injective_iff_of_equiv (indexedAssemblyHom Γ X p φ) (assemblyHom Γ X p)
    (TopologicalKHomology.cofinalIndexEquiv p φ hφ).toEquiv
    (assemblyHom_cofinalIndexEquiv Γ X p φ hφ)

/-- Genuine cofinal restriction preserves assembly surjectivity. -/
theorem indexedAssemblyHom_surjective_iff_cofinalIndex (p : Bool)
    (φ : J →o CocompactPiece Γ X) (hφ : ∀ S, ∃ j, S ≤ φ j) :
    Function.Surjective (indexedAssemblyHom Γ X p φ) ↔
      Function.Surjective (assemblyHom Γ X p) :=
  surjective_iff_of_equiv (indexedAssemblyHom Γ X p φ) (assemblyHom Γ X p)
    (TopologicalKHomology.cofinalIndexEquiv p φ hφ).toEquiv
    (assemblyHom_cofinalIndexEquiv Γ X p φ hφ)

/-- Genuine cofinal restriction preserves assembly bijectivity. -/
theorem indexedAssemblyHom_bijective_iff_cofinalIndex (p : Bool)
    (φ : J →o CocompactPiece Γ X) (hφ : ∀ S, ∃ j, S ≤ φ j) :
    Function.Bijective (indexedAssemblyHom Γ X p φ) ↔
      Function.Bijective (assemblyHom Γ X p) :=
  bijective_iff_of_equiv (indexedAssemblyHom Γ X p φ) (assemblyHom Γ X p)
    (TopologicalKHomology.cofinalIndexEquiv p φ hφ).toEquiv
    (assemblyHom_cofinalIndexEquiv Γ X p φ hφ)

/-- The two-degree property for an actual cofinal subsystem equals that of
the full cocompact-piece system. -/
theorem indexedAssemblyProperty_iff_cofinalIndex
    (φ : J →o CocompactPiece Γ X) (hφ : ∀ S, ∃ j, S ≤ φ j) :
    indexedAssemblyProperty Γ X φ ↔ modelAssemblyProperty Γ X := by
  constructor
  · intro h p
    exact (indexedAssemblyHom_bijective_iff_cofinalIndex Γ X p φ hφ).mp (h p)
  · intro h p
    exact (indexedAssemblyHom_bijective_iff_cofinalIndex Γ X p φ hφ).mpr (h p)

variable {L : Type uL} [Preorder L] [Nonempty L] [IsDirectedOrder L]

/-- Two actual cofinal subsystems have equivalent assembly injectivity. -/
theorem indexedAssemblyHom_injective_iff_cofinalComparison (p : Bool)
    (φ : J →o CocompactPiece Γ X) (ψ : L →o CocompactPiece Γ X)
    (hφ : ∀ S, ∃ j, S ≤ φ j) (hψ : ∀ S, ∃ j, S ≤ ψ j) :
    Function.Injective (indexedAssemblyHom Γ X p φ) ↔
      Function.Injective (indexedAssemblyHom Γ X p ψ) :=
  injective_iff_of_equiv (indexedAssemblyHom Γ X p φ) (indexedAssemblyHom Γ X p ψ)
    ((TopologicalKHomology.diagram (Γ := Γ) (X := X) p).cofinalComparisonEquiv
      φ ψ hφ hψ).toEquiv
    (indexedAssemblyHom_cofinalComparisonEquiv Γ X p φ ψ hφ hψ)

/-- Two actual cofinal subsystems have equivalent assembly surjectivity. -/
theorem indexedAssemblyHom_surjective_iff_cofinalComparison (p : Bool)
    (φ : J →o CocompactPiece Γ X) (ψ : L →o CocompactPiece Γ X)
    (hφ : ∀ S, ∃ j, S ≤ φ j) (hψ : ∀ S, ∃ j, S ≤ ψ j) :
    Function.Surjective (indexedAssemblyHom Γ X p φ) ↔
      Function.Surjective (indexedAssemblyHom Γ X p ψ) :=
  surjective_iff_of_equiv (indexedAssemblyHom Γ X p φ) (indexedAssemblyHom Γ X p ψ)
    ((TopologicalKHomology.diagram (Γ := Γ) (X := X) p).cofinalComparisonEquiv
      φ ψ hφ hψ).toEquiv
    (indexedAssemblyHom_cofinalComparisonEquiv Γ X p φ ψ hφ hψ)

/-- Two actual cofinal subsystems have equivalent assembly bijectivity. -/
theorem indexedAssemblyHom_bijective_iff_cofinalComparison (p : Bool)
    (φ : J →o CocompactPiece Γ X) (ψ : L →o CocompactPiece Γ X)
    (hφ : ∀ S, ∃ j, S ≤ φ j) (hψ : ∀ S, ∃ j, S ≤ ψ j) :
    Function.Bijective (indexedAssemblyHom Γ X p φ) ↔
      Function.Bijective (indexedAssemblyHom Γ X p ψ) :=
  bijective_iff_of_equiv (indexedAssemblyHom Γ X p φ) (indexedAssemblyHom Γ X p ψ)
    ((TopologicalKHomology.diagram (Γ := Γ) (X := X) p).cofinalComparisonEquiv
      φ ψ hφ hψ).toEquiv
    (indexedAssemblyHom_cofinalComparisonEquiv Γ X p φ ψ hφ hψ)

/-- Both-degree bijectivity agrees for any two genuinely cofinal restrictions. -/
theorem indexedAssemblyProperty_iff_cofinalComparison
    (φ : J →o CocompactPiece Γ X) (ψ : L →o CocompactPiece Γ X)
    (hφ : ∀ S, ∃ j, S ≤ φ j) (hψ : ∀ S, ∃ j, S ≤ ψ j) :
    indexedAssemblyProperty Γ X φ ↔ indexedAssemblyProperty Γ X ψ :=
  (indexedAssemblyProperty_iff_cofinalIndex Γ X φ hφ).trans
    (indexedAssemblyProperty_iff_cofinalIndex Γ X ψ hψ).symm

end Cofinal
end ProperSpaces

section UniversalModels
variable (Γ : Type uX) [Group Γ] [Countable Γ]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  (X Y : Type uX) [TopologicalSpace X] [TopologicalSpace Y]
  [MulAction Γ X] [MulAction Γ Y]
  [ContinuousConstSMul Γ X] [ContinuousConstSMul Γ Y]
  [LocallyCompactSpace X] [LocallyCompactSpace Y] [T2Space X] [T2Space Y]
  [SecondCountableTopology X] [SecondCountableTopology Y]

/-- The proved universal proper-model equivalence preserves assembly
injectivity. The CW structures supply the properness instances. -/
theorem assemblyHom_injective_iff_universalModels (p : Bool)
    (cX : EquivariantCWComplex (topologicalAction Γ X))
    (cY : EquivariantCWComplex (topologicalAction Γ Y))
    (hX : FixedPointCriterion Γ X) (hY : FixedPointCriterion Γ Y) :
    letI := cX.proper
    letI := cY.proper
    Function.Injective (assemblyHom Γ X p) ↔
      Function.Injective (assemblyHom Γ Y p) := by
  let : ProperSMul Γ X := cX.proper
  let : ProperSMul Γ Y := cY.proper
  exact injective_iff_of_equiv (assemblyHom Γ X p) (assemblyHom Γ Y p)
    (TopologicalKHomology.universalModelEquiv p cX cY hX hY).toEquiv
    (assemblyHom_universalModelEquiv Γ X Y p cX cY hX hY)

/-- The proved universal proper-model equivalence preserves assembly
surjectivity. The CW structures supply the properness instances. -/
theorem assemblyHom_surjective_iff_universalModels (p : Bool)
    (cX : EquivariantCWComplex (topologicalAction Γ X))
    (cY : EquivariantCWComplex (topologicalAction Γ Y))
    (hX : FixedPointCriterion Γ X) (hY : FixedPointCriterion Γ Y) :
    letI := cX.proper
    letI := cY.proper
    Function.Surjective (assemblyHom Γ X p) ↔
      Function.Surjective (assemblyHom Γ Y p) := by
  let : ProperSMul Γ X := cX.proper
  let : ProperSMul Γ Y := cY.proper
  exact surjective_iff_of_equiv (assemblyHom Γ X p) (assemblyHom Γ Y p)
    (TopologicalKHomology.universalModelEquiv p cX cY hX hY).toEquiv
    (assemblyHom_universalModelEquiv Γ X Y p cX cY hX hY)

/-- The proved universal proper-model equivalence preserves assembly
bijectivity. The CW structures supply the properness instances. -/
theorem assemblyHom_bijective_iff_universalModels (p : Bool)
    (cX : EquivariantCWComplex (topologicalAction Γ X))
    (cY : EquivariantCWComplex (topologicalAction Γ Y))
    (hX : FixedPointCriterion Γ X) (hY : FixedPointCriterion Γ Y) :
    letI := cX.proper
    letI := cY.proper
    Function.Bijective (assemblyHom Γ X p) ↔
      Function.Bijective (assemblyHom Γ Y p) := by
  let : ProperSMul Γ X := cX.proper
  let : ProperSMul Γ Y := cY.proper
  exact bijective_iff_of_equiv (assemblyHom Γ X p) (assemblyHom Γ Y p)
    (TopologicalKHomology.universalModelEquiv p cX cY hX hY).toEquiv
    (assemblyHom_universalModelEquiv Γ X Y p cX cY hX hY)

/-- Genuine universal proper CW models give the same two-degree property. -/
theorem modelAssemblyProperty_iff_universalModels
    (cX : EquivariantCWComplex (topologicalAction Γ X))
    (cY : EquivariantCWComplex (topologicalAction Γ Y))
    (hX : FixedPointCriterion Γ X) (hY : FixedPointCriterion Γ Y) :
    letI := cX.proper
    letI := cY.proper
    modelAssemblyProperty Γ X ↔ modelAssemblyProperty Γ Y := by
  let : ProperSMul Γ X := cX.proper
  let : ProperSMul Γ Y := cY.proper
  constructor
  · intro h p
    exact (assemblyHom_bijective_iff_universalModels Γ X Y p cX cY hX hY).mp (h p)
  · intro h p
    exact (assemblyHom_bijective_iff_universalModels Γ X Y p cX cY hX hY).mpr (h p)

end UniversalModels

section CanonicalModel
variable (Γ : Type uX) [Group Γ] [Countable Γ]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  (X : Type uX) [TopologicalSpace X] [MulAction Γ X]
  [ContinuousConstSMul Γ X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X]

/-- Assembly injectivity on a genuine universal proper CW model is
exactly injectivity of the constructed canonical assembly map. -/
theorem assemblyHom_injective_iff_canonical (p : Bool)
    (cX : EquivariantCWComplex (topologicalAction Γ X))
    (hX : FixedPointCriterion Γ X) :
    letI := cX.proper
    Function.Injective (assemblyHom Γ X p) ↔
      Function.Injective (reducedAssemblyHom Γ p) := by
  let : ProperSMul Γ X := cX.proper
  let : ProperSMul Γ (LabeledOrbitTelescope.Model Γ) := LabeledOrbitTelescope.proper Γ
  change Function.Injective (assemblyHom Γ X p) ↔
    Function.Injective (assemblyHom Γ (LabeledOrbitTelescope.Model Γ) p)
  exact assemblyHom_injective_iff_universalModels Γ X (LabeledOrbitTelescope.Model Γ) p
    cX (LabeledOrbitTelescope.equivariantCWComplex Γ)
    hX (LabeledOrbitTelescope.fixedPointCriterion Γ)

/-- Assembly surjectivity on a genuine universal proper CW model is
exactly surjectivity of the constructed canonical assembly map. -/
theorem assemblyHom_surjective_iff_canonical (p : Bool)
    (cX : EquivariantCWComplex (topologicalAction Γ X))
    (hX : FixedPointCriterion Γ X) :
    letI := cX.proper
    Function.Surjective (assemblyHom Γ X p) ↔
      Function.Surjective (reducedAssemblyHom Γ p) := by
  let : ProperSMul Γ X := cX.proper
  let : ProperSMul Γ (LabeledOrbitTelescope.Model Γ) := LabeledOrbitTelescope.proper Γ
  change Function.Surjective (assemblyHom Γ X p) ↔
    Function.Surjective (assemblyHom Γ (LabeledOrbitTelescope.Model Γ) p)
  exact assemblyHom_surjective_iff_universalModels Γ X (LabeledOrbitTelescope.Model Γ) p
    cX (LabeledOrbitTelescope.equivariantCWComplex Γ)
    hX (LabeledOrbitTelescope.fixedPointCriterion Γ)

/-- Assembly bijectivity on a genuine universal proper CW model is
exactly bijectivity of the constructed canonical assembly map. -/
theorem assemblyHom_bijective_iff_canonical (p : Bool)
    (cX : EquivariantCWComplex (topologicalAction Γ X))
    (hX : FixedPointCriterion Γ X) :
    letI := cX.proper
    Function.Bijective (assemblyHom Γ X p) ↔
      Function.Bijective (reducedAssemblyHom Γ p) := by
  let : ProperSMul Γ X := cX.proper
  let : ProperSMul Γ (LabeledOrbitTelescope.Model Γ) := LabeledOrbitTelescope.proper Γ
  change Function.Bijective (assemblyHom Γ X p) ↔
    Function.Bijective (assemblyHom Γ (LabeledOrbitTelescope.Model Γ) p)
  exact assemblyHom_bijective_iff_universalModels Γ X (LabeledOrbitTelescope.Model Γ) p
    cX (LabeledOrbitTelescope.equivariantCWComplex Γ)
    hX (LabeledOrbitTelescope.fixedPointCriterion Γ)

/-- The Baum–Connes property uses the actual canonical telescope and is
equivalent to assembly bijectivity on every indicated genuine universal model. -/
theorem modelAssemblyProperty_iff_baumConnesProperty
    (cX : EquivariantCWComplex (topologicalAction Γ X))
    (hX : FixedPointCriterion Γ X) :
    letI := cX.proper
    modelAssemblyProperty Γ X ↔ BaumConnesProperty Γ := by
  let : ProperSMul Γ X := cX.proper
  constructor
  · intro h p
    exact (assemblyHom_bijective_iff_canonical Γ X p cX hX).mp (h p)
  · intro h p
    exact (assemblyHom_bijective_iff_canonical Γ X p cX hX).mpr (h p)

end CanonicalModel
end BC4lean.Assembly
