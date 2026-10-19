import BC4lean.AssemblyColimit
import BC4lean.AssemblyProperNaturality
import BC4lean.TopologicalKHomologyHomotopy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Actual comparison-map and universal proper-model independence

The construction imports concrete descent, cutoff, transition and colimit
results. Arbitrary
ambient equivariant maps are restricted by Chapter 6 to genuine proper maps
on cocompact pieces. The concrete assembly naturality there descends through
the existing actual colimit. Universal-model comparison uses the established
CW fixed-point uniqueness equivalence, rather than an assumed K-homology map.
-/

noncomputable section
universe uΓ uX
namespace BC4lean.Assembly
open ProperActions

section Maps
variable (Γ : Type uΓ) [Group Γ] [Countable Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
  (X Y : Type uX) [TopologicalSpace X] [TopologicalSpace Y]
  [MulAction Γ X] [MulAction Γ Y]
  [ContinuousConstSMul Γ X] [ContinuousConstSMul Γ Y]
  [LocallyCompactSpace X] [LocallyCompactSpace Y] [T2Space X] [T2Space Y]
  [SecondCountableTopology X] [SecondCountableTopology Y]
  [ProperSMul Γ X] [ProperSMul Γ Y]

local instance source_piece_locallyCompact (S : CocompactPiece Γ X) :
    LocallyCompactSpace S.toInvariantSubset := S.locallyCompact
local instance target_piece_locallyCompact (T : CocompactPiece Γ Y) :
    LocallyCompactSpace T.toInvariantSubset := T.locallyCompact

/-- Every actual bounded piece map has the same assembly value. The ambient
map need not be proper; its existing restricted map is genuinely proper. -/
theorem pieceAssemblyHom_boundedMap (p : Bool) (f : EquivariantMap Γ X Y)
    (S : CocompactPiece Γ X) (T : CocompactPiece Γ Y)
    (h : CocompactPiece.map f S ≤ T) (x : TopologicalKHomology.pieceGroup p S) :
    pieceAssemblyHom Γ Y p T (TopologicalKHomology.boundedMap p f S T h x) =
      pieceAssemblyHom Γ X p S x :=
  spaceAssemblyHom_properPushforward Γ S.toInvariantSubset T.toInvariantSubset p
    (CocompactPiece.mapRestrictionTo f S T h)
    (CocompactPiece.mapRestrictionTo_isProperMap f S T h)
    (pieceCutoff Γ Y T) (pieceCutoff Γ X S) x

/-- The constructed colimit assembly is natural for every actual ambient
equivariant map between the indicated proper spaces. -/
theorem assemblyHom_pushforward (p : Bool) (f : EquivariantMap Γ X Y)
    (x : TopologicalKHomology.group (Γ := Γ) (X := X) p) :
    assemblyHom Γ Y p (TopologicalKHomology.pushforward p f x) = assemblyHom Γ X p x := by
  obtain ⟨S, y, rfl⟩ := (TopologicalKHomology.diagram (Γ := Γ) (X := X) p).exists_of x
  change TopologicalKHomology.pieceGroup p S at y
  change assemblyHom Γ Y p
      (TopologicalKHomology.pushforward p f (TopologicalKHomology.ofPiece p S y)) =
    assemblyHom Γ X p (TopologicalKHomology.ofPiece p S y)
  rw [TopologicalKHomology.pushforward_ofPiece, assemblyHom_ofPiece, assemblyHom_ofPiece]
  exact pieceAssemblyHom_boundedMap Γ X Y p f S (CocompactPiece.map f S) le_rfl y

theorem assemblyHom_comp_pushforward (p : Bool) (f : EquivariantMap Γ X Y) :
    (assemblyHom Γ Y p).comp (TopologicalKHomology.pushforward p f) = assemblyHom Γ X p := by
  apply AddMonoidHom.ext
  intro x
  exact assemblyHom_pushforward Γ X Y p f x

/-- In particular the established actual homotopy-equivalence map preserves
the assembly value on every topological class. -/
theorem assemblyHom_homotopyEquiv (p : Bool) (e : EquivariantHomotopyEquiv Γ X Y)
    (x : TopologicalKHomology.group (Γ := Γ) (X := X) p) :
    assemblyHom Γ Y p (TopologicalKHomology.homotopyEquiv p e x) = assemblyHom Γ X p x :=
  assemblyHom_pushforward Γ X Y p e.toMap x

end Maps

section UniversalModels
variable (Γ : Type uX) [Group Γ] [Countable Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
  (X Y : Type uX) [TopologicalSpace X] [TopologicalSpace Y]
  [MulAction Γ X] [MulAction Γ Y]
  [ContinuousConstSMul Γ X] [ContinuousConstSMul Γ Y]
  [LocallyCompactSpace X] [LocallyCompactSpace Y] [T2Space X] [T2Space Y]
  [SecondCountableTopology X] [SecondCountableTopology Y]

/-- The existing fixed-point criterion supplies the genuine universal-model
equivalence, and the assembly maps commute with that actual equivalence. -/
theorem assemblyHom_universalModelEquiv (p : Bool)
    (cX : EquivariantCWComplex (topologicalAction Γ X))
    (cY : EquivariantCWComplex (topologicalAction Γ Y))
    (hX : FixedPointCriterion Γ X) (hY : FixedPointCriterion Γ Y) :
    letI := cX.proper
    letI := cY.proper
    ∀ x : TopologicalKHomology.group (Γ := Γ) (X := X) p,
      assemblyHom Γ Y p (TopologicalKHomology.universalModelEquiv p cX cY hX hY x) =
        assemblyHom Γ X p x := by
  let := cX.proper
  let := cY.proper
  intro x
  exact assemblyHom_homotopyEquiv Γ X Y p
    (Classical.choice (cX.fixedPointCriterion_unique cY hX hY)) x

end UniversalModels

section Canonical
variable (Γ : Type uX) [Group Γ] [Countable Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]

/-- The canonical assembly homomorphism uses Chapter 4's actual geometric
telescope and Chapter 6's established canonical topological group. -/
def reducedAssemblyHom (p : Bool) :
    TopologicalKHomology.topologicalGroup p Γ →+ analyticGroup Γ p := by
  letI : ProperSMul Γ (LabeledOrbitTelescope.Model Γ) := LabeledOrbitTelescope.proper Γ
  exact assemblyHom Γ (LabeledOrbitTelescope.Model Γ) p

def reducedAssemblyEvenHom : TopologicalKHomology.topologicalGroup false Γ →+ ReducedK0 Γ :=
  reducedAssemblyHom Γ false

def reducedAssemblyOddHom : TopologicalKHomology.topologicalGroup true Γ →+ ReducedK1 Γ :=
  reducedAssemblyHom Γ true

end Canonical
end BC4lean.Assembly
