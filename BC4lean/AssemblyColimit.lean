import BC4lean.AssemblyTransition
import BC4lean.TopologicalKHomologyColimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The actual assembly homomorphism on the existing topological colimit

The construction imports concrete descent, cutoff naturality and transition
proofs. The constructed
map descends the actual piece homomorphisms through the established Chapter 6
directed additive-group colimit. No arbitrary family or compatibility witness
is supplied as a user hypothesis. Universal-model independence and the full
descent product compatibility remain separate obligations.
-/

noncomputable section
universe uΓ uX
namespace BC4lean.Assembly
open ProperActions

variable (Γ : Type uΓ) [Group Γ] [Countable Γ]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  (X : Type uX) [TopologicalSpace X] [MulAction Γ X]
  [ContinuousConstSMul Γ X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [ProperSMul Γ X]

/-- The actual assembly homomorphism for the given proper ambient model. -/
def assemblyHom (p : Bool) :
    TopologicalKHomology.group (Γ := Γ) (X := X) p →+ analyticGroup Γ p :=
  (TopologicalKHomology.diagram (Γ := Γ) (X := X) p).desc
    (pieceAssemblyHom Γ X p)
    (fun _ _ h x => pieceAssemblyHom_transition Γ X p h x)

/-- Its restriction to every actual cocompact piece is exactly the genuine
cutoff/product assembly homomorphism defined above. -/
@[simp] theorem assemblyHom_ofPiece (p : Bool) (S : CocompactPiece Γ X)
    (x : TopologicalKHomology.pieceGroup p S) :
    assemblyHom Γ X p (TopologicalKHomology.ofPiece p S x) = pieceAssemblyHom Γ X p S x := rfl

/-- The existing colimit universal property determines this constructed map. -/
theorem assemblyHom_unique (p : Bool)
    (F : TopologicalKHomology.group (Γ := Γ) (X := X) p →+ analyticGroup Γ p)
    (hF : ∀ S : CocompactPiece Γ X,
      F.comp (TopologicalKHomology.ofPiece p S) = pieceAssemblyHom Γ X p S) :
    F = assemblyHom Γ X p :=
  (TopologicalKHomology.diagram (Γ := Γ) (X := X) p).desc_unique
    (pieceAssemblyHom Γ X p) (fun _ _ h x => pieceAssemblyHom_transition Γ X p h x) F hF

/-- Even assembly lands in the established reduced projection K0 group. -/
def assemblyEvenHom : TopologicalKHomology.group (Γ := Γ) (X := X) false →+ ReducedK0 Γ :=
  assemblyHom Γ X false

/-- Odd assembly lands in the established reduced stable-unitary K1 group. -/
def assemblyOddHom : TopologicalKHomology.group (Γ := Γ) (X := X) true →+ ReducedK1 Γ :=
  assemblyHom Γ X true

end BC4lean.Assembly
