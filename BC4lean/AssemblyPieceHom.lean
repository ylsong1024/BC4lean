import BC4lean.KasparovDescentClass
import BC4lean.ReducedScalarKKComparison
import BC4lean.ReducedCutoffProjection
import BC4lean.CocompactPieceCutoff
import BC4lean.TopologicalKHomologyDiagram
import BC4lean.GroupUniverseCommonParityProduct

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The actual cutoff product defining assembly on a cocompact piece

The construction uses the concrete descent class homomorphism and its
raw/full-homotopy prerequisites. The definition
below uses that specific constructed map, the actual cutoff OperatorK0 class,
the inverse genuine scalar KK/K0 comparison, the existing native parity
products, and the true scalar crossed-to-reduced-group K-theory maps.

Product compatibility for descent is not an input to this definition. Neither
transition compatibility nor a map on the topological colimit is asserted.
-/

noncomputable section
universe uΓ uX
namespace BC4lean.Assembly
open KKTheory ProperActions OperatorKTheory
open KKTheory.GroupUniverseParityGroup
open scoped ZeroAtInfty ComplexOrder KasparovDescent

variable (Γ : Type uΓ) [Group Γ] [Countable Γ]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  (X : Type uX) [TopologicalSpace X] [MulAction Γ X]
  [ContinuousConstSMul Γ X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [ProperSMul Γ X]

local instance spaceCoefficient_separable :
    TopologicalSpace.SeparableSpace C₀(X, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

/-- The actual cutoff K0 class, lifted by the proved inverse scalar comparison.
The module universe contains both the group and the actual source algebra. -/
def cutoffKKClass (c : Cutoff.CutoffFunction Γ X) :
    KKParityGroup.{0, 0, max uΓ uX, max uΓ uX} false
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
        (ReducedCrossedProduct (CZero.action Γ (X := X)))) :=
  (scalarKKOperatorK0AddEquiv.{max uΓ uX, max uΓ uX}).symm (Cutoff.cutoffK0 c)

/-- The mixed-cutoff partial isometry proves equality before forming a product. -/
theorem cutoffKKClass_independent (c d : Cutoff.CutoffFunction Γ X) :
    cutoffKKClass Γ X c = cutoffKKClass Γ X d := by
  unfold cutoffKKClass
  rw [Cutoff.cutoffK0_independent c d]

/-- Left product by the actual even cutoff class, using the existing native
even-even or even-odd product according to the requested degree. -/
def cutoffProductHom (p : Bool) (c : Cutoff.CutoffFunction Γ X) :
    KKParityGroup.{0, max uΓ uX, uΓ, max uΓ uX} p
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
        (ReducedCrossedProduct (CZero.action Γ (X := X))))
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
        (ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ))) →+
    KKParityGroup.{0, 0, uΓ, max uΓ uX} p
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
        (ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ))) := by
  cases p
  · exact GroupUniverseCommonParityProduct.productAddHom.{0, 0, max uΓ uX, uΓ, max uΓ uX}
      false false (cutoffKKClass Γ X c)
  · exact GroupUniverseCommonParityProduct.productAddHom.{0, 0, max uΓ uX, uΓ, max uΓ uX}
      false true (cutoffKKClass Γ X c)

/-- The actual piece formula [p_c] tensor j_r(x), followed by the native
KK-to-K_i comparison and the actual scalar crossed-product identification. -/
def spaceAssemblyHom (p : Bool) (c : Cutoff.CutoffFunction Γ X) :
    TopologicalKHomology.spaceGroup p Γ X →+ analyticGroup Γ p :=
  (reducedScalarKKToAnalyticHom.{uΓ, max uΓ uX} Γ p).comp
    ((cutoffProductHom Γ X p c).comp
      (KasparovDescent.classHom.{uΓ, uX, 0, uX}
        (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
        (CZero.action Γ (X := X)) p))

/-- Independence of the auxiliary cutoff follows from its actual K0 class. -/
theorem spaceAssemblyHom_independent (p : Bool) (c d : Cutoff.CutoffFunction Γ X) :
    spaceAssemblyHom Γ X p c = spaceAssemblyHom Γ X p d := by
  have h := cutoffKKClass_independent Γ X c d
  cases p <;> simp only [spaceAssemblyHom, cutoffProductHom, h]

local instance piece_locallyCompact (S : CocompactPiece Γ X) :
    LocallyCompactSpace S.toInvariantSubset := S.locallyCompact

/-- The cutoff exists on every actual Chapter 6 closed cocompact piece,
including empty pieces, by the established proper-cocompact construction. -/
def pieceCutoff (S : CocompactPiece Γ X) : Cutoff.CutoffFunction Γ S.toInvariantSubset :=
  Classical.choice S.exists_cutoffFunction

/-- Assembly on the actual Chapter 6 piece group in either degree. Its
codomain consists of the established ReducedK0 or ReducedK1 group. -/
def pieceAssemblyHom (p : Bool) (S : CocompactPiece Γ X) :
    TopologicalKHomology.pieceGroup p S →+ analyticGroup Γ p :=
  spaceAssemblyHom Γ S.toInvariantSubset p (pieceCutoff Γ X S)

theorem pieceAssemblyHom_eq_of_cutoff (p : Bool) (S : CocompactPiece Γ X)
    (c : Cutoff.CutoffFunction Γ S.toInvariantSubset) :
    pieceAssemblyHom Γ X p S = spaceAssemblyHom Γ S.toInvariantSubset p c :=
  spaceAssemblyHom_independent Γ S.toInvariantSubset p (pieceCutoff Γ X S) c

/-- The degree-zero endpoint has exactly the existing ReducedK0 target. -/
def pieceAssemblyEvenHom (S : CocompactPiece Γ X) :
    TopologicalKHomology.pieceGroup false S →+ ReducedK0 Γ :=
  pieceAssemblyHom Γ X false S

/-- The degree-one endpoint has exactly the existing ReducedK1 target. -/
def pieceAssemblyOddHom (S : CocompactPiece Γ X) :
    TopologicalKHomology.pieceGroup true S →+ ReducedK1 Γ :=
  pieceAssemblyHom Γ X true S

end BC4lean.Assembly
