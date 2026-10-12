import BC4lean.GroupUniverseEvenBridge
import BC4lean.GroupUniverseCliffordBridge

/-! # Genuine parity groups with independent algebra and module universes

Even and odd are the existing actual full-homotopy quotients. Their
abelian groups use genuine direct sums, inverse rotation and arbitrary
interval witnesses. The graded-even and complete one-Clifford odd parity
identifications are their proved additive full-quotient equivalences.
-/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory.GroupUniverseParityGroup
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

/-- False is the actual even quotient and true the actual odd quotient,
with the original group, algebras and chosen module universe retained. -/
def KKParityGroup (p : Bool) (α : CStarAlgebraAction Γ A) (β : CStarAlgebraAction Γ B) :
    Type (max uΓ (max uA (max uB (uE + 1)))) :=
  match p with
  | false => KasparovHomotopyClass.{uΓ,uA,uB,uE} α β
  | true => OddKK.{uΓ,uA,uB,uE} α β

instance kkParityGroupAddCommGroup (p : Bool) :
    AddCommGroup (KKParityGroup.{uΓ,uA,uB,uE} p α β) := by
  cases p <;> dsimp [KKParityGroup] <;> infer_instance

/-- The full trivially graded quotient is the established even group. -/
def evenParityIdentification :
    GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α β
      CStarGrading.trivial CStarGrading.trivial ≃+
    KKParityGroup.{uΓ,uA,uB,uE} false α β :=
  GroupUniverseEvenBridge.addEquivalence

/-- The degree-one group is the full graded quotient with the actual
complete Clifford coefficient tensor and its plus-generator convention. -/
def oddParityIdentification :
    GradedKasparovHomotopyClass.{uΓ,uA,uB,uE} α (cliffordTensorAction β)
      CStarGrading.trivial cliffordTensorGrading ≃+
    KKParityGroup.{uΓ,uA,uB,uE} true α β :=
  GroupUniverseCliffordBridge.oddAddEquivalence

end BC4lean.KKTheory.GroupUniverseParityGroup
