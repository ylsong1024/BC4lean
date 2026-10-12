import BC4lean.GradedTripleAnticommutatorConnection
import BC4lean.GradedTensorAnticommutatorCommute
import BC4lean.ModuleCreationPositivePartIntertwining
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

/-! # Both genuine localities of the associativity partition residual

The first-pair anticommutator has two different roles. Its genuine third
connection makes it a zero connection on the first-pair creation ranges.
Its connection to the second-pair anticommutator, coefficient commutators
and actual localized product positivity make its positive-part residual a
zero connection on the original first-module creation ranges as well.
These are derived from the original signed connection laws, not asserted
as technical theorem inputs.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovTriple
open InteriorModuleTensorAssociator
open GradedTripleAnticommutatorConnection

variable {B C D E F G : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Dᵐᵒᵖ G] [CStarModule Dᵐᵒᵖ G]
  [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
  {δB : CStarGrading B} {δC : CStarGrading C}
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
  (ψ : C →⋆ₙₐ[ℂ] AdjointableMap D G G)
  (J : GradedHilbertModule δB E) (K : GradedHilbertModule δC F)
  (hφ : ModuleTensorRepresentationGraded (δB := δB) φ K)

local instance kasparovTripleResidualLocalityLocalInstance1 : PartialOrder (AdjointableMap D
    (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ)) := CStarAlgebra.spectralOrder _
local instance kasparovTripleResidualLocalityLocalInstance2 : StarOrderedRing (AdjointableMap D
    (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ)) := CStarAlgebra.spectralOrderedRing _
local instance kasparovTripleResidualLocalityLocalInstance3 : PartialOrder (AdjointableMap D
    (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ)) := CStarAlgebra.spectralOrder _
local instance kasparovTripleResidualLocalityLocalInstance4 : StarOrderedRing (AdjointableMap D
    (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ)) := CStarAlgebra.spectralOrderedRing _
local instance kasparovTripleResidualLocalityLocalInstance5 : PartialOrder (AdjointableMap D
    (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ)) := CStarAlgebra.spectralOrder _
local instance kasparovTripleResidualLocalityLocalInstance6 : StarOrderedRing (AdjointableMap D
    (LeftTensor (E := E) φ ψ) (LeftTensor (E := E) φ ψ)) := CStarAlgebra.spectralOrderedRing _

def tripleAnticommutator
    (Q : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ))
    (R : AdjointableMap D (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ)) :=
  pairLift φ ψ Q * R + R * pairLift φ ψ Q

def middleAnticommutator (S : AdjointableMap C F F)
    (T : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ)) :=
  interiorModuleTensorOperator ψ S * T + T * interiorModuleTensorOperator ψ S

theorem tripleAnticommutator_selfadjoint
    (Q : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ))
    (R : AdjointableMap D (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ))
    (hQ : IsSelfAdjoint Q) (hR : IsSelfAdjoint R) :
    IsSelfAdjoint (tripleAnticommutator φ ψ Q R) := by
  have hlift : IsSelfAdjoint (pairLift φ ψ Q) := by
    change star ((hilbertEquiv φ ψ).transport (interiorModuleTensorOperatorHom ψ Q)) =
      (hilbertEquiv φ ψ).transport (interiorModuleTensorOperatorHom ψ Q)
    rw [← HilbertModuleEquiv.transport_star, ← map_star, hQ.star_eq]
  change star (_ + _) = _
  simp only [star_add, star_mul, hlift.star_eq, hR.star_eq]
  exact add_comm _ _

theorem middleAnticommutator_selfadjoint (S : AdjointableMap C F F)
    (T : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ))
    (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (middleAnticommutator ψ S T) := by
  have hlift : IsSelfAdjoint (interiorModuleTensorOperator ψ S) := by
    change star (interiorModuleTensorOperatorHom ψ S) = interiorModuleTensorOperatorHom ψ S
    rw [← map_star, hS.star_eq]
  change star (_ + _) = _
  simp only [star_add, star_mul, hlift.star_eq, hT.star_eq]
  exact add_comm _ _

/-- Both residual localities are derived from the three actual
connections and the second-pair product's localized positivity. -/
theorem residual_creation_localities
    (Q : AdjointableMap C (InteriorModuleTensor (E := E) φ) (InteriorModuleTensor (E := E) φ))
    (S : AdjointableMap C F F)
    (R : AdjointableMap D (RightTensor (E := E) φ ψ) (RightTensor (E := E) φ ψ))
    (T : AdjointableMap D (InteriorModuleTensor (E := F) ψ) (InteriorModuleTensor (E := F) ψ))
    (U : AdjointableMap D G G)
    (hQ : IsSignedModuleConnection J φ S Q)
    (hR : IsSignedModuleConnection J (rightRepresentation φ ψ) T R)
    (hT : IsSignedModuleConnection K ψ U T)
    (hQodd : (J.interiorTensor K hφ).IsOdd (J.interiorTensor K hφ) Q)
    (hSodd : K.IsOdd K S)
    (hQsa : IsSelfAdjoint Q) (hSsa : IsSelfAdjoint S)
    (hRsa : IsSelfAdjoint R) (hTsa : IsSelfAdjoint T)
    (hScomm : ∀ b, IsModuleCompact (S * φ b - φ (δB.automorphism b) * S))
    (hTcomm : ∀ b, IsModuleCompact (T * rightRepresentation φ ψ b -
      rightRepresentation φ ψ (δB.automorphism b) * T))
    (hpositive : ∀ b, IsPositiveModuloModuleCompact
      (rightRepresentation φ ψ b * middleAnticommutator ψ S T * star (rightRepresentation φ ψ b))) :
    IsCreationLocallyCompact (rightRepresentation φ ψ)
      (tripleAnticommutator φ ψ Q R - (tripleAnticommutator φ ψ Q R)⁺) ∧
    IsCreationLocallyCompact ψ ((hilbertEquiv (E := E) φ ψ).symm.transport
      (tripleAnticommutator φ ψ Q R - (tripleAnticommutator φ ψ Q R)⁺)) := by
  let Ω := hilbertEquiv (E := E) φ ψ
  let anti := tripleAnticommutator φ ψ Q R
  let middle := middleAnticommutator ψ S T
  have hAsa : IsSelfAdjoint anti := tripleAnticommutator_selfadjoint φ ψ Q R hQsa hRsa
  have hBsa : IsSelfAdjoint middle := middleAnticommutator_selfadjoint ψ S T hSsa hTsa
  have hBcomm (b : B) : IsModuleCompact (middle * rightRepresentation φ ψ b - rightRepresentation φ ψ b * middle) := by
    exact gradedTensorAnticommutator_commutator_isModuleCompact K φ hφ ψ S hSodd U T hT hScomm hTcomm b
  have hconn (x : E) : IsModuleCompact (anti.comp (moduleCreationMap (rightRepresentation φ ψ) x) -
      (moduleCreationMap (rightRepresentation φ ψ) x).comp middle) :=
    anticommutator_connection_compact φ ψ J K hφ Q S R T U hQ hR hT hQodd hSodd x
  have hfirst := creation_sub_posPart_isCreationLocallyCompact (rightRepresentation φ ψ)
    anti middle hAsa hBsa hconn hBcomm hpositive
  have hL : Ω.symm.transport anti = interiorModuleTensorOperator ψ Q * Ω.symm.transport R +
      Ω.symm.transport R * interiorModuleTensorOperator ψ Q := by
    have hlift : Ω.symm.transport (pairLift φ ψ Q) = interiorModuleTensorOperator ψ Q := by
      change Ω.symm.transport (Ω.transport (interiorModuleTensorOperator ψ Q)) =
        interiorModuleTensorOperator ψ Q
      exact Ω.transport_symm _
    simp only [anti, tripleAnticommutator, HilbertModuleEquiv.transport_add,
      HilbertModuleEquiv.transport_mul, hlift]
  have hLsa : IsSelfAdjoint (Ω.symm.transport anti) := by
    change star (Ω.symm.transport anti) = _
    rw [← HilbertModuleEquiv.transport_star, hAsa.star_eq]
  have hzero : IsCreationLocallyCompact ψ (Ω.symm.transport anti) := by
    apply IsCreationLocallyCompact.of_selfadjoint hLsa
    intro u
    rw [hL]
    exact anticommutator_pair_creation_compact φ ψ J K hφ Q R T U hR hT hQodd u
  have hpart : Ω.symm.transport anti⁺ = (Ω.symm.transport anti)⁺ := by
    let σ := Ω.symm.transportStarAlgEquiv
    have hσ : Continuous σ := (NonUnitalStarAlgHom.isometry σ σ.injective).continuous
    have hcfc := NonUnitalStarAlgHomClass.map_cfcₙ σ (fun s : ℝ => max s 0) anti
      (continuous_id.max continuous_const).continuousOn (by simp) hσ hAsa hLsa
    change Ω.symm.transport (cfcₙ (fun s : ℝ => max s 0) anti) =
      cfcₙ (fun s : ℝ => max s 0) (Ω.symm.transport anti) at hcfc
    simpa only [CFC.posPart_def, _root_.posPart_def] using hcfc
  refine ⟨hfirst, ?_⟩
  rw [HilbertModuleEquiv.transport_sub, hpart]
  exact hzero.sub_posPart hLsa

end BC4lean.KKTheory.KasparovTriple
