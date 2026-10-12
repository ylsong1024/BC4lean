import BC4lean.OddFredholmModuleFibreEquiv

/-! # Actual odd index invariance on arbitrary interval modules

Stabilize the complete countably generated C(I,B)-module once. Its genuine
evaluated absorption yields an actual absorption at every endpoint after the
proved sum-fibre and standard-fibre unitaries. Absorption independence compares
these absorptions with the selected ones. The already constructed finite
standard interval index then proves the actual endpoint equality.
-/

noncomputable section
namespace BC4lean.KKTheory
open unitInterval
open scoped CStarAlgebra

section Transport
variable {B E F G : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]

theorem oddFredholmTransport_trans (u : HilbertModuleEquiv B E F)
    (v : HilbertModuleEquiv B F G) (T : AdjointableMap B E E) :
    (u.trans v).transport T = v.transport (u.transport T) := by
  ext x
  rfl

end Transport

section SumTransport
variable {B E F G H : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G] [CStarModule Bᵐᵒᵖ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H]

theorem oddFredholmTransport_sum (u : HilbertModuleEquiv B E G)
    (v : HilbertModuleEquiv B F H) (S : AdjointableMap B E E) (T : AdjointableMap B F F) :
    (u.sum v).transport (sumMap S T) = sumMap (u.transport S) (v.transport T) := by
  have hsymm (x : HilbertModuleSum B G H) :
      (u.sum v).symm x = sumMk (u.symm x.fst) (v.symm x.snd) := by
    apply (u.sum v).injective
    simp only [HilbertModuleEquiv.apply_symm_apply, HilbertModuleEquiv.sum_apply,
      sumMk_fst, sumMk_snd, sumMk_eta]
  ext x
  simp only [HilbertModuleEquiv.transport_apply, hsymm, sumMap_apply,
    HilbertModuleEquiv.sum_apply, sumMk_fst, sumMk_snd]

end SumTransport

variable {B M : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(I, B)ᵐᵒᵖ M]
  [CStarModule C(I, B)ᵐᵒᵖ M] [CompleteSpace M]

def oddFredholmFibreSelfAdjoint (t : I) (F : selfAdjoint (AdjointableMap C(I, B) M M)) :
    selfAdjoint (AdjointableMap B (HilbertModuleFibre B M t) (HilbertModuleFibre B M t)) :=
  ⟨hilbertModuleFibreOperator (B := B) t (F : _), F.property.map (hilbertModuleFibreOperatorHom t)⟩

theorem oddFredholmFibreSelfAdjoint_square_compact (t : I)
    (F : selfAdjoint (AdjointableMap C(I, B) M M))
    (hF : IsModuleCompact ((F : AdjointableMap C(I, B) M M) * (F : AdjointableMap C(I, B) M M) - 1)) :
    IsModuleCompact ((oddFredholmFibreSelfAdjoint (B := B) (M := M) t F : AdjointableMap B
      (HilbertModuleFibre B M t) (HilbertModuleFibre B M t)) *
      (oddFredholmFibreSelfAdjoint (B := B) (M := M) t F : AdjointableMap B
        (HilbertModuleFibre B M t) (HilbertModuleFibre B M t)) - 1) := by
  simpa only [oddFredholmFibreSelfAdjoint, hilbertModuleFibreOperator_sub,
    hilbertModuleFibreOperator_mul, hilbertModuleFibreOperator_one] using hF.fibre t

/-- Split the actual augmentation fibre and identify its standard summand. -/
def oddFredholmAugmentationFibreEquiv (t : I) :
    HilbertModuleEquiv B (HilbertModuleFibre B
      (HilbertModuleSum C(I, B) M (StandardCountableHilbertModule C(I, B))) t)
      (HilbertModuleSum B (HilbertModuleFibre B M t) (StandardCountableHilbertModule B)) :=
  (hilbertModuleFibreSumEquiv (B := B) (M := M) (N := StandardCountableHilbertModule C(I, B)) t).trans
    ((HilbertModuleEquiv.refl (B := B) (E := HilbertModuleFibre B M t)).sum
      (standardCountableModuleFibreEquiv (B := B) t))

set_option maxHeartbeats 1200000 in
theorem oddFredholmAugmentationFibreEquiv_operator (t : I)
    (F : selfAdjoint (AdjointableMap C(I, B) M M)) :
    (oddFredholmAugmentationFibreEquiv (B := B) (M := M) t).transport
      (hilbertModuleFibreOperator (B := B) t (oddFredholmStandardAugmentedOperator F)) =
      oddFredholmStandardAugmentedOperator (oddFredholmFibreSelfAdjoint (B := B) (M := M) t F) := by
  let U := hilbertModuleFibreSumEquiv (B := B) (M := M)
    (N := StandardCountableHilbertModule C(I, B)) t
  let V := (HilbertModuleEquiv.refl (B := B) (E := HilbertModuleFibre B M t)).sum
    (standardCountableModuleFibreEquiv (B := B) t)
  change (U.trans V).transport (hilbertModuleFibreOperator (B := B) t
      (sumMap (F : AdjointableMap C(I, B) M M)
        (1 : AdjointableMap C(I, B) (StandardCountableHilbertModule C(I, B))
          (StandardCountableHilbertModule C(I, B))))) =
    sumMap (hilbertModuleFibreOperator (B := B) t (F : AdjointableMap C(I, B) M M)) 1
  rw [oddFredholmTransport_trans]
  rw [hilbertModuleFibreSumEquiv_transport_operator (B := B) (M := M)
    (N := StandardCountableHilbertModule C(I, B)) t
    (F : AdjointableMap C(I, B) M M)
    (1 : AdjointableMap C(I, B) (StandardCountableHilbertModule C(I, B))
      (StandardCountableHilbertModule C(I, B))),
    hilbertModuleFibreOperator_one (B := B) (M := StandardCountableHilbertModule C(I, B)) t]
  rw [oddFredholmTransport_sum, HilbertModuleEquiv.transport_one]
  rfl

/-- Evaluate the globally selected actual absorption, then use the whole
standard-module fibre equivalence. -/
def oddFredholmEvaluatedGlobalAbsorption (hM : IsCountablyGeneratedModule C(I, B) M) (t : I) :
    HilbertModuleEquiv B (HilbertModuleFibre B
      (HilbertModuleSum C(I, B) M (StandardCountableHilbertModule C(I, B))) t)
      (StandardCountableHilbertModule B) :=
  (oddFredholmModuleFibreEquiv (standardModuleStabilization (B := C(I, B)) (E := M) hM) t).trans
    (standardCountableModuleFibreEquiv (B := B) t)

/-- The actual endpoint absorption of fibre(M) ⊕ H_B derived from the one
global C(I,B) absorption, without requiring its equality to a chosen one. -/
def oddFredholmEndpointAbsorption (hM : IsCountablyGeneratedModule C(I, B) M) (t : I) :
    HilbertModuleEquiv B
      (HilbertModuleSum B (HilbertModuleFibre B M t) (StandardCountableHilbertModule B))
      (StandardCountableHilbertModule B) :=
  (oddFredholmAugmentationFibreEquiv (B := B) (M := M) t).symm.trans
    (oddFredholmEvaluatedGlobalAbsorption (B := B) (M := M) hM t)

theorem oddFredholmEndpointAbsorption_operator
    (hM : IsCountablyGeneratedModule C(I, B) M) (t : I)
    (F : selfAdjoint (AdjointableMap C(I, B) M M)) :
    (oddFredholmEndpointAbsorption (B := B) (M := M) hM t).transport
      (oddFredholmStandardAugmentedOperator (oddFredholmFibreSelfAdjoint (B := B) (M := M) t F)) =
      (oddFredholmStandardFibreSelfAdjoint t
        (oddFredholmStandardStabilizedOperator hM F) : OddFredholmStandardOperator B) := by
  rw [oddFredholmEndpointAbsorption, oddFredholmTransport_trans,
    ← oddFredholmAugmentationFibreEquiv_operator (B := B) (M := M) t F,
    HilbertModuleEquiv.transport_symm]
  let U := standardModuleStabilization (B := C(I, B)) (E := M) hM
  let V := standardCountableModuleFibreEquiv (B := B) t
  change ((oddFredholmModuleFibreEquiv (B := B) U t).trans V).transport
      (hilbertModuleFibreOperator (B := B) t (oddFredholmStandardAugmentedOperator F)) = _
  rw [oddFredholmTransport_trans]
  rw [oddFredholmModuleFibreEquiv_transport (B := B) (X := I)
    (M := HilbertModuleSum C(I, B) M (StandardCountableHilbertModule C(I, B)))
    (N := StandardCountableHilbertModule C(I, B)) U t (oddFredholmStandardAugmentedOperator F)]
  rfl

/-- The selected index of the actual fibre is the selected finite index of
the evaluated globally stabilized operator, by proved absorption independence. -/
theorem oddFredholmStabilizedIndex_fibre
    (hM : IsCountablyGeneratedModule C(I, B) M) (t : I)
    (F : selfAdjoint (AdjointableMap C(I, B) M M))
    (hF : IsModuleCompact ((F : AdjointableMap C(I, B) M M) * (F : AdjointableMap C(I, B) M M) - 1)) :
    oddFredholmStabilizedIndex (hM.fibre t) (oddFredholmFibreSelfAdjoint (B := B) (M := M) t F)
      (oddFredholmFibreSelfAdjoint_square_compact t F hF) =
      oddFredholmStandardIndex
        (oddFredholmStandardFibreSelfAdjoint t (oddFredholmStandardStabilizedOperator hM F))
        (oddFredholmStandardFibre_square_compact t (oddFredholmStandardStabilizedOperator hM F)
          (by simpa only [pow_two] using oddFredholmStandardStabilizedOperator_square_compact hM F hF)) := by
  rw [oddFredholmStabilizedIndex_eq_absorption _ _ _ (oddFredholmEndpointAbsorption (B := B) (M := M) hM t)]
  unfold oddFredholmAbsorbedIndex
  have he : oddFredholmTransportSelfAdjoint (oddFredholmEndpointAbsorption (B := B) (M := M) hM t)
      ⟨oddFredholmStandardAugmentedOperator (oddFredholmFibreSelfAdjoint (B := B) (M := M) t F),
        oddFredholmStandardAugmentedOperator_isSelfAdjoint (oddFredholmFibreSelfAdjoint (B := B) (M := M) t F)⟩ =
      oddFredholmStandardFibreSelfAdjoint t (oddFredholmStandardStabilizedOperator hM F) := by
    apply Subtype.ext
    exact oddFredholmEndpointAbsorption_operator hM t F
  congr 1

/-- Genuine exponential-index equality on the endpoints of every complete
countably generated selfadjoint Fredholm interval module. The interval module
may be arbitrary: it need not be a continuous-section module. -/
theorem oddFredholmFullIntervalIndex_endpoints
    (hM : IsCountablyGeneratedModule C(I, B) M)
    (F : selfAdjoint (AdjointableMap C(I, B) M M))
    (hF : IsModuleCompact ((F : AdjointableMap C(I, B) M M) * (F : AdjointableMap C(I, B) M M) - 1)) :
    oddFredholmStabilizedIndex (hM.fibre 0) (oddFredholmFibreSelfAdjoint 0 F)
        (oddFredholmFibreSelfAdjoint_square_compact 0 F hF) =
      oddFredholmStabilizedIndex (hM.fibre 1) (oddFredholmFibreSelfAdjoint 1 F)
        (oddFredholmFibreSelfAdjoint_square_compact 1 F hF) := by
  rw [oddFredholmStabilizedIndex_fibre (B := B) (M := M) hM (0 : I) F hF,
    oddFredholmStabilizedIndex_fibre (B := B) (M := M) hM (1 : I) F hF]
  exact oddFredholmStandardIntervalIndex_endpoints (oddFredholmStandardStabilizedOperator hM F)
    (by simpa only [pow_two] using oddFredholmStandardStabilizedOperator_square_compact hM F hF)

end BC4lean.KKTheory
