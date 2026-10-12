import BC4lean.RectangularFredholmStandardFibreIndex
import BC4lean.OddFredholmFullIntervalIndex

/-! # Actual rectangular Fredholm index on arbitrary interval modules

The generic module-fibre and augmentation unitaries already constructed for
the odd index are genuine Hilbert-module unitaries and are reused here.
Evaluate the two actual global frame absorptions once. Their endpoint maps
transport the whole rectangular augmentation to the actual fibre of the
globally stabilized operator. Absorption independence compares these maps
with the selected endpoint absorptions; genuine standard finite evaluation
then proves endpoint equality on arbitrary interval modules.
-/

noncomputable section
namespace BC4lean.KKTheory
open unitInterval
open scoped CStarAlgebra

section Transport
variable {B E F E' F' E'' F'' : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [SMul Bᵐᵒᵖ E'] [CStarModule Bᵐᵒᵖ E']
  [NormedAddCommGroup F'] [NormedSpace ℂ F'] [SMul Bᵐᵒᵖ F'] [CStarModule Bᵐᵒᵖ F']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] [SMul Bᵐᵒᵖ E''] [CStarModule Bᵐᵒᵖ E'']
  [NormedAddCommGroup F''] [NormedSpace ℂ F''] [SMul Bᵐᵒᵖ F''] [CStarModule Bᵐᵒᵖ F'']

theorem rectangularFredholmTransportMap_trans (u : HilbertModuleEquiv B E E')
    (u' : HilbertModuleEquiv B E' E'') (v : HilbertModuleEquiv B F F')
    (v' : HilbertModuleEquiv B F' F'') (T : AdjointableMap B E F) :
    (u.trans u').transportMap (v.trans v') T = u'.transportMap v' (u.transportMap v T) := by
  apply AdjointableMap.ext
  intro x
  rfl

end Transport

section FibreTransport
variable {B X M N M' N' : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]
  [NormedAddCommGroup N] [NormedSpace ℂ N] [SMul C(X, B)ᵐᵒᵖ N] [CStarModule C(X, B)ᵐᵒᵖ N] [CompleteSpace N]
  [NormedAddCommGroup M'] [NormedSpace ℂ M'] [SMul C(X, B)ᵐᵒᵖ M'] [CStarModule C(X, B)ᵐᵒᵖ M'] [CompleteSpace M']
  [NormedAddCommGroup N'] [NormedSpace ℂ N'] [SMul C(X, B)ᵐᵒᵖ N'] [CStarModule C(X, B)ᵐᵒᵖ N'] [CompleteSpace N']

/-- The actual rectangular fibre functor respects both whole module unitaries. -/
theorem rectangularFredholmModuleFibreEquiv_transportMap
    (u : HilbertModuleEquiv C(X, B) M M') (v : HilbertModuleEquiv C(X, B) N N')
    (t : X) (T : AdjointableMap C(X, B) M N) :
    (oddFredholmModuleFibreEquiv u t).transportMap (oddFredholmModuleFibreEquiv v t)
      (hilbertModuleFibreRectangularMap t T) =
        hilbertModuleFibreRectangularMap t (u.transportMap v T) := by
  apply AdjointableMap.ext
  intro z
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B) (M := M') t z
  change oddFredholmModuleFibreForward v t
    (hilbertModuleFibreRectangularMap t T
      (oddFredholmModuleFibreForward u.symm t (hilbertModuleFibreMk (B := B) t x))) = _
  simp only [oddFredholmModuleFibreForward, hilbertModuleFibreRectangularMap_mk,
    HilbertModuleEquiv.toAdjointable_apply, HilbertModuleEquiv.transportMap_apply]

end FibreTransport

variable {B M N : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(I, B)ᵐᵒᵖ M] [CStarModule C(I, B)ᵐᵒᵖ M] [CompleteSpace M]
  [NormedAddCommGroup N] [NormedSpace ℂ N] [SMul C(I, B)ᵐᵒᵖ N] [CStarModule C(I, B)ᵐᵒᵖ N] [CompleteSpace N]

/-- The actual rectangular map between the two completed coefficient fibres. -/
def rectangularFredholmFibre (t : I) (T : AdjointableMap C(I, B) M N) :
    AdjointableMap B (HilbertModuleFibre B M t) (HilbertModuleFibre B N t) :=
      hilbertModuleFibreRectangularMap t T

theorem rectangularFredholmFibre_source_defect (t : I) (T : AdjointableMap C(I, B) M N)
    (hs : IsModuleCompact (1 - T.adjoint.comp T)) :
    IsModuleCompact (1 - (rectangularFredholmFibre t T).adjoint.comp (rectangularFredholmFibre t T)) := by
  have h := hs.fibre t
  change IsModuleCompact (hilbertModuleFibreOperator (B := B) (M := M) t
    (1 - T.adjoint.comp T)) at h
  rw [hilbertModuleFibreOperator_sub, hilbertModuleFibreOperator_one] at h
  simpa only [rectangularFredholmFibre, ← hilbertModuleFibreRectangularMap_eq_operator,
    hilbertModuleFibreRectangularMap_comp, ← hilbertModuleFibreRectangularMap_adjoint] using h

theorem rectangularFredholmFibre_target_defect (t : I) (T : AdjointableMap C(I, B) M N)
    (ht : IsModuleCompact (T.comp T.adjoint - 1)) :
    IsModuleCompact ((rectangularFredholmFibre t T).comp (rectangularFredholmFibre t T).adjoint - 1) := by
  have h := ht.fibre t
  change IsModuleCompact (hilbertModuleFibreOperator (B := B) (M := N) t
    (T.comp T.adjoint - 1)) at h
  rw [hilbertModuleFibreOperator_sub, hilbertModuleFibreOperator_one] at h
  simpa only [rectangularFredholmFibre, ← hilbertModuleFibreRectangularMap_eq_operator,
    hilbertModuleFibreRectangularMap_comp, ← hilbertModuleFibreRectangularMap_adjoint] using h

omit [CompleteSpace M] in
set_option maxHeartbeats 1200000 in
/-- The genuine augmentation unitary on a canonical completed-fibre vector. -/
private theorem rectangularAugmentationFibreEquiv_mk (t : I)
    (x : HilbertModuleSum C(I, B) M (StandardCountableHilbertModule C(I, B))) :
    oddFredholmAugmentationFibreEquiv (B := B) (M := M) t
      (hilbertModuleFibreMk (B := B) t x) =
        sumMk (hilbertModuleFibreMk (B := B) t x.fst)
          (standardCountableCoefficientEvaluation (B := B) t x.snd) := by
  simp only [oddFredholmAugmentationFibreEquiv, HilbertModuleEquiv.trans_apply,
    HilbertModuleEquiv.sum_apply, hilbertModuleFibreSumEquiv_mk,
    standardCountableModuleFibreEquiv_mk, HilbertModuleEquiv.refl_apply,
    sumMk_fst, sumMk_snd]

set_option maxHeartbeats 4000000 in
/-- The two augmentation fibre unitaries evaluate the actual rectangular sum. -/
theorem rectangularFredholmAugmentationFibreEquiv_operator (t : I)
    (T : AdjointableMap C(I, B) M N) :
    (oddFredholmAugmentationFibreEquiv (M := M) t).transportMap
      (oddFredholmAugmentationFibreEquiv (M := N) t)
      (hilbertModuleFibreRectangularMap t (augmentedRectangularFredholm T)) =
        augmentedRectangularFredholm (rectangularFredholmFibre t T) := by
  let U := oddFredholmAugmentationFibreEquiv (B := B) (M := M) t
  let V := oddFredholmAugmentationFibreEquiv (B := B) (M := N) t
  let A := hilbertModuleFibreRectangularMap (B := B) t (augmentedRectangularFredholm T)
  let D := augmentedRectangularFredholm (rectangularFredholmFibre t T)
  have hintertwine (v : HilbertModuleSum C(I, B) M
      (StandardCountableHilbertModule C(I, B))) :
      V (A (hilbertModuleFibreMk (B := B) t v)) =
        D (U (hilbertModuleFibreMk (B := B) t v)) := by
    have hmap : A (hilbertModuleFibreMk (B := B) t v) =
        hilbertModuleFibreMk (B := B) t (augmentedRectangularFredholm T v) :=
      hilbertModuleFibreRectangularMap_mk (B := B) t (augmentedRectangularFredholm T) v
    have hglobal : augmentedRectangularFredholm T v =
        sumMk (B := C(I, B)) (T v.fst) v.snd := by
      simp only [augmentedRectangularFredholm, sumMap_apply, AdjointableMap.one_apply]
    have hsource : U (hilbertModuleFibreMk (B := B) t v) =
        sumMk (B := B) (hilbertModuleFibreMk (B := B) t v.fst)
          (standardCountableCoefficientEvaluation (B := B) t v.snd) :=
      rectangularAugmentationFibreEquiv_mk (B := B) (M := M) t v
    have htarget : V (hilbertModuleFibreMk (B := B) t
        (sumMk (B := C(I, B)) (T v.fst) v.snd)) =
        sumMk (B := B) (hilbertModuleFibreMk (B := B) t (T v.fst))
          (standardCountableCoefficientEvaluation (B := B) t v.snd) :=
      rectangularAugmentationFibreEquiv_mk (B := B) (M := N) t
        (sumMk (B := C(I, B)) (T v.fst) v.snd)
    have hleft : V (A (hilbertModuleFibreMk (B := B) t v)) =
        sumMk (B := B) (hilbertModuleFibreMk (B := B) t (T v.fst))
          (standardCountableCoefficientEvaluation (B := B) t v.snd) :=
      (congrArg (fun y : HilbertModuleFibre B
        (HilbertModuleSum C(I, B) N (StandardCountableHilbertModule C(I, B))) t => V y)
        hmap).trans
        ((congrArg (fun y : HilbertModuleSum C(I, B) N
          (StandardCountableHilbertModule C(I, B)) =>
            V (hilbertModuleFibreMk (B := B) t y)) hglobal).trans htarget)
    have hfibre : D (sumMk (B := B) (hilbertModuleFibreMk (B := B) t v.fst)
        (standardCountableCoefficientEvaluation (B := B) t v.snd)) =
        sumMk (B := B)
          (hilbertModuleFibreRectangularMap (B := B) t T
            (hilbertModuleFibreMk (B := B) t v.fst))
          (standardCountableCoefficientEvaluation (B := B) t v.snd) := by
      simp only [D, augmentedRectangularFredholm, sumMap_apply, sumMk_fst, sumMk_snd,
        AdjointableMap.one_apply, rectangularFredholmFibre]
    have hcoordinate : sumMk (B := B)
        (hilbertModuleFibreRectangularMap (B := B) t T
          (hilbertModuleFibreMk (B := B) t v.fst))
        (standardCountableCoefficientEvaluation (B := B) t v.snd) =
        sumMk (B := B) (hilbertModuleFibreMk (B := B) t (T v.fst))
          (standardCountableCoefficientEvaluation (B := B) t v.snd) :=
      congrArg (fun y : HilbertModuleFibre B N t =>
        sumMk (B := B) y (standardCountableCoefficientEvaluation (B := B) t v.snd))
        (hilbertModuleFibreRectangularMap_mk (B := B) t T v.fst)
    exact hleft.trans
      ((congrArg (fun y : HilbertModuleSum B (HilbertModuleFibre B M t)
        (StandardCountableHilbertModule B) => D y) hsource).trans
          (hfibre.trans hcoordinate)).symm
  apply AdjointableMap.ext
  intro x
  let z := U.symm x
  obtain ⟨v, hv⟩ := hilbertModuleFibreMk_surjective (B := B)
    (M := HilbertModuleSum C(I, B) M (StandardCountableHilbertModule C(I, B))) t z
  have hsource : U (hilbertModuleFibreMk (B := B) t v) = x :=
    (congrArg (fun y : HilbertModuleFibre B
      (HilbertModuleSum C(I, B) M (StandardCountableHilbertModule C(I, B))) t => U y)
      hv).trans (U.apply_symm_apply x)
  calc
    (oddFredholmAugmentationFibreEquiv (M := M) t).transportMap
        (oddFredholmAugmentationFibreEquiv (M := N) t)
        (hilbertModuleFibreRectangularMap t (augmentedRectangularFredholm T)) x =
        V (A z) := HilbertModuleEquiv.transportMap_apply U V A x
    _ = V (A (hilbertModuleFibreMk (B := B) t v)) :=
      congrArg (fun y : HilbertModuleFibre B
        (HilbertModuleSum C(I, B) M (StandardCountableHilbertModule C(I, B))) t => V (A y)) hv.symm
    _ = D (U (hilbertModuleFibreMk (B := B) t v)) := hintertwine v
    _ = D x := congrArg (fun y : HilbertModuleSum B (HilbertModuleFibre B M t)
      (StandardCountableHilbertModule B) => D y) hsource

set_option maxHeartbeats 1200000 in
/-- The actual endpoint absorptions evaluate the globally stabilized rectangular map. -/
theorem rectangularFredholmEndpointAbsorption_operator
    (hM : IsCountablyGeneratedModule C(I, B) M) (hN : IsCountablyGeneratedModule C(I, B) N)
    (t : I) (T : AdjointableMap C(I, B) M N) :
    (oddFredholmEndpointAbsorption hM t).transportMap (oddFredholmEndpointAbsorption hN t)
      (augmentedRectangularFredholm (rectangularFredholmFibre t T)) =
        standardCountableFibreOperatorHom t (standardStabilizedRectangularFredholm T hM hN) := by
  rw [oddFredholmEndpointAbsorption, oddFredholmEndpointAbsorption,
    rectangularFredholmTransportMap_trans,
    ← rectangularFredholmAugmentationFibreEquiv_operator t T,
    HilbertModuleEquiv.transportMap_symm]
  let U := standardModuleStabilization (B := C(I, B)) (E := M) hM
  let V := standardModuleStabilization (B := C(I, B)) (E := N) hN
  let W := standardCountableModuleFibreEquiv (B := B) t
  change ((oddFredholmModuleFibreEquiv (B := B) U t).trans W).transportMap
      ((oddFredholmModuleFibreEquiv (B := B) V t).trans W)
      (hilbertModuleFibreRectangularMap t (augmentedRectangularFredholm T)) = _
  rw [rectangularFredholmTransportMap_trans,
    rectangularFredholmModuleFibreEquiv_transportMap,
    hilbertModuleFibreRectangularMap_eq_operator]
  rfl

/-- The selected actual fibre index equals the evaluated globally stabilized index. -/
theorem rectangularFredholmIndex_fibre
    (hM : IsCountablyGeneratedModule C(I, B) M) (hN : IsCountablyGeneratedModule C(I, B) N)
    (t : I) (T : AdjointableMap C(I, B) M N)
    (hs : IsModuleCompact (1 - T.adjoint.comp T)) (ht : IsModuleCompact (T.comp T.adjoint - 1)) :
    rectangularFredholmIndex (rectangularFredholmFibre t T) (hM.fibre t) (hN.fibre t)
        (rectangularFredholmFibre_source_defect t T hs) (rectangularFredholmFibre_target_defect t T ht) =
      standardNormalizedRectangularFredholmIndex
        (standardCountableFibreOperatorHom t (standardStabilizedRectangularFredholm T hM hN))
        (standardCountableFibreFredholm_source_defect t _
          (standardStabilizedRectangularFredholm_source_defect T hM hN hs))
        (standardCountableFibreFredholm_target_defect t _
          (standardStabilizedRectangularFredholm_target_defect T hM hN ht)) := by
  rw [rectangularFredholmIndex_absorption_independent _ _ _ _ _
    (oddFredholmEndpointAbsorption hM t) (oddFredholmEndpointAbsorption hN t)]
  unfold rectangularFredholmIndexWith
  simp only [rectangularFredholmEndpointAbsorption_operator]

/-- Actual completed endpoint fibre indices agree for every arbitrary complete
countably generated rectangular Fredholm interval module. -/
theorem rectangularFredholmFullIntervalIndex_endpoints
    (hM : IsCountablyGeneratedModule C(I, B) M) (hN : IsCountablyGeneratedModule C(I, B) N)
    (T : AdjointableMap C(I, B) M N)
    (hs : IsModuleCompact (1 - T.adjoint.comp T)) (ht : IsModuleCompact (T.comp T.adjoint - 1)) :
    rectangularFredholmIndex (rectangularFredholmFibre (0 : I) T) (hM.fibre 0) (hN.fibre 0)
        (rectangularFredholmFibre_source_defect 0 T hs) (rectangularFredholmFibre_target_defect 0 T ht) =
      rectangularFredholmIndex (rectangularFredholmFibre (1 : I) T) (hM.fibre 1) (hN.fibre 1)
        (rectangularFredholmFibre_source_defect 1 T hs) (rectangularFredholmFibre_target_defect 1 T ht) := by
  rw [rectangularFredholmIndex_fibre (B := B) (M := M) (N := N) hM hN (0 : I) T hs ht,
    rectangularFredholmIndex_fibre (B := B) (M := M) (N := N) hM hN (1 : I) T hs ht]
  exact standardNormalizedRectangularFredholmIndex_fibre_endpoints
    (standardStabilizedRectangularFredholm T hM hN)
    (standardStabilizedRectangularFredholm_source_defect T hM hN hs)
    (standardStabilizedRectangularFredholm_target_defect T hM hN ht)

end BC4lean.KKTheory
