import BC4lean.CliffordOddConditionalPauli
import BC4lean.CliffordPairSecondTensorCompatibility
import BC4lean.CliffordOddBalancedTensorConnection
import Mathlib.Tactic.Module

/-! # All-vector connection defects under the conditional Pauli unitary

The exact defect is a rectangular matrix of the original signed defects
on the genuine even and odd parts. This proves compactness for arbitrary
pair vectors, and hence all four homogeneous connection laws. The second
operator and its star remain separate throughout.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordOddConditionalConnection
open CliffordExternalEvenBalancedTensor
open CliffordOddConditionalPauli

variable {B C E F : Type*}
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
  (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E)

abbrev K := CliffordPairSecondTensor.baseGrading φ J
abbrev Tensor := InteriorModuleTensor (E := E) φ

local instance cliffordOddConditionalConnectionLocalInstance1 : CompleteSpace (HilbertModuleSum C F F) := hilbertModuleSum_complete
local instance cliffordOddConditionalConnectionLocalInstance2 : CompleteSpace (HilbertModuleSum C (Tensor (E := E) φ) (Tensor (E := E) φ)) := hilbertModuleSum_complete

/-- These are actual completed tensor identities, derived from elementary
creator evaluation and the proved tensor grading. -/
theorem plus_creation_apply (x : E) (y : F) :
    plus (K φ J) (moduleCreationMap φ x y) =
      moduleCreationMap φ (J.evenPart x) y := by
  change (2 : ℂ)⁻¹ •
    (interiorModuleTensorMk φ x y +
      (CliffordPairSecondTensor.baseGrading φ J).grading
        (interiorModuleTensorMk φ x y)) =
    interiorModuleTensorMk φ (J.evenPart x) y
  rw [CliffordPairSecondTensor.baseGrading_mk]
  rw [GradedHilbertModule.evenPart]
  have hs := LinearMap.congr_fun
    ((interiorModuleTensorMk (E := E) φ).map_smul (2 : ℂ)⁻¹ (x + J.grading x)) y
  have ha := LinearMap.congr_fun
    ((interiorModuleTensorMk (E := E) φ).map_add x (J.grading x)) y
  change interiorModuleTensorMk φ ((2 : ℂ)⁻¹ • (x + J.grading x)) y =
    (2 : ℂ)⁻¹ • interiorModuleTensorMk φ (x + J.grading x) y at hs
  change interiorModuleTensorMk φ (x + J.grading x) y =
    interiorModuleTensorMk φ x y + interiorModuleTensorMk φ (J.grading x) y at ha
  rw [ha] at hs
  exact hs.symm

theorem minus_creation_apply (x : E) (y : F) :
    minus (K φ J) (moduleCreationMap φ x y) =
      moduleCreationMap φ (J.oddPart x) y := by
  simp only [minus, CliffordOne.minusProjection, AdjointableMap.coe_smul_apply,
    AdjointableMap.coe_sub_apply, AdjointableMap.one_apply,
    GradedHilbertModule.toAdjointable_apply, moduleCreationMap_apply]
  change (2 : ℂ)⁻¹ •
    (interiorModuleTensorMk φ x y -
      (CliffordPairSecondTensor.baseGrading φ J).grading
        (interiorModuleTensorMk φ x y)) =
    interiorModuleTensorMk φ (J.oddPart x) y
  rw [CliffordPairSecondTensor.baseGrading_mk]
  rw [GradedHilbertModule.oddPart]
  have hs := LinearMap.congr_fun
    ((interiorModuleTensorMk (E := E) φ).map_smul (2 : ℂ)⁻¹ (x - J.grading x)) y
  have ha := LinearMap.congr_fun
    ((interiorModuleTensorMk (E := E) φ).map_sub x (J.grading x)) y
  change interiorModuleTensorMk φ ((2 : ℂ)⁻¹ • (x - J.grading x)) y =
    (2 : ℂ)⁻¹ • interiorModuleTensorMk φ (x - J.grading x) y at hs
  change interiorModuleTensorMk φ (x - J.grading x) y =
    interiorModuleTensorMk φ x y - interiorModuleTensorMk φ (J.grading x) y at ha
  rw [ha] at hs
  exact hs.symm

variable (G : AdjointableMap C (Tensor (E := E) φ) (Tensor (E := E) φ)) (D : AdjointableMap C F F)

def signedDefect (x : E) : AdjointableMap C F (Tensor (E := E) φ) :=
  G.comp (moduleCreationMap φ x) - (moduleCreationMap φ (J.grading x)).comp D

def candidate : AdjointableMap C (HilbertModuleSum C (Tensor (E := E) φ) (Tensor (E := E) φ))
    (HilbertModuleSum C (Tensor (E := E) φ) (Tensor (E := E) φ)) :=
  (CliffordOddConditionalPauli.hilbertEquiv (K φ J)).transport
    (CliffordOddSourceCycle.operator G)

/-- The genuine rectangular block expression of the complete defect. -/
def blockDefect (x : CliffordPairModule B E) :
    AdjointableMap C (HilbertModuleSum C F F) (HilbertModuleSum C (Tensor (E := E) φ) (Tensor (E := E) φ)) :=
  ((sumInl.comp (signedDefect φ J G D (J.oddPart x.1))).comp sumFst) +
    (-Complex.I) • ((sumInl.comp (signedDefect φ J G D (J.evenPart x.2))).comp sumSnd) +
    Complex.I • ((sumInr.comp (signedDefect φ J G D (J.evenPart x.1))).comp sumFst) +
    ((sumInr.comp (signedDefect φ J G D (J.oddPart x.2))).comp sumSnd)

/-- This exact identity retains every original pair vector and its full
signed grading. No equality of the two vector coordinates is imposed. -/
theorem creation_defect (x : CliffordPairModule B E) :
    (CliffordOddConditionalPauli.hilbertEquiv (K φ J)).toAdjointable.comp
      ((candidate φ J G).comp (CliffordOddBalancedTensor.coordinateCreation φ x) -
        (CliffordOddBalancedTensor.coordinateCreation φ
          (cliffordPairMk (B := B) (J.grading x.2) (J.grading x.1))).comp
            (CliffordOddSourceCycle.operator D)) = blockDefect φ J G D x := by
  have hcoord (z : CliffordPairModule B E) (v : HilbertModuleSum C F F) :
      CliffordOddBalancedTensor.coordinateCreation φ z v =
        sumMk (moduleCreationMap φ z.1 v.fst) (moduleCreationMap φ z.2 v.snd) := by
    simp only [CliffordOddBalancedTensor.coordinateCreation, sumMap_apply]
  have hUT (z : CliffordPairModule B E) (v : HilbertModuleSum C F F) :
      CliffordOddConditionalPauli.operator (K φ J)
          (CliffordOddBalancedTensor.coordinateCreation φ z v) =
        sumMk
          (moduleCreationMap φ (J.evenPart z.1) v.fst +
            (-Complex.I) • moduleCreationMap φ (J.oddPart z.2) v.snd)
          (Complex.I • moduleCreationMap φ (J.oddPart z.1) v.fst +
            moduleCreationMap φ (J.evenPart z.2) v.snd) := by
    rw [hcoord, CliffordOddConditionalPauli.operator_apply]
    simp only [sumMk_fst, sumMk_snd, plus_creation_apply, minus_creation_apply]
  have heven (z : E) : J.evenPart (J.grading z) = J.evenPart z := by
    simp only [GradedHilbertModule.evenPart, J.grading_sq]
    rw [add_comm]
  have hodd (z : E) : J.oddPart (J.grading z) = -J.oddPart z := by
    simp only [GradedHilbertModule.oddPart, J.grading_sq]
    rw [← smul_neg, neg_sub]
  have hGa (u v : Tensor (E := E) φ) : G (u + v) = G u + G v :=
    map_add G.toCLM u v
  have hGs (a : ℂ) (u : Tensor (E := E) φ) : G (a • u) = a • G u :=
    map_smul G.toCLM a u
  have hTs (z : E) (a : ℂ) (v : F) :
      moduleCreationMap φ z (a • v) = a • moduleCreationMap φ z v :=
    map_smul (moduleCreationMap φ z).toCLM a v
  have hGUT (z : CliffordPairModule B E) (v : HilbertModuleSum C F F) :
      CliffordOddSourceCycle.operator G
        (CliffordOddConditionalPauli.operator (K φ J)
          (CliffordOddBalancedTensor.coordinateCreation φ z v)) =
        sumMk
          (G (moduleCreationMap φ (J.oddPart z.1) v.fst) +
            (-Complex.I) • G (moduleCreationMap φ (J.evenPart z.2) v.snd))
          (Complex.I • G (moduleCreationMap φ (J.evenPart z.1) v.fst) +
            G (moduleCreationMap φ (J.oddPart z.2) v.snd)) := by
    rw [hUT, CliffordOddSourceCycle.operator_apply]
    simp only [sumMk_fst, sumMk_snd, hGa, hGs, smul_add, smul_smul,
      neg_mul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  have hSigmaD (z : CliffordPairModule B E) (v : HilbertModuleSum C F F) :
      CliffordOddConditionalPauli.operator (K φ J)
        (CliffordOddBalancedTensor.coordinateCreation φ
          (cliffordPairMk (B := B) (J.grading z.2) (J.grading z.1))
          (CliffordOddSourceCycle.operator D v)) =
        sumMk
          (-moduleCreationMap φ (J.oddPart z.1) (D v.fst) +
            (-Complex.I) • moduleCreationMap φ (J.evenPart z.2) (D v.snd))
          (Complex.I • moduleCreationMap φ (J.evenPart z.1) (D v.fst) -
            moduleCreationMap φ (J.oddPart z.2) (D v.snd)) := by
    rw [hUT, CliffordOddSourceCycle.operator_apply]
    apply Prod.ext <;>
      simp only [sumMk_fst, sumMk_snd, cliffordPairMk, heven, hodd,
        moduleCreationMap_neg, AdjointableMap.coe_neg_apply, hTs,
        smul_neg, smul_smul, neg_mul, mul_neg, Complex.I_mul_I, neg_neg, one_smul] <;>
      module
  ext y
  simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
    HilbertModuleEquiv.toAdjointable_apply,
    CliffordOddConditionalPauli.hilbertEquiv_apply]
  rw [map_sub]
  simp only [candidate, HilbertModuleEquiv.transport_apply,
    CliffordOddConditionalPauli.hilbertEquiv_apply,
    CliffordOddConditionalPauli.hilbertEquiv_symm_apply, operator_involutive]
  rw [hGUT, hSigmaD]
  apply Prod.ext <;>
    simp only [blockDefect, signedDefect, AdjointableMap.coe_add_apply,
      AdjointableMap.coe_sub_apply, AdjointableMap.coe_smul_apply,
      AdjointableMap.coe_neg_apply, AdjointableMap.comp_apply,
      sumInl_apply, sumInr_apply, sumFst_apply, sumSnd_apply,
      WithCStarModule.add_fst, WithCStarModule.add_snd,
      WithCStarModule.sub_fst, WithCStarModule.sub_snd,
      WithCStarModule.smul_fst, WithCStarModule.smul_snd,
      sumMk_fst, sumMk_snd, GradedHilbertModule.grading_evenPart,
      GradedHilbertModule.grading_oddPart, moduleCreationMap_neg,
      smul_zero, zero_add, add_zero] <;> module

theorem compact_blockDefect
    (h : ∀ x : E, IsModuleCompact (signedDefect φ J G D x))
    (x : CliffordPairModule B E) : IsModuleCompact (blockDefect φ J G D x) :=
  (((((h (J.oddPart x.1)).comp_left sumInl).comp_right sumFst).add
    ((((h (J.evenPart x.2)).comp_left sumInl).comp_right sumSnd).smul (-Complex.I))).add
    ((((h (J.evenPart x.1)).comp_left sumInr).comp_right sumFst).smul Complex.I)).add
    (((h (J.oddPart x.2)).comp_left sumInr).comp_right sumSnd)

/-- Onto-ness of the actual coefficient-form Pauli unitary carries the
proved compact block back to the original complete coordinate carrier. -/
theorem compact_creation_defect
    (h : ∀ x : E, IsModuleCompact (signedDefect φ J G D x))
    (x : CliffordPairModule B E) :
    IsModuleCompact ((candidate φ J G).comp (CliffordOddBalancedTensor.coordinateCreation φ x) -
      (CliffordOddBalancedTensor.coordinateCreation φ
        (cliffordPairMk (B := B) (J.grading x.2) (J.grading x.1))).comp
          (CliffordOddSourceCycle.operator D)) := by
  have hc := (compact_blockDefect φ J G D h x).comp_left
    (CliffordOddConditionalPauli.hilbertEquiv (K φ J)).symm.toAdjointable
  rw [← creation_defect φ J G D x] at hc
  convert hc using 1
  ext y
  simp only [AdjointableMap.comp_apply, HilbertModuleEquiv.toAdjointable_apply,
    HilbertModuleEquiv.symm_apply_apply]

theorem candidate_star : star (candidate φ J G) = candidate φ J (star G) := by
  unfold candidate
  rw [← HilbertModuleEquiv.transport_star, CliffordOddSourceCycle.operator_star]

end BC4lean.KKTheory.CliffordOddConditionalConnection
