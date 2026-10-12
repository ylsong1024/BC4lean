import BC4lean.CliffordExternalEvenBalancedTensor

/-! # Actual creator formulas under the balanced external Clifford unitary

Each coordinate creator is a genuine sum of original creators composed with
the actual grading projections. The completed balanced unitary intertwines
the whole creators and their adjoints. All four homogeneous connection
errors therefore transfer by the actual rectangular compact ideal laws.
-/

noncomputable section
namespace BC4lean.KKTheory.CliffordExternalEvenBalancedTensor
open CliffordExternalEvenRepresentation

variable {B C H F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Bᵐᵒᵖ H] [CStarModule Bᵐᵒᵖ H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace H] [CompleteSpace F]
  (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
  (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading C) F)
  (hφ : ∀ b, J.toAdjointable * φ b = φ b * J.toAdjointable)

def coordinateCreation (x : CliffordPairModule B H) :
    AdjointableMap (C × C) (CliffordPairModule C F) (TargetModule (H := H) φ) :=
  cliffordPairMap
    ((moduleCreationMap φ x.1).comp (plus J) + (moduleCreationMap φ x.2).comp (minus J))
    ((moduleCreationMap φ x.1).comp (minus J) + (moduleCreationMap φ x.2).comp (plus J))

@[simp] theorem coordinateCreation_apply (x : CliffordPairModule B H) (y : CliffordPairModule C F) :
    coordinateCreation φ J x y = bilinear φ J x y := rfl

/-- This equality holds for the whole completed creator, not only a dense
algebraic domain. -/
theorem creation_operator (x : CliffordPairModule B H) :
    (hilbertEquiv φ J hφ).toAdjointable.comp (moduleCreationMap (representation φ J hφ) x) =
      coordinateCreation φ J x := by
  ext y
  exact hilbertEquiv_mk φ J hφ x y

theorem creation_apply (x : CliffordPairModule B H) (y : CliffordPairModule C F) :
    hilbertEquiv φ J hφ (moduleCreationMap (representation φ J hφ) x y) =
      coordinateCreation φ J x y :=
  congrArg (fun T : AdjointableMap (C × C) (CliffordPairModule C F) (TargetModule (H := H) φ) => T y)
    (creation_operator φ J hφ x)

/-- Adjoint compatibility follows from the genuine whole creator equality. -/
theorem creation_adjoint_operator (x : CliffordPairModule B H) :
    (coordinateCreation φ J x).adjoint =
      (moduleCreationMap (representation φ J hφ) x).adjoint.comp
        (hilbertEquiv φ J hφ).symm.toAdjointable := by
  have hh := congrArg AdjointableMap.adjoint (creation_operator φ J hφ x)
  simpa only [AdjointableMap.adjoint_comp, HilbertModuleEquiv.toAdjointable_adjoint] using hh.symm

theorem creation_adjoint_apply (x : CliffordPairModule B H) (z : TargetModule (H := H) φ) :
    (coordinateCreation φ J x).adjoint z =
      (moduleCreationMap (representation φ J hφ) x).adjoint ((hilbertEquiv φ J hφ).symm z) :=
  congrArg (fun T : AdjointableMap (C × C) (TargetModule (H := H) φ) (CliffordPairModule C F) => T z)
    (creation_adjoint_operator φ J hφ x)

theorem creator_sub_error
    (R : AdjointableMap (C × C) (SourceTensor (H := H) φ J hφ) (SourceTensor (H := H) φ J hφ))
    (D : AdjointableMap (C × C) (CliffordPairModule C F) (CliffordPairModule C F))
    (x : CliffordPairModule B H) :
    (coordinateCreation φ J x).comp D -
        ((hilbertEquiv φ J hφ).transport R).comp (coordinateCreation φ J x) =
      (hilbertEquiv φ J hφ).toAdjointable.comp
        ((moduleCreationMap (representation φ J hφ) x).comp D -
          R.comp (moduleCreationMap (representation φ J hφ) x)) := by
  ext y
  simp only [AdjointableMap.comp_apply, AdjointableMap.coe_sub_apply,
    HilbertModuleEquiv.toAdjointable_apply]
  rw [← creation_apply φ J hφ x (D y), ← creation_apply φ J hφ x y]
  simp only [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply,
    HilbertModuleEquiv.map_sub]

theorem creator_add_error
    (R : AdjointableMap (C × C) (SourceTensor (H := H) φ J hφ) (SourceTensor (H := H) φ J hφ))
    (D : AdjointableMap (C × C) (CliffordPairModule C F) (CliffordPairModule C F))
    (x : CliffordPairModule B H) :
    (coordinateCreation φ J x).comp D +
        ((hilbertEquiv φ J hφ).transport R).comp (coordinateCreation φ J x) =
      (hilbertEquiv φ J hφ).toAdjointable.comp
        ((moduleCreationMap (representation φ J hφ) x).comp D +
          R.comp (moduleCreationMap (representation φ J hφ) x)) := by
  ext y
  simp only [AdjointableMap.comp_apply, AdjointableMap.coe_add_apply,
    HilbertModuleEquiv.toAdjointable_apply]
  rw [← creation_apply φ J hφ x (D y), ← creation_apply φ J hφ x y]
  simp only [HilbertModuleEquiv.transport_apply, HilbertModuleEquiv.symm_apply_apply,
    HilbertModuleEquiv.map_add]

variable
  (R : AdjointableMap (C × C) (SourceTensor (H := H) φ J hφ) (SourceTensor (H := H) φ J hφ))
  (D : AdjointableMap (C × C) (CliffordPairModule C F) (CliffordPairModule C F))
  (x : CliffordPairModule B H)

theorem compact_creator_even
    (hc : IsModuleCompact ((moduleCreationMap (representation φ J hφ) x).comp D -
      R.comp (moduleCreationMap (representation φ J hφ) x))) :
    IsModuleCompact ((coordinateCreation φ J x).comp D -
      ((hilbertEquiv φ J hφ).transport R).comp (coordinateCreation φ J x)) := by
  rw [creator_sub_error φ J hφ]
  exact hc.comp_left _

theorem compact_creator_even_adjoint
    (hc : IsModuleCompact ((moduleCreationMap (representation φ J hφ) x).comp (star D) -
      (star R).comp (moduleCreationMap (representation φ J hφ) x))) :
    IsModuleCompact ((coordinateCreation φ J x).comp (star D) -
      (star ((hilbertEquiv φ J hφ).transport R)).comp (coordinateCreation φ J x)) := by
  simpa only [HilbertModuleEquiv.transport_star] using compact_creator_even φ J hφ (star R) (star D) x hc

theorem compact_creator_odd
    (hc : IsModuleCompact ((moduleCreationMap (representation φ J hφ) x).comp D +
      R.comp (moduleCreationMap (representation φ J hφ) x))) :
    IsModuleCompact ((coordinateCreation φ J x).comp D +
      ((hilbertEquiv φ J hφ).transport R).comp (coordinateCreation φ J x)) := by
  rw [creator_add_error φ J hφ]
  exact hc.comp_left _

theorem compact_creator_odd_adjoint
    (hc : IsModuleCompact ((moduleCreationMap (representation φ J hφ) x).comp (star D) +
      (star R).comp (moduleCreationMap (representation φ J hφ) x))) :
    IsModuleCompact ((coordinateCreation φ J x).comp (star D) +
      (star ((hilbertEquiv φ J hφ).transport R)).comp (coordinateCreation φ J x)) := by
  simpa only [HilbertModuleEquiv.transport_star] using compact_creator_odd φ J hφ (star R) (star D) x hc

end BC4lean.KKTheory.CliffordExternalEvenBalancedTensor
