import BC4lean.KasparovDescentDirectSum
import BC4lean.ReducedCrossedProductPair
import BC4lean.CliffordOddSourceCycle

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Actual reduced descent of the signed Clifford odd-source model



The actual tensor/direct-sum coefficient-form unitary is reused. Its single
map carries the genuine swap grading and the actual Pauli σ_y F operator.
The group action is already diagonal under the proved sum-tensor identity.
The completed source representation is intertwined through the actual pair
crossed-product star equivalence, first on finite generators and then by
density. No nondegeneracy is required for the original representation.

This is the concrete parity coherence needed to apply the existing native
odd-even and odd-odd product reduction theorems. It does not assume a matrix
crossed-product equivalence or a desired native product law.
-/

noncomputable section
namespace BC4lean.KKTheory.KasparovDescent
open scoped KasparovDescent CStarAlgebra

variable {Γ A B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  (β : CStarAlgebraAction Γ B)

local instance signedSourceSumComplete : CompleteSpace (HilbertModuleSum B E E) :=
  hilbertModuleSum_complete
local instance signedSourceTargetSumComplete : CompleteSpace
    (HilbertModuleSum (ReducedCrossedProduct β) (Module β E) (Module β E)) :=
  hilbertModuleSum_complete

/-- Swap of the actual source Hilbert sum remains swap after completion. -/
theorem sumModuleEquiv_signedSource_grading
    (z : Module β (HilbertModuleSum B E E)) :
    sumModuleEquiv β
      ((ordinaryModuleGrading β (CliffordOddSourceCycle.grading (C := B) (H := E))).grading z) =
      (CliffordOddSourceCycle.grading (C := ReducedCrossedProduct β) (H := Module β E)).grading
        (sumModuleEquiv β z) := by
  let W : Module β (HilbertModuleSum B E E) →L[ℂ]
      HilbertModuleSum (ReducedCrossedProduct β) (Module β E) (Module β E) :=
    (sumModuleEquiv (E := E) (F := E) β).toAdjointable.toCLM
  let J : Module β (HilbertModuleSum B E E) →L[ℂ]
      Module β (HilbertModuleSum B E E) :=
    (ordinaryModuleGrading β (CliffordOddSourceCycle.grading (C := B) (H := E))).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let K : HilbertModuleSum (ReducedCrossedProduct β) (Module β E) (Module β E) →L[ℂ]
      HilbertModuleSum (ReducedCrossedProduct β) (Module β E) (Module β E) :=
    (CliffordOddSourceCycle.grading (C := ReducedCrossedProduct β)
      (H := Module β E)).grading.toContinuousLinearEquiv.toContinuousLinearMap
  let P : HilbertModuleSum B E E → (ReducedCrossedProduct β)ᵐᵒᵖ →
      HilbertModuleSum (ReducedCrossedProduct β) (Module β E) (Module β E) := fun y d =>
    sumMk (mk β E y.fst d) (mk β E y.snd d)
  have hW (y : HilbertModuleSum B E E) (d : (ReducedCrossedProduct β)ᵐᵒᵖ) :
      W (mk β (HilbertModuleSum B E E) y d) = P y d :=
    sumModuleEquiv_mk (Γ := Γ) (B := B) (E := E) (F := E) β y d
  have hJ (y : HilbertModuleSum B E E) (d : (ReducedCrossedProduct β)ᵐᵒᵖ) :
      J (mk β (HilbertModuleSum B E E) y d) =
        mk β (HilbertModuleSum B E E)
          ((CliffordOddSourceCycle.grading (C := B) (H := E)).grading y) d :=
    ordinaryModuleGrading_mk (Γ := Γ) (B := B) (E := HilbertModuleSum B E E)
      β (CliffordOddSourceCycle.grading (C := B) (H := E)) y d
  have hP (y : HilbertModuleSum B E E) (d : (ReducedCrossedProduct β)ᵐᵒᵖ) :
      P ((CliffordOddSourceCycle.grading (C := B) (H := E)).grading y) d = K (P y d) := by
    have hy : (CliffordOddSourceCycle.grading (C := B) (H := E)).grading y =
        sumMk (B := B) y.snd y.fst :=
      sumSwap_apply (B := B) (E := E) (F := E) y
    have hk : K (P y d) = sumMk (mk β E y.snd d) (mk β E y.fst d) :=
      sumSwap_apply (B := ReducedCrossedProduct β) (E := Module β E) (F := Module β E) (P y d)
    exact (congrArg (fun v : HilbertModuleSum B E E => P v d) hy).trans hk.symm
  have h : W.comp J = K.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      (B := B) (C := ReducedCrossedProduct β) (E := HilbertModuleSum B E E)
      (F := (ReducedCrossedProduct β)ᵐᵒᵖ) (φ := coefficientRepresentation β)
      (P := HilbertModuleSum (ReducedCrossedProduct β) (Module β E) (Module β E))
      (f := W.comp J) (g := K.comp W)
    intro x c
    calc
      (W.comp J) (mk β (HilbertModuleSum B E E) x c) =
          W (mk β (HilbertModuleSum B E E)
            ((CliffordOddSourceCycle.grading (C := B) (H := E)).grading x) c) :=
        congrArg (fun v : Module β (HilbertModuleSum B E E) => W v) (hJ x c)
      _ = P ((CliffordOddSourceCycle.grading (C := B) (H := E)).grading x) c :=
        hW ((CliffordOddSourceCycle.grading (C := B) (H := E)).grading x) c
      _ = K (P x c) := hP x c
      _ = (K.comp W) (mk β (HilbertModuleSum B E E) x c) :=
        congrArg
          (fun v : HilbertModuleSum (ReducedCrossedProduct β) (Module β E) (Module β E) => K v)
          (hW x c).symm
  exact DFunLike.congr_fun h z

/-- The actual σ_y sign and scalar phases are retained by the same unitary. -/
theorem sumModuleEquiv_signedSource_operator (T : AdjointableMap B E E)
    (z : Module β (HilbertModuleSum B E E)) :
    sumModuleEquiv β
      (operatorHom β (HilbertModuleSum B E E) (CliffordOddSourceCycle.operator T) z) =
      CliffordOddSourceCycle.operator (operatorHom β E T) (sumModuleEquiv β z) := by
  let W : Module β (HilbertModuleSum B E E) →L[ℂ]
      HilbertModuleSum (ReducedCrossedProduct β) (Module β E) (Module β E) :=
    (sumModuleEquiv (E := E) (F := E) β).toAdjointable.toCLM
  let L : Module β (HilbertModuleSum B E E) →L[ℂ]
      Module β (HilbertModuleSum B E E) :=
    (operatorHom β (HilbertModuleSum B E E) (CliffordOddSourceCycle.operator T)).toCLM
  let R : HilbertModuleSum (ReducedCrossedProduct β) (Module β E) (Module β E) →L[ℂ]
      HilbertModuleSum (ReducedCrossedProduct β) (Module β E) (Module β E) :=
    (CliffordOddSourceCycle.operator (operatorHom β E T)).toCLM
  let P : HilbertModuleSum B E E → (ReducedCrossedProduct β)ᵐᵒᵖ →
      HilbertModuleSum (ReducedCrossedProduct β) (Module β E) (Module β E) := fun y d =>
    sumMk (mk β E y.fst d) (mk β E y.snd d)
  have hW (y : HilbertModuleSum B E E) (d : (ReducedCrossedProduct β)ᵐᵒᵖ) :
      W (mk β (HilbertModuleSum B E E) y d) = P y d :=
    sumModuleEquiv_mk (Γ := Γ) (B := B) (E := E) (F := E) β y d
  have hL (y : HilbertModuleSum B E E) (d : (ReducedCrossedProduct β)ᵐᵒᵖ) :
      L (mk β (HilbertModuleSum B E E) y d) =
        mk β (HilbertModuleSum B E E) (CliffordOddSourceCycle.operator T y) d :=
    operatorHom_mk (Γ := Γ) (B := B) β (HilbertModuleSum B E E)
      (CliffordOddSourceCycle.operator T) y d
  have hsmul (a : ℂ) (y : E) (d : (ReducedCrossedProduct β)ᵐᵒᵖ) :
      mk β E (a • y) d = a • mk β E y d := by
    have hs : interiorModuleTensorMk (E := E) (coefficientRepresentation β) (a • y) =
        a • interiorModuleTensorMk (E := E) (coefficientRepresentation β) y :=
      map_smul (interiorModuleTensorMk (E := E) (coefficientRepresentation β)) a y
    exact LinearMap.congr_fun hs d
  have hP (y : HilbertModuleSum B E E) (d : (ReducedCrossedProduct β)ᵐᵒᵖ) :
      P (CliffordOddSourceCycle.operator T y) d = R (P y d) := by
    calc
      P (CliffordOddSourceCycle.operator T y) d =
          P (sumMk (B := B) ((-Complex.I) • T y.snd) (Complex.I • T y.fst)) d :=
        congrArg (fun v : HilbertModuleSum B E E => P v d)
          (CliffordOddSourceCycle.operator_apply T y)
      _ = sumMk
          (mk β E ((-Complex.I) • T y.snd) d)
          (mk β E (Complex.I • T y.fst) d) := rfl
      _ = sumMk ((-Complex.I) • mk β E (T y.snd) d)
          (Complex.I • mk β E (T y.fst) d) :=
        congrArg₂
          (fun u v : Module β E => sumMk (B := ReducedCrossedProduct β) u v)
          (hsmul (-Complex.I) (T y.snd) d) (hsmul Complex.I (T y.fst) d)
      _ = sumMk
          ((-Complex.I) • operatorHom β E T (mk β E y.snd d))
          (Complex.I • operatorHom β E T (mk β E y.fst d)) :=
        congrArg₂
          (fun u v : Module β E =>
            sumMk (B := ReducedCrossedProduct β) ((-Complex.I) • u) (Complex.I • v))
          (operatorHom_mk β E T y.snd d).symm
          (operatorHom_mk β E T y.fst d).symm
      _ = R (P y d) :=
        (CliffordOddSourceCycle.operator_apply (operatorHom β E T) (P y d)).symm
  have h : W.comp L = R.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      (B := B) (C := ReducedCrossedProduct β) (E := HilbertModuleSum B E E)
      (F := (ReducedCrossedProduct β)ᵐᵒᵖ) (φ := coefficientRepresentation β)
      (P := HilbertModuleSum (ReducedCrossedProduct β) (Module β E) (Module β E))
      (f := W.comp L) (g := R.comp W)
    intro x c
    calc
      (W.comp L) (mk β (HilbertModuleSum B E E) x c) =
          W (mk β (HilbertModuleSum B E E) (CliffordOddSourceCycle.operator T x) c) :=
        congrArg (fun v : Module β (HilbertModuleSum B E E) => W v) (hL x c)
      _ = P (CliffordOddSourceCycle.operator T x) c :=
        hW (CliffordOddSourceCycle.operator T x) c
      _ = R (P x c) := hP x c
      _ = (R.comp W) (mk β (HilbertModuleSum B E E) x c) :=
        congrArg
          (fun v : HilbertModuleSum (ReducedCrossedProduct β) (Module β E) (Module β E) => R v)
          (hW x c).symm
  exact DFunLike.congr_fun h z

variable (α : CStarAlgebraAction Γ A)
  (U : EquivariantHilbertModule β E)
  (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
  (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))

omit [PartialOrder A] [StarOrderedRing A] [CompleteSpace E] in
include hπ in
/-- Actual source covariance for the signed model is inherited coordinatewise. -/
theorem signedSource_representation_equivariant (g : Γ) (a : A × A) :
    (U.sum U).conjugateOperator g (CliffordOddSourceCycle.representation π a) =
      CliffordOddSourceCycle.representation π ((cliffordCoefficientAction α).automorphism g a) := by
  change (U.sum U).conjugateOperator g (sumMap (π a.1) (π a.2)) = _
  rw [EquivariantHilbertModule.sum_conjugateOperator, hπ, hπ]
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
theorem sumModuleEquiv_signedSource_generator (a : A × A) (g : Γ)
    (z : Module β (HilbertModuleSum B E E)) :
    sumModuleEquiv β
      (sourceGenerator β (HilbertModuleSum B E E) (U.sum U)
        (CliffordOddSourceCycle.representation π) a g z) =
      sumMap (sourceGenerator β E U π a.1 g) (sourceGenerator β E U π a.2 g)
        (sumModuleEquiv β z) := by
  exact sumModuleEquiv_sourceGenerator
    (Γ := Γ) (B := B) (E := E) (F := E) β U U
    (π.comp (NonUnitalStarAlgHom.fst ℂ A A))
    (π.comp (NonUnitalStarAlgHom.snd ℂ A A)) a g z

theorem pairCrossed_equiv_single (a : A × A) (g : Γ) :
    ReducedCrossedProductPair.equiv α
      (algebraicToReducedCrossed (cliffordCoefficientAction α)
        (AlgebraicCrossedProduct.single (cliffordCoefficientAction α) g a)) =
      (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a.1),
        algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α g a.2)) := by
  have hp (b : A × A) : algebraicToReducedCrossed (cliffordCoefficientAction α)
      (AlgebraicCrossedProduct.single (cliffordCoefficientAction α) g b) =
      (⟨reducedCrossedGenerator (cliffordCoefficientAction α) b g,
        reducedCrossedGenerator_mem (cliffordCoefficientAction α) b g⟩ :
          ReducedCrossedProduct (cliffordCoefficientAction α)) := by
    apply Subtype.ext
    exact algebraicToReducedCrossed_single (cliffordCoefficientAction α) g b
  rw [hp, ReducedCrossedProductPair.equiv_generator]
  apply Prod.ext <;> apply Subtype.ext <;>
    exact (algebraicToReducedCrossed_single α g _).symm

/-- This is the actual source action on every completed crossed element. -/
theorem sumModuleEquiv_signedSource_representation
    (a : ReducedCrossedProduct (cliffordCoefficientAction α))
    (z : Module β (HilbertModuleSum B E E)) :
    sumModuleEquiv β
      (reducedSourceRepresentation β (HilbertModuleSum B E E)
        (cliffordCoefficientAction α) (U.sum U) (CliffordOddSourceCycle.representation π)
        (signedSource_representation_equivariant β α U π hπ) a z) =
      CliffordOddSourceCycle.representation
        (reducedSourceRepresentation β E α U π hπ) (ReducedCrossedProductPair.equiv α a)
          (sumModuleEquiv β z) := by
  let ρS := reducedSourceRepresentation β (HilbertModuleSum B E E)
    (cliffordCoefficientAction α) (U.sum U) (CliffordOddSourceCycle.representation π)
      (signedSource_representation_equivariant β α U π hπ)
  let ρT := (CliffordOddSourceCycle.representation
    (reducedSourceRepresentation β E α U π hπ)).comp
      (ReducedCrossedProductPair.equiv α).toNonUnitalStarAlgHom
  let W := (sumModuleEquiv (E := E) (F := E) β).toAdjointable.toCLM
  have hS : Continuous (fun a => W (ρS a z)) :=
    W.continuous.comp
      ((AdjointableMap.toCLM_isometry.continuous.comp (map_continuous ρS)).clm_apply continuous_const)
  have hT : Continuous (fun a => ρT a (W z)) :=
    (AdjointableMap.toCLM_isometry.continuous.comp (map_continuous ρT)).clm_apply continuous_const
  change W (ρS a z) = ρT a (W z)
  refine (algebraicToReducedCrossed_denseRange (cliffordCoefficientAction α)).induction_on a
    (isClosed_eq hS hT) ?_
  intro f
  induction f using AlgebraicCrossedProduct.induction_on (cliffordCoefficientAction α) with
  | zero => simp only [map_zero, AdjointableMap.coe_zero_apply]
  | single g b =>
    have hs : ρS (algebraicToReducedCrossed (cliffordCoefficientAction α)
        (AlgebraicCrossedProduct.single (cliffordCoefficientAction α) g b)) =
        sourceGenerator β (HilbertModuleSum B E E) (U.sum U)
          (CliffordOddSourceCycle.representation π) b g :=
      reducedSourceRepresentation_single β (HilbertModuleSum B E E)
        (cliffordCoefficientAction α) (U.sum U) (CliffordOddSourceCycle.representation π)
        (signedSource_representation_equivariant β α U π hπ) g b
    have ht : ρT (algebraicToReducedCrossed (cliffordCoefficientAction α)
        (AlgebraicCrossedProduct.single (cliffordCoefficientAction α) g b)) =
        sumMap (sourceGenerator β E U π b.1 g) (sourceGenerator β E U π b.2 g) :=
      (congrArg
        (fun q : ReducedCrossedProduct α × ReducedCrossedProduct α =>
          CliffordOddSourceCycle.representation
            (reducedSourceRepresentation β E α U π hπ) q)
        (pairCrossed_equiv_single α b g)).trans
          (congrArg₂
            (fun P Q : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E) =>
              sumMap P Q)
            (reducedSourceRepresentation_single β E α U π hπ g b.1)
            (reducedSourceRepresentation_single β E α U π hπ g b.2))
    exact (congrArg
      (fun T : AdjointableMap (ReducedCrossedProduct β)
        (Module β (HilbertModuleSum B E E)) (Module β (HilbertModuleSum B E E)) => W (T z)) hs).trans
      ((sumModuleEquiv_signedSource_generator β U π b g z).trans
        (congrArg
          (fun T : AdjointableMap (ReducedCrossedProduct β)
            (HilbertModuleSum (ReducedCrossedProduct β) (Module β E) (Module β E))
            (HilbertModuleSum (ReducedCrossedProduct β) (Module β E) (Module β E)) => T (W z)) ht).symm)
  | add f h ihf ihh =>
    simpa only [map_add, AdjointableMap.coe_add_apply] using congrArg₂ (· + ·) ihf ihh

end BC4lean.KKTheory.KasparovDescent
