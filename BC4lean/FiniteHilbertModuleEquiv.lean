import BC4lean.FiniteHilbertModuleCoefficientMatrix
import BC4lean.FiniteHilbertModuleFibre

/-! # Whole finite-sum unitaries and coefficient matrix naturality

These are actual coordinate unitaries. The matrix intertwining follows
from the scalar plus coefficient formula for the forced unitization.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace

variable {A B E F ι : Type*} [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
  [Fintype ι] [DecidableEq ι]

def finiteHilbertModuleEquivLinear (e : HilbertModuleEquiv B E F) :
    FiniteHilbertModuleSum B E ι ≃ₗ[ℂ] FiniteHilbertModuleSum B F ι where
  toFun x := (WithCStarModule.equiv _ _).symm (fun i => e (x i))
  invFun x := (WithCStarModule.equiv _ _).symm (fun i => e.symm (x i))
  left_inv x := by ext i; exact e.symm_apply_apply (x i)
  right_inv x := by ext i; exact e.apply_symm_apply (x i)
  map_add' x y := by ext i; exact e.map_add (x i) (y i)
  map_smul' a x := by ext i; exact e.map_smul a (x i)

omit [DecidableEq ι] in
theorem finiteHilbertModuleEquivLinear_inner (e : HilbertModuleEquiv B E F)
    (x y : FiniteHilbertModuleSum B E ι) :
    ⟪finiteHilbertModuleEquivLinear e x, finiteHilbertModuleEquivLinear e y⟫_(Bᵐᵒᵖ) =
      ⟪x, y⟫_(Bᵐᵒᵖ) := by
  change (∑ i, ⟪e (x i), e (y i)⟫_(Bᵐᵒᵖ)) = ∑ i, ⟪x i, y i⟫_(Bᵐᵒᵖ)
  exact Finset.sum_congr rfl (fun _ _ => e.inner_map _ _)

def finiteHilbertModuleEquiv (e : HilbertModuleEquiv B E F) :
    HilbertModuleEquiv B (FiniteHilbertModuleSum B E ι) (FiniteHilbertModuleSum B F ι) where
  linearIsometryEquiv :=
    { toLinearEquiv := finiteHilbertModuleEquivLinear e
      norm_map' x := by
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ),
          finiteHilbertModuleEquivLinear_inner]
        exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm }
  inner_map := finiteHilbertModuleEquivLinear_inner e

omit [DecidableEq ι] in
@[simp] theorem finiteHilbertModuleEquiv_apply (e : HilbertModuleEquiv B E F)
    (x : FiniteHilbertModuleSum B E ι) (i : ι) :
    finiteHilbertModuleEquiv e x i = e (x i) := rfl

variable [CompleteSpace E] [CompleteSpace F]

omit [StarOrderedRing B] [CompleteSpace E] [CompleteSpace F] in
theorem finiteHilbertModuleEquiv_unitized (e : HilbertModuleEquiv B E F)
    (ρ : A →⋆ₙₐ[ℂ] AdjointableMap B E E) (σ : A →⋆ₙₐ[ℂ] AdjointableMap B F F)
    (hρ : ∀ a x, e (ρ a x) = σ a (e x)) (a : Unitization ℂ A) (x : E) :
    e (Unitization.starLift ρ a x) = Unitization.starLift σ a (e x) := by
  change e (a.fst • x + ρ a.snd x) = a.fst • e x + σ a.snd (e x)
  rw [e.map_add, e.map_smul, hρ]

theorem finiteHilbertModuleEquiv_coefficientMatrix (e : HilbertModuleEquiv B E F)
    (ρ : A →⋆ₙₐ[ℂ] AdjointableMap B E E) (σ : A →⋆ₙₐ[ℂ] AdjointableMap B F F)
    (hρ : ∀ a x, e (ρ a x) = σ a (e x))
    (M : CStarMatrix ι ι (Unitization ℂ A)) (x : FiniteHilbertModuleSum B E ι) :
    finiteHilbertModuleEquiv e (finiteHilbertModuleCoefficientMatrixHom ρ M x) =
      finiteHilbertModuleCoefficientMatrixHom σ M (finiteHilbertModuleEquiv e x) := by
  let m : Matrix ι ι (Unitization ℂ A) := CStarMatrix.ofMatrix.symm M
  have hm : CStarMatrix.ofMatrix m = M := CStarMatrix.ofMatrix.apply_symm_apply M
  rw [← hm]
  ext i
  simp only [finiteHilbertModuleEquiv_apply, finiteHilbertModuleCoefficientMatrixHom_apply,
    CStarMatrix.ofMatrix_apply]
  rw [map_sum e.linearIsometryEquiv]
  exact Finset.sum_congr rfl (fun _ _ => finiteHilbertModuleEquiv_unitized e ρ σ hρ _ _)

section Fibre
variable {X M : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul C(X, B)ᵐᵒᵖ M]
  [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

local instance oddContinuationFiniteHilbertModuleEquivLocalInstance01 : CompleteSpace (FiniteHilbertModuleSum C(X, B) M ι) := finiteHilbertModuleSum_complete
local instance oddContinuationFiniteHilbertModuleEquivLocalInstance02 (t : X) : CompleteSpace (FiniteHilbertModuleSum B (HilbertModuleFibre B M t) ι) :=
  finiteHilbertModuleSum_complete

def finiteHilbertModuleFibreRepresentation (t : X)
    (ρ : A →⋆ₙₐ[ℂ] AdjointableMap C(X, B) M M) :
    A →⋆ₙₐ[ℂ] AdjointableMap B (HilbertModuleFibre B M t) (HilbertModuleFibre B M t) :=
  (hilbertModuleFibreOperatorHom t).toNonUnitalStarAlgHom.comp ρ

theorem finiteHilbertModuleFibreEquiv_coefficientMatrix (t : X)
    (ρ : A →⋆ₙₐ[ℂ] AdjointableMap C(X, B) M M)
    (M₀ : CStarMatrix ι ι (Unitization ℂ A))
    (z : HilbertModuleFibre B (FiniteHilbertModuleSum C(X, B) M ι) t) :
    finiteHilbertModuleFibreEquiv t
      (hilbertModuleFibreOperator (B := B) t (finiteHilbertModuleCoefficientMatrixHom ρ M₀) z) =
    finiteHilbertModuleCoefficientMatrixHom (finiteHilbertModuleFibreRepresentation t ρ) M₀
      (finiteHilbertModuleFibreEquiv t z) := by
  obtain ⟨x, rfl⟩ := hilbertModuleFibreMk_surjective (B := B)
    (M := FiniteHilbertModuleSum C(X, B) M ι) t z
  rw [hilbertModuleFibreOperator_mk]
  ext i
  simp only [finiteHilbertModuleFibreEquiv_mk, finiteHilbertModuleCoefficientMatrixHom_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change hilbertModuleFibreMk (B := B) t
    ((M₀ i j).fst • x j + ρ (M₀ i j).snd (x j)) =
      (M₀ i j).fst • hilbertModuleFibreMk (B := B) t (x j) +
        hilbertModuleFibreOperator (B := B) t (ρ (M₀ i j).snd)
          (hilbertModuleFibreMk (B := B) t (x j))
  rw [map_add, map_smul, hilbertModuleFibreOperator_mk]

end Fibre
end BC4lean.KKTheory
