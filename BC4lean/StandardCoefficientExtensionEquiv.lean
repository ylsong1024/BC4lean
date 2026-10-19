import BC4lean.StandardCoefficientImageTensor
import BC4lean.HilbertModuleCoefficientEquiv
import BC4lean.InteriorModuleTensorFormCompletion
import BC4lean.InteriorModuleTensorIsometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Actual coefficient equivalence for standard extension of a module



For an arbitrary nonunital f : B → D and an actual coefficient star equivalence
e : D ≃ C, this constructs
  e_*(E tensor_f D) ≃ E tensor_(e f) C.
The reverse map is defined on balanced tensors, preserves the full C-valued
form, and is onto by pure-tensor density. No norm estimate, injectivity,
nondegeneracy, or surjectivity is assumed for f. This is the coefficient bridge
needed before applying the existing CliffordPairStandardTensor.hilbertEquiv
to the actual pair crossed-product equivalence.
-/

noncomputable section
namespace BC4lean.KKTheory.StandardCoefficientExtensionEquiv
open scoped InnerProductSpace

variable {B D C E : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  (f : B →⋆ₙₐ[ℂ] D) (e : D ≃⋆ₐ[ℂ] C)

abbrev targetHom : B →⋆ₙₐ[ℂ] C := e.toNonUnitalStarAlgHom.comp f
abbrev Source := CoefficientChangedModule e
  (InteriorModuleTensor (E := E) (standardCoefficientImageRepresentation f))
abbrev Target := InteriorModuleTensor (E := E)
  (standardCoefficientImageRepresentation (targetHom f e))

private def reverseCoefficientLinear : Cᵐᵒᵖ →ₗ[ℂ] Dᵐᵒᵖ where
  toFun := opStarAlgEquivBetween e.symm
  map_add' := map_add (opStarAlgEquivBetween e.symm)
  map_smul' := map_smul (opStarAlgEquivBetween e.symm)

def reverseBilinear : E →ₗ[ℂ] Cᵐᵒᵖ →ₗ[ℂ] Source (E := E) f e where
  toFun x :=
    ((coefficientChangedLinearIsometry e).toLinearEquiv.toLinearMap.comp
      (interiorModuleTensorMk (standardCoefficientImageRepresentation f) x)).comp
        (reverseCoefficientLinear e)
  map_add' x y := by
    apply LinearMap.ext
    intro c
    let q := reverseCoefficientLinear e c
    let m := (interiorModuleTensorMk (E := E) (standardCoefficientImageRepresentation f)).flip q
    change coefficientChangedLinearIsometry e (m (x + y)) =
      coefficientChangedLinearIsometry e (m x) + coefficientChangedLinearIsometry e (m y)
    exact (congrArg (coefficientChangedLinearIsometry e) (m.map_add x y)).trans
      ((coefficientChangedLinearIsometry e).map_add (m x) (m y))
  map_smul' a x := by
    apply LinearMap.ext
    intro c
    let q := reverseCoefficientLinear e c
    let m := (interiorModuleTensorMk (E := E) (standardCoefficientImageRepresentation f)).flip q
    change coefficientChangedLinearIsometry e (m (a • x)) =
      a • coefficientChangedLinearIsometry e (m x)
    exact (congrArg (coefficientChangedLinearIsometry e) (m.map_smul a x)).trans
      ((coefficientChangedLinearIsometry e).map_smul a (m x))

omit [PartialOrder C] [StarOrderedRing C] in
@[simp] theorem reverseBilinear_apply (x : E) (c : Cᵐᵒᵖ) :
    reverseBilinear f e x c = coefficientChangedLinearIsometry e
      (interiorModuleTensorMk (standardCoefficientImageRepresentation f) x
        (opStarAlgEquivBetween e.symm c)) := rfl

theorem reverseBilinear_balance (b : B) (x : E) (c : Cᵐᵒᵖ) :
    reverseBilinear f e (MulOpposite.op b • x) c =
      reverseBilinear f e x
        (standardCoefficientImageRepresentation (targetHom f e) b c) := by
  change coefficientChangedLinearIsometry e
      (interiorModuleTensorMk (standardCoefficientImageRepresentation f)
        (MulOpposite.op b • x) (MulOpposite.op (e.symm (MulOpposite.unop c)))) =
    coefficientChangedLinearIsometry e
      (interiorModuleTensorMk (standardCoefficientImageRepresentation f) x
        (MulOpposite.op (e.symm (e (f b) * MulOpposite.unop c))))
  rw [interiorModuleTensorMk_balance, map_mul, e.symm_apply_apply]
  rfl

def reverseBalanced : BalancedModuleTensor (E := E)
    (standardCoefficientImageRepresentation (targetHom f e)) →ₗ[ℂ] Source (E := E) f e :=
  moduleTensorLift _ (reverseBilinear f e) (reverseBilinear_balance f e)

@[simp] theorem reverseBalanced_mk (x : E) (c : Cᵐᵒᵖ) :
    reverseBalanced f e (moduleTensorMk
      (standardCoefficientImageRepresentation (targetHom f e)) x c) =
      reverseBilinear f e x c := rfl

theorem reverseBalanced_inner (u v : BalancedModuleTensor (E := E)
    (standardCoefficientImageRepresentation (targetHom f e))) :
    ⟪reverseBalanced f e u, reverseBalanced f e v⟫_(Cᵐᵒᵖ) =
      moduleTensorInner (standardCoefficientImageRepresentation (targetHom f e)) u v := by
  revert v
  refine moduleTensor_induction _ u ?_ ?_ ?_
  · intro v
    simp
  · intro x c v
    refine moduleTensor_induction _ v ?_ ?_ ?_
    · simp
    · intro y d
      rw [reverseBalanced_mk, reverseBalanced_mk, reverseBilinear_apply,
        reverseBilinear_apply, moduleTensorInner_mk_mk]
      change opStarAlgEquivBetween e
          ⟪interiorModuleTensorMk (standardCoefficientImageRepresentation f) x
            (opStarAlgEquivBetween e.symm c),
            interiorModuleTensorMk (standardCoefficientImageRepresentation f) y
              (opStarAlgEquivBetween e.symm d)⟫_(Dᵐᵒᵖ) = _
      rw [interiorModuleTensorInner_mk_mk]
      apply MulOpposite.unop_injective
      change e (star (e.symm (MulOpposite.unop c)) *
          (f (MulOpposite.unop ⟪x, y⟫_(Bᵐᵒᵖ)) * e.symm (MulOpposite.unop d))) =
        star (MulOpposite.unop c) *
          (e (f (MulOpposite.unop ⟪x, y⟫_(Bᵐᵒᵖ))) * MulOpposite.unop d)
      rw [map_mul, map_mul, map_star, e.apply_symm_apply, e.apply_symm_apply]
    · intro v w hv hw
      simp only [map_add, CStarModule.inner_add_right, hv, hw]
  · intro u v hu hv w
    simp only [map_add, LinearMap.add_apply, CStarModule.inner_add_left, hu, hv]

def reverseIsometry : Target (E := E) f e →ₗᵢ[ℂ] Source (E := E) f e :=
  InteriorModuleTensorFormCompletion.completedIsometry _
    (reverseBalanced f e) (reverseBalanced_inner f e)

@[simp] theorem reverseIsometry_mk (x : E) (c : Cᵐᵒᵖ) :
    reverseIsometry f e
      (interiorModuleTensorMk (standardCoefficientImageRepresentation (targetHom f e)) x c) =
        coefficientChangedLinearIsometry e
          (interiorModuleTensorMk (standardCoefficientImageRepresentation f) x
            (opStarAlgEquivBetween e.symm c)) :=
  InteriorModuleTensorFormCompletion.completedIsometry_mk _ _ _ x c

theorem reverseIsometry_surjective : Function.Surjective (reverseIsometry (E := E) f e) := by
  let R := (reverseIsometry (E := E) f e).toLinearMap.range
  have hR : IsClosed (R : Set (Source (E := E) f e)) :=
    (reverseIsometry f e).isometry.isUniformInducing.isComplete_range.isClosed
  let P := R.comap (coefficientChangedLinearIsometry
    (M := InteriorModuleTensor (E := E) (standardCoefficientImageRepresentation f)) e).toLinearMap
  have hP : IsClosed (P : Set
      (InteriorModuleTensor (E := E) (standardCoefficientImageRepresentation f))) :=
    hR.preimage (coefficientChangedLinearIsometry e).continuous
  have hspan : Submodule.span ℂ (Set.range fun p : E × Dᵐᵒᵖ =>
      interiorModuleTensorMk (standardCoefficientImageRepresentation f) p.1 p.2) ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x,d⟩,rfl⟩
    refine ⟨interiorModuleTensorMk
      (standardCoefficientImageRepresentation (targetHom f e)) x
        (opStarAlgEquivBetween e d), ?_⟩
    change reverseIsometry f e
        (interiorModuleTensorMk (standardCoefficientImageRepresentation (targetHom f e)) x
          (opStarAlgEquivBetween e d)) =
      coefficientChangedLinearIsometry e
        (interiorModuleTensorMk (standardCoefficientImageRepresentation f) x d)
    exact (reverseIsometry_mk f e x (opStarAlgEquivBetween e d)).trans
      (congrArg (fun q : Dᵐᵒᵖ => coefficientChangedLinearIsometry e
        (interiorModuleTensorMk (standardCoefficientImageRepresentation f) x q))
        (coefficientChanged_op_symm_apply_apply e d))
  intro z
  change z ∈ R
  exact closure_minimal hspan hP
    (interiorModuleTensor_span_dense (standardCoefficientImageRepresentation f)
      (coefficientChangedToOriginal e z))

def reverseHilbertEquiv : HilbertModuleEquiv C (Target (E := E) f e) (Source (E := E) f e) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective (reverseIsometry f e)
    (reverseIsometry_surjective f e)
  inner_map := InteriorModuleTensorFormCompletion.completedIsometry_inner _ _ _

def hilbertEquiv : HilbertModuleEquiv C (Source (E := E) f e) (Target (E := E) f e) :=
  (reverseHilbertEquiv f e).symm

@[simp] theorem hilbertEquiv_mk (x : E) (d : Dᵐᵒᵖ) :
    hilbertEquiv f e (coefficientChangedLinearIsometry e
      (interiorModuleTensorMk (standardCoefficientImageRepresentation f) x d)) =
      interiorModuleTensorMk (standardCoefficientImageRepresentation (targetHom f e)) x
        (opStarAlgEquivBetween e d) := by
  apply (reverseHilbertEquiv f e).injective
  change reverseHilbertEquiv f e ((reverseHilbertEquiv f e).symm _) =
    reverseIsometry f e _
  rw [HilbertModuleEquiv.apply_symm_apply, reverseIsometry_mk,
    coefficientChanged_op_symm_apply_apply]

/-- Actual first-factor operators are unchanged under the constructed comparison. -/
theorem hilbertEquiv_operator (T : AdjointableMap B E E) (z : Source (E := E) f e) :
    hilbertEquiv f e (coefficientChangedOperator e
      (interiorModuleTensorOperator (standardCoefficientImageRepresentation f) T) z) =
      interiorModuleTensorOperator (standardCoefficientImageRepresentation (targetHom f e)) T
        (hilbertEquiv f e z) := by
  obtain ⟨w,rfl⟩ := (reverseHilbertEquiv (E := E) f e).surjective z
  let W := (reverseHilbertEquiv (E := E) f e).toAdjointable.toCLM
  have h : W.comp
      (interiorModuleTensorOperator (standardCoefficientImageRepresentation (targetHom f e)) T).toCLM =
    (coefficientChangedOperator e
      (interiorModuleTensorOperator (standardCoefficientImageRepresentation f) T)).toCLM.comp W := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x c
    change reverseIsometry f e
      (interiorModuleTensorOperator (standardCoefficientImageRepresentation (targetHom f e)) T
        (interiorModuleTensorMk (standardCoefficientImageRepresentation (targetHom f e)) x c)) =
      coefficientChangedOperator e
        (interiorModuleTensorOperator (standardCoefficientImageRepresentation f) T)
          (reverseIsometry f e
            (interiorModuleTensorMk (standardCoefficientImageRepresentation (targetHom f e)) x c))
    rw [interiorModuleTensorOperator_mk, reverseIsometry_mk, reverseIsometry_mk]
    change coefficientChangedLinearIsometry e
        (interiorModuleTensorMk (standardCoefficientImageRepresentation f) (T x)
          (opStarAlgEquivBetween e.symm c)) =
      coefficientChangedLinearIsometry e
        (interiorModuleTensorOperator (standardCoefficientImageRepresentation f) T
          (interiorModuleTensorMk (standardCoefficientImageRepresentation f) x
            (opStarAlgEquivBetween e.symm c)))
    rw [interiorModuleTensorOperator_mk]
  let P := coefficientChangedOperator e
    (interiorModuleTensorOperator (standardCoefficientImageRepresentation f) T)
  let Q := interiorModuleTensorOperator
    (standardCoefficientImageRepresentation (targetHom f e)) T
  have hw : reverseHilbertEquiv f e (Q w) = P (reverseHilbertEquiv f e w) :=
    DFunLike.congr_fun h w
  exact (congrArg (fun v : Source (E := E) f e => hilbertEquiv f e v) hw.symm).trans
    (((reverseHilbertEquiv f e).symm_apply_apply (Q w)).trans
      (congrArg Q ((reverseHilbertEquiv f e).symm_apply_apply w)).symm)

/-- A named target coefficient homomorphism may be identified with e ∘ f.
This equality records coefficient algebra data, not a desired tensor theorem. -/
def hilbertEquivTo (k : B →⋆ₙₐ[ℂ] C) (hk : targetHom f e = k) :
    HilbertModuleEquiv C (Source (E := E) f e)
      (InteriorModuleTensor (E := E) (standardCoefficientImageRepresentation k)) :=
  hk ▸ hilbertEquiv f e

@[simp] theorem hilbertEquivTo_mk (k : B →⋆ₙₐ[ℂ] C) (hk : targetHom f e = k)
    (x : E) (d : Dᵐᵒᵖ) :
    hilbertEquivTo f e k hk (coefficientChangedLinearIsometry e
      (interiorModuleTensorMk (standardCoefficientImageRepresentation f) x d)) =
      interiorModuleTensorMk (standardCoefficientImageRepresentation k) x
        (opStarAlgEquivBetween e d) := by
  cases hk
  exact hilbertEquiv_mk f e x d

theorem hilbertEquivTo_operator (k : B →⋆ₙₐ[ℂ] C) (hk : targetHom f e = k)
    (T : AdjointableMap B E E) (z : Source (E := E) f e) :
    hilbertEquivTo f e k hk (coefficientChangedOperator e
      (interiorModuleTensorOperator (standardCoefficientImageRepresentation f) T) z) =
      interiorModuleTensorOperator (standardCoefficientImageRepresentation k) T
        (hilbertEquivTo f e k hk z) := by
  cases hk
  exact hilbertEquiv_operator f e T z

end BC4lean.KKTheory.StandardCoefficientExtensionEquiv
