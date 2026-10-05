import BC4lean.AdjointableComplete
import BC4lean.HilbertModuleSum
import BC4lean.InjectiveStarHomPositivity
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-! # Actual positivity of finite Hilbert-module Gram matrices

A finite standard right module uses Mathlib's finite Hilbert-module norm.
The matrix representation is faithful and has the usual column action after
explicitly reversing the opposite coefficient convention.  For a finite family
of module vectors, its Gram matrix represents the actual operator S* S, where
S is their bounded synthesis map.  Injective star-homomorphisms reflect
positivity, so the Gram matrix is positive in the matrix C*-algebra.
-/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace WithCStarModule
open CStarModule

variable {B E n : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Fintype n]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

/-- The actual finite standard right Hilbert B-module. -/
abbrev FiniteStandardModule (B n : Type*) := WithCStarModule Bᵐᵒᵖ (n → Bᵐᵒᵖ)

/-- The complex-linear synthesis map for a finite family of vectors. -/
def moduleGramSynthesisLinear (x : n → E) : FiniteStandardModule B n →ₗ[ℂ] E where
  toFun v := ∑ i, v i • x i
  map_add' v w := by
    simp only [WithCStarModule.add_apply, module_add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [WithCStarModule.smul_apply, module_complex_smul, Finset.smul_sum,
      RingHom.id_apply]

/-- The complex-linear coefficient-analysis map of a finite family. -/
def moduleGramAnalysisLinear (x : n → E) : E →ₗ[ℂ] FiniteStandardModule B n where
  toFun y := (WithCStarModule.equiv _ _).symm fun i => ⟪x i, y⟫_(Bᵐᵒᵖ)
  map_add' y z := by
    ext i
    simp only [WithCStarModule.equiv_symm_pi_apply, WithCStarModule.add_apply,
      CStarModule.inner_add_right]
  map_smul' c y := by
    ext i
    simp only [WithCStarModule.equiv_symm_pi_apply, WithCStarModule.smul_apply,
      inner_smul_right_complex, RingHom.id_apply]

/-- Synthesis is bounded for the genuine finite Hilbert-module norm. -/
theorem moduleGramSynthesisLinear_bound (x : n → E) (v : FiniteStandardModule B n) :
    ‖moduleGramSynthesisLinear x v‖ ≤ (∑ i, ‖x i‖) * ‖v‖ := by
  classical
  calc
    ‖moduleGramSynthesisLinear x v‖ ≤ ∑ i, ‖v i • x i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖v i‖ * ‖x i‖ := Finset.sum_le_sum fun i _ => module_norm_smul_le _ _
    _ ≤ ∑ i, ‖v‖ * ‖x i‖ := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (WithCStarModule.norm_apply_le_norm v i) (norm_nonneg _)
    _ = (∑ i, ‖x i‖) * ‖v‖ := by rw [← Finset.mul_sum, mul_comm]

/-- Coefficient analysis is bounded for the genuine finite Hilbert-module norm. -/
theorem moduleGramAnalysisLinear_bound (x : n → E) (y : E) :
    ‖moduleGramAnalysisLinear (B := B) x y‖ ≤ (∑ i, ‖x i‖) * ‖y‖ := by
  classical
  calc
    ‖moduleGramAnalysisLinear (B := B) x y‖ ≤ ∑ i, ‖⟪x i, y⟫_(Bᵐᵒᵖ)‖ :=
      WithCStarModule.pi_norm_le_sum_norm _
    _ ≤ ∑ i, ‖x i‖ * ‖y‖ := Finset.sum_le_sum fun _ _ => norm_inner_le E
    _ = (∑ i, ‖x i‖) * ‖y‖ := (Finset.sum_mul _ _ _).symm

/-- Synthesis and coefficient analysis form an actual adjointable map. -/
def moduleGramSynthesis (x : n → E) : AdjointableMap B (FiniteStandardModule B n) E where
  toCLM := (moduleGramSynthesisLinear (B := B) x).mkContinuous (∑ i, ‖x i‖)
    (moduleGramSynthesisLinear_bound (B := B) x)
  adjointCLM := (moduleGramAnalysisLinear (B := B) x).mkContinuous (∑ i, ‖x i‖)
    (moduleGramAnalysisLinear_bound (B := B) x)
  adjoint_identity v y := by
    simp only [LinearMap.mkContinuous_apply, moduleGramSynthesisLinear,
      moduleGramAnalysisLinear, LinearMap.coe_mk, AddHom.coe_mk, inner_sum_left,
      inner_op_smul_left, WithCStarModule.pi_inner, WithCStarModule.inner_def,
      WithCStarModule.equiv_symm_pi_apply]

/-- Transpose and take opposite coefficients, so Mathlib's row action becomes
the usual column action on a right module. -/
def moduleMatrixOpposite (M : CStarMatrix n n B) : CStarMatrix n n Bᵐᵒᵖ :=
  CStarMatrix.ofMatrix fun i j => MulOpposite.op (M j i)

omit [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [Fintype n] in
@[simp] theorem moduleMatrixOpposite_apply (M : CStarMatrix n n B) (i j : n) :
    moduleMatrixOpposite M i j = MulOpposite.op (M j i) := rfl

omit [PartialOrder B] [StarOrderedRing B] [Fintype n] in
@[simp] theorem moduleMatrixOpposite_add (M N : CStarMatrix n n B) :
    moduleMatrixOpposite (M + N) = moduleMatrixOpposite M + moduleMatrixOpposite N := by
  ext i j
  simp

omit [PartialOrder B] [StarOrderedRing B] [Fintype n] in
@[simp] theorem moduleMatrixOpposite_smul (c : ℂ) (M : CStarMatrix n n B) :
    moduleMatrixOpposite (c • M) = c • moduleMatrixOpposite M := by
  ext i j
  simp

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem moduleMatrixOpposite_mul (M N : CStarMatrix n n B) :
    moduleMatrixOpposite (M * N) = moduleMatrixOpposite N * moduleMatrixOpposite M := by
  ext i j
  simp only [moduleMatrixOpposite_apply, CStarMatrix.mul_apply,
    Finset.op_sum, MulOpposite.op_mul]

omit [PartialOrder B] [StarOrderedRing B] [Fintype n] in
@[simp] theorem moduleMatrixOpposite_star (M : CStarMatrix n n B) :
    moduleMatrixOpposite (star M) = star (moduleMatrixOpposite M) := by
  ext i j
  simp only [moduleMatrixOpposite_apply, CStarMatrix.star_apply, MulOpposite.op_star]

omit [PartialOrder B] [StarOrderedRing B] [Fintype n] in
@[simp] theorem moduleMatrixOpposite_zero :
    moduleMatrixOpposite (0 : CStarMatrix n n B) = 0 := by
  ext i j
  rfl

/-- A coefficient matrix acts by a genuine bounded adjointable map. -/
def moduleMatrixOperator (M : CStarMatrix n n B) :
    AdjointableMap B (FiniteStandardModule B n) (FiniteStandardModule B n) where
  toCLM := CStarMatrix.toCLM (moduleMatrixOpposite M)
  adjointCLM := CStarMatrix.toCLM (star (moduleMatrixOpposite M))
  adjoint_identity _v _w := (CStarMatrix.inner_toCLM_conjTranspose_right).symm

/-- The faithful matrix action, bundled as a nonunital complex star-homomorphism. -/
def moduleMatrixRepresentation : CStarMatrix n n B →⋆ₙₐ[ℂ]
    AdjointableMap B (FiniteStandardModule B n) (FiniteStandardModule B n) where
  toFun := moduleMatrixOperator
  map_zero' := by
    apply AdjointableMap.ext
    intro v
    simp [moduleMatrixOperator]
  map_add' M N := by
    apply AdjointableMap.ext
    intro v
    simp [moduleMatrixOperator]
  map_smul' c M := by
    apply AdjointableMap.ext
    intro v
    simp [moduleMatrixOperator]
  map_mul' M N := by
    apply AdjointableMap.ext
    intro v
    change CStarMatrix.toCLM (moduleMatrixOpposite (M * N)) v =
      (CStarMatrix.toCLM (moduleMatrixOpposite M)).comp
        (CStarMatrix.toCLM (moduleMatrixOpposite N)) v
    rw [moduleMatrixOpposite_mul]
    have h := congrArg MulOpposite.unop
      (map_mul (CStarMatrix.toCLMNonUnitalAlgHom (A := Bᵐᵒᵖ))
        (moduleMatrixOpposite N) (moduleMatrixOpposite M))
    exact congrArg (fun T => T v) h
  map_star' M := by
    apply AdjointableMap.ext
    intro v
    change CStarMatrix.toCLM (moduleMatrixOpposite (star M)) v =
      CStarMatrix.toCLM (star (moduleMatrixOpposite M)) v
    rw [moduleMatrixOpposite_star]

/-- The matrix representation is faithful, even for nonunital B. -/
theorem moduleMatrixRepresentation_injective :
    Function.Injective (moduleMatrixRepresentation (B := B) (n := n)) := by
  intro M N h
  have hCLM := congrArg AdjointableMap.toCLM h
  have hop := CStarMatrix.toCLM_injective hCLM
  apply CStarMatrix.ext
  intro i j
  exact MulOpposite.op_injective (congrFun (congrFun hop j) i)

/-- The actual finite Gram matrix with the usual B-valued right-module inner product. -/
def moduleGramMatrix (x : n → E) : CStarMatrix n n B :=
  CStarMatrix.ofMatrix fun i j => MulOpposite.unop ⟪x i, x j⟫_(Bᵐᵒᵖ)

/-- The matrix representation of the Gram matrix is the actual square S* S. -/
theorem moduleGramMatrix_representation (x : n → E) :
    moduleMatrixRepresentation (moduleGramMatrix (B := B) x) =
      (moduleGramSynthesis (B := B) x).adjoint.comp (moduleGramSynthesis (B := B) x) := by
  apply AdjointableMap.ext
  intro v
  ext j
  change (CStarMatrix.toCLM (moduleMatrixOpposite (moduleGramMatrix x)) v) j =
    ⟪x j, ∑ i, v i • x i⟫_(Bᵐᵒᵖ)
  simp only [moduleGramMatrix,
    moduleMatrixOpposite_apply,
    CStarMatrix.toCLM_apply_eq_sum, WithCStarModule.equiv_symm_pi_apply,
    inner_sum_right, inner_op_smul_right]
  rfl

/-- The matrix action embedded as the first block of a linking-module operator. -/
def moduleGramBlockRepresentation : CStarMatrix n n B →⋆ₙₐ[ℂ]
    AdjointableMap B (HilbertModuleSum B (FiniteStandardModule B n) E)
      (HilbertModuleSum B (FiniteStandardModule B n) E) where
  toFun M := sumMap (moduleMatrixRepresentation M) (0 : AdjointableMap B E E)
  map_zero' := by simp only [map_zero, sumMap_zero]
  map_add' M N := by
    simp only [map_add]
    simpa only [zero_add] using
      sumMap_add (moduleMatrixRepresentation M) (moduleMatrixRepresentation N)
        (0 : AdjointableMap B E E) 0
  map_smul' c M := by
    simpa only [map_smul, smul_zero, MonoidHom.id_apply] using
      sumMap_smul c (moduleMatrixRepresentation M) (0 : AdjointableMap B E E)
  map_mul' M N := by
    simp only [map_mul]
    simpa only [zero_mul] using
      sumMap_mul (moduleMatrixRepresentation M) (moduleMatrixRepresentation N)
        (0 : AdjointableMap B E E) 0
  map_star' M := by
    simpa only [map_star, star_zero] using
      sumMap_star (moduleMatrixRepresentation M) (0 : AdjointableMap B E E)

/-- The block representation remains faithful. -/
theorem moduleGramBlockRepresentation_injective :
    Function.Injective (moduleGramBlockRepresentation (B := B) (E := E) (n := n)) := by
  intro M N h
  apply moduleMatrixRepresentation_injective
  apply AdjointableMap.ext
  intro v
  have hv := congrArg (fun T => (T (sumMk v (0 : E))).fst) h
  change (sumMap (moduleMatrixRepresentation M) (0 : AdjointableMap B E E)
      (sumMk v (0 : E))).fst =
    (sumMap (moduleMatrixRepresentation N) (0 : AdjointableMap B E E)
      (sumMk v (0 : E))).fst at hv
  simpa only [sumMap_apply, sumMk_fst] using hv

/-- Gram positivity is established in the actual matrix C*-algebra. The
linking-module square handles the differing source and target of synthesis. -/
theorem moduleGramMatrix_nonneg [CompleteSpace E] (x : n → E) :
    0 ≤ moduleGramMatrix (B := B) x := by
  let U := HilbertModuleSum B (FiniteStandardModule B n) E
  let : CompleteSpace U := hilbertModuleSum_complete
  let : PartialOrder (AdjointableMap B U U) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (AdjointableMap B U U) := CStarAlgebra.spectralOrderedRing _
  let T : AdjointableMap B U U :=
    ((sumInr (B := B) (E := FiniteStandardModule B n) (F := E)).comp
      (moduleGramSynthesis x)).comp sumFst
  have ht (u : U) : T u = sumMk (0 : FiniteStandardModule B n) (moduleGramSynthesis x u.fst) := by
    rfl
  have hta (u : U) : T.adjoint u =
      sumMk ((moduleGramSynthesis x).adjoint u.snd) (0 : E) := by
    rfl
  have hsquare : moduleGramBlockRepresentation (E := E) (moduleGramMatrix x) = star T * T := by
    apply AdjointableMap.ext
    intro u
    change sumMap (moduleMatrixRepresentation (moduleGramMatrix x))
      (0 : AdjointableMap B E E) u = T.adjoint (T u)
    rw [sumMap_apply, ht, hta]
    simp only [AdjointableMap.coe_zero_apply, sumMk_snd]
    rw [moduleGramMatrix_representation, AdjointableMap.comp_apply]
  apply (injectiveStarHom_nonneg_iff (moduleGramBlockRepresentation (E := E))
    moduleGramBlockRepresentation_injective _).mp
  rw [hsquare]
  exact star_mul_self_nonneg T

end BC4lean.KKTheory
