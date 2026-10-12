import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.RCLike.Extend
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Countable.Defs
import Mathlib.Tactic.Module
import BC4lean.QuasicentralApproximateUnit

noncomputable section

namespace BC4lean.KKTheory

open scoped ComplexOrder InnerProductSpace Topology
open UniformSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

@[reducible] local instance : LE (A × A) := (Prod.instPartialOrder A A).toLE

/-- The C⋆ order-unit bound on a selfadjoint element follows from both
extreme real spectral values. -/
theorem selfAdjoint_norm_le_of_order_bounds [Nontrivial A] {x : A} (hx : IsSelfAdjoint x)
    {r : ℝ} (hlo : -(algebraMap ℝ A r) ≤ x) (hup : x ≤ algebraMap ℝ A r) :
    ‖x‖ ≤ r := by
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum hx with hn | hn
  · exact (le_algebraMap_iff_spectrum_le hx).mp hup ‖x‖ hn
  · have hlow : algebraMap ℝ A (-r) ≤ x := by simpa using hlo
    have h := (algebraMap_le_iff_le_spectrum hx).mp hlow (-‖x‖) hn
    linarith

/-- A real bounded functional on the selfadjoint part is positive if it
attains its norm at the order unit. -/
theorem selfAdjoint_dual_nonneg_of_unit_eq_norm
    (f : StrongDual ℝ (selfAdjoint A)) (hf : f 1 = ‖f‖)
    (x : selfAdjoint A) (hx : 0 ≤ (x : A)) : 0 ≤ f x := by
  by_cases hzero : x = 0
  · simp [hzero]
  have hc : 0 < ‖x‖ := norm_pos_iff.mpr hzero
  let y : selfAdjoint A := ‖x‖⁻¹ • x
  have hy0 : 0 ≤ (y : A) := by
    simpa only [y, selfAdjoint.val_smul] using smul_nonneg (inv_nonneg.mpr hc.le) hx
  have hynorm : ‖(y : A)‖ ≤ 1 := by
    change ‖‖x‖⁻¹ • (x : A)‖ ≤ 1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le)]
    change ‖x‖⁻¹ * ‖x‖ ≤ 1
    rw [inv_mul_cancel₀ hc.ne']
  have hy1 : (y : A) ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg (y : A) hy0).mp hynorm
  have hcompnorm : ‖(1 - y : selfAdjoint A)‖ ≤ 1 := by
    change ‖(1 - (y : A) : A)‖ ≤ 1
    exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ (sub_nonneg.mpr hy1)).mpr
      (sub_le_self _ hy0)
  have hupper : f (1 - y) ≤ ‖f‖ := by
    calc
      f (1 - y) ≤ ‖f (1 - y)‖ := Real.le_norm_self _
      _ ≤ ‖f‖ * ‖(1 - y : selfAdjoint A)‖ := f.le_opNorm _
      _ ≤ ‖f‖ * 1 := mul_le_mul_of_nonneg_left hcompnorm f.opNorm_nonneg
      _ = ‖f‖ := mul_one _
  rw [map_sub, hf] at hupper
  have hy : 0 ≤ f y := by linarith
  change 0 ≤ f (‖x‖⁻¹ • x) at hy
  rw [map_smul] at hy
  exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hc)).mp hy

/-- The unital GNS cyclic vector is the completion class of the algebra
unit; no normalized-state hypothesis is required. -/
def unitalGNSCyclicVector (f : A →ₚ[ℂ] ℂ) : f.GNS :=
  (f.toPreGNS 1 : f.GNS)

@[simp] theorem unitalGNS_apply_cyclic (f : A →ₚ[ℂ] ℂ) (a : A) :
    f.gnsStarAlgHom a (unitalGNSCyclicVector f) = (f.toPreGNS a : f.GNS) := by
  change f.gnsNonUnitalStarAlgHom a (f.toPreGNS 1) = (f.toPreGNS a : f.GNS)
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe]
  simp [PositiveLinearMap.leftMulMapPreGNS]

@[simp] theorem unitalGNS_cyclic_pairing (f : A →ₚ[ℂ] ℂ) (a : A) :
    ⟪unitalGNSCyclicVector f, f.gnsStarAlgHom a (unitalGNSCyclicVector f)⟫_ℂ = f a := by
  rw [unitalGNS_apply_cyclic]
  simp [unitalGNSCyclicVector, Completion.inner_coe, PositiveLinearMap.preGNS_inner_def]

theorem unitalGNS_cyclic_denseRange (f : A →ₚ[ℂ] ℂ) :
    DenseRange (fun a : A => f.gnsStarAlgHom a (unitalGNSCyclicVector f)) := by
  simp only [unitalGNS_apply_cyclic]
  exact Completion.denseRange_coe.comp f.toPreGNS.surjective.denseRange
    (Completion.continuous_coe f.PreGNS)

/-- A real functional on selfadjoint elements has a unique complex-linear
extension, by the actual real and imaginary part decomposition. -/
def complexifySelfAdjointFunctional (g : selfAdjoint A →ₗ[ℝ] ℝ) : A →ₗ[ℂ] ℂ where
  toFun a := (g (realPart a) : ℂ) + Complex.I * (g (imaginaryPart a) : ℂ)
  map_add' a b := by
    simp only [map_add, Complex.ofReal_add]
    ring
  map_smul' z a := by
    apply Complex.ext <;>
      simp [realPart_smul, imaginaryPart_smul, map_smul, smul_eq_mul,
        Complex.mul_re, Complex.mul_im]

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem complexifySelfAdjointFunctional_selfAdjoint
    (g : selfAdjoint A →ₗ[ℝ] ℝ) (a : selfAdjoint A) :
    complexifySelfAdjointFunctional g (a : A) = (g a : ℂ) := by
  simp [complexifySelfAdjointFunctional, a.property.imaginaryPart,
    selfAdjoint.realPart_coe]

/-- The complexification of a positive real functional on the selfadjoint
part is an actual positive complex-linear map. -/
def positiveComplexifySelfAdjointFunctional (g : StrongDual ℝ (selfAdjoint A))
    (hg : ∀ a : selfAdjoint A, 0 ≤ (a : A) → 0 ≤ g a) : A →ₚ[ℂ] ℂ where
  toLinearMap := complexifySelfAdjointFunctional g.toLinearMap
  monotone' := by
    intro a b hab
    apply sub_nonneg.mp
    change 0 ≤ complexifySelfAdjointFunctional g.toLinearMap b -
      complexifySelfAdjointFunctional g.toLinearMap a
    rw [← (complexifySelfAdjointFunctional g.toLinearMap).map_sub]
    have h := sub_nonneg.mpr hab
    have hsa : IsSelfAdjoint (b - a) := .of_nonneg h
    have hreal : 0 ≤ g (realPart (b - a)) :=
      hg _ (by simpa only [hsa.coe_realPart] using h)
    simpa [complexifySelfAdjointFunctional, hsa.imaginaryPart] using
      (Complex.zero_le_real.mpr hreal)

private def selfAdjointPairFst : selfAdjoint (A × A) →L[ℝ] selfAdjoint A :=
  ({ toFun := fun x => ⟨(x : A × A).1, congrArg Prod.fst x.property⟩
     map_add' := fun _ _ => Subtype.ext rfl
     map_smul' := fun _ _ => Subtype.ext rfl } :
    selfAdjoint (A × A) →ₗ[ℝ] selfAdjoint A).mkContinuous 1 fun x => by
      simpa using norm_fst_le (x : A × A)

private def selfAdjointPairSnd : selfAdjoint (A × A) →L[ℝ] selfAdjoint A :=
  ({ toFun := fun x => ⟨(x : A × A).2, congrArg Prod.snd x.property⟩
     map_add' := fun _ _ => Subtype.ext rfl
     map_smul' := fun _ _ => Subtype.ext rfl } :
    selfAdjoint (A × A) →ₗ[ℝ] selfAdjoint A).mkContinuous 1 fun x => by
      simpa using norm_snd_le (x : A × A)

private def selfAdjointPairInl : selfAdjoint A →L[ℝ] selfAdjoint (A × A) :=
  ({ toFun := fun x => ⟨((x : A), 0), by ext <;> simp⟩
     map_add' := fun _ _ => Subtype.ext (Prod.ext rfl (zero_add _).symm)
     map_smul' := fun _ _ => Subtype.ext (Prod.ext rfl (smul_zero _).symm) } :
    selfAdjoint A →ₗ[ℝ] selfAdjoint (A × A)).mkContinuous 1 fun x => by
      simp [Prod.norm_def]

private def selfAdjointPairInr : selfAdjoint A →L[ℝ] selfAdjoint (A × A) :=
  ({ toFun := fun x => ⟨(0, (x : A)), by ext <;> simp⟩
     map_add' := fun _ _ => Subtype.ext (Prod.ext (zero_add _).symm rfl)
     map_smul' := fun _ _ => Subtype.ext (Prod.ext (smul_zero _).symm rfl) } :
    selfAdjoint A →ₗ[ℝ] selfAdjoint (A × A)).mkContinuous 1 fun x => by
      simp [Prod.norm_def]

private def selfAdjointJordanEmbedding :
    selfAdjoint A × ℝ →ₗ[ℝ] selfAdjoint (A × A) :=
  (selfAdjointPairInl.toLinearMap - selfAdjointPairInr.toLinearMap).coprod
    (LinearMap.toSpanSingleton ℝ (selfAdjoint (A × A)) 1)

omit [PartialOrder A] [StarOrderedRing A] in
private theorem selfAdjointJordanEmbedding_apply (x : selfAdjoint A) (r : ℝ) :
    (selfAdjointJordanEmbedding (x, r) : A × A) =
      ((x : A) + r • (1 : A), -(x : A) + r • (1 : A)) := by
  ext <;> simp [selfAdjointJordanEmbedding, selfAdjointPairInl, selfAdjointPairInr]

/-- Every real bounded functional on the selfadjoint part of a unital
C⋆-algebra is a difference of positive real bounded functionals. The proof
is the real Hahn–Banach order-unit argument in the selfadjoint part of the
product algebra. -/
theorem exists_positive_real_dual_decomposition [Nontrivial A]
    (f : StrongDual ℝ (selfAdjoint A)) :
    ∃ g h : StrongDual ℝ (selfAdjoint A),
      (∀ x : selfAdjoint A, 0 ≤ (x : A) → 0 ≤ g x) ∧
      (∀ x : selfAdjoint A, 0 ≤ (x : A) → 0 ≤ h x) ∧ f = g - h := by
  let V : Type _ := selfAdjoint A
  let W : Type _ := selfAdjoint (A × A)
  have hu : ‖(1 : V)‖ = 1 := norm_one (α := A)
  obtain ⟨ν, _hνnorm, hνunit⟩ := exists_dual_vector ℝ (1 : V) (by simp [hu])
  have hν1 : ν (1 : V) = 1 := by simpa [hu] using hνunit
  let K := ‖f‖
  let T := selfAdjointJordanEmbedding (A := A)
  let S := T.range
  let L₀ : W →L[ℝ] ℝ :=
    (1 / 2 : ℝ) • (f.comp (selfAdjointPairFst - selfAdjointPairSnd)) +
      (K / 2) • (ν.comp (selfAdjointPairFst + selfAdjointPairSnd))
  have hLT (x : V) (r : ℝ) : L₀ (T (x, r)) = f x + r * K := by
    have hfst : selfAdjointPairFst (T (x, r)) = x + r • (1 : V) := by
      ext
      change ((selfAdjointPairFst (T (x, r)) : selfAdjoint A) : A) =
        ((x : selfAdjoint A) : A) + r • (1 : A)
      simp [T, selfAdjointJordanEmbedding, selfAdjointPairFst,
        selfAdjointPairInl, selfAdjointPairInr]
    have hsnd : selfAdjointPairSnd (T (x, r)) = -x + r • (1 : V) := by
      ext
      change ((selfAdjointPairSnd (T (x, r)) : selfAdjoint A) : A) =
        -((x : selfAdjoint A) : A) + r • (1 : A)
      simp [T, selfAdjointJordanEmbedding, selfAdjointPairSnd,
        selfAdjointPairInl, selfAdjointPairInr]
    change (1 / 2 : ℝ) * f (selfAdjointPairFst (T (x, r)) - selfAdjointPairSnd (T (x, r))) +
      (K / 2) * ν (selfAdjointPairFst (T (x, r)) + selfAdjointPairSnd (T (x, r))) = _
    rw [hfst, hsnd]
    have hνneg : ν (-x) = -ν x := ν.map_neg x
    simp only [map_sub, map_add, map_neg, map_smul, smul_eq_mul, hν1, hνneg]
    ring
  have huS : (1 : W) ∈ S := by
    refine ⟨(0, 1), ?_⟩
    ext <;> simp [T, selfAdjointJordanEmbedding, selfAdjointPairInl, selfAdjointPairInr]
  have hLunit : L₀ (1 : W) = K := by
    have huT : T (0, 1) = (1 : W) := by
      ext <;> simp [T, selfAdjointJordanEmbedding, selfAdjointPairInl, selfAdjointPairInr]
    simpa only [huT, map_zero, zero_add, one_mul] using hLT 0 1
  have hLpos (s : W) (hs : s ∈ S) (hs0 : 0 ≤ (s : A × A)) : 0 ≤ L₀ s := by
    obtain ⟨⟨x, r⟩, rfl⟩ := hs
    rw [hLT]
    have hfst : 0 ≤ (x : A) + r • (1 : A) := by
      simpa [T, selfAdjointJordanEmbedding, selfAdjointPairInl, selfAdjointPairInr] using hs0.1
    have hsnd : 0 ≤ -(x : A) + r • (1 : A) := by
      simpa [T, selfAdjointJordanEmbedding, selfAdjointPairInl, selfAdjointPairInr] using hs0.2
    have hlo : -(algebraMap ℝ A r) ≤ (x : A) := by
      rw [Algebra.algebraMap_eq_smul_one]
      exact neg_le_iff_add_nonneg.mpr (by simpa only [add_comm] using hfst)
    have hup : (x : A) ≤ algebraMap ℝ A r := by
      rw [Algebra.algebraMap_eq_smul_one]
      apply sub_nonneg.mp
      simpa only [sub_eq_add_neg, add_comm] using hsnd
    have hxr : ‖x‖ ≤ r := selfAdjoint_norm_le_of_order_bounds x.property hlo hup
    have hfx : -(K * ‖x‖) ≤ f x := by
      exact (abs_le.mp (f.le_opNorm x)).1
    have hK : 0 ≤ K := f.opNorm_nonneg
    nlinarith
  let L : S →ₗ[ℝ] ℝ := L₀.toLinearMap.comp S.subtype
  have hLbound : ∀ s : S, ‖L s‖ ≤ K * ‖s‖ := by
    intro s
    have hplusmem : ‖s‖ • (1 : W) + (s : W) ∈ S :=
      S.add_mem (S.smul_mem _ huS) s.property
    have hminusmem : ‖s‖ • (1 : W) - (s : W) ∈ S :=
      S.sub_mem (S.smul_mem _ huS) s.property
    have hplus0 : 0 ≤ ((‖s‖ • (1 : W) + (s : W) : W) : A × A) := by
      change 0 ≤ ‖s‖ • (1 : A × A) + ((s : W) : A × A)
      have hnorm : ‖s‖ = ‖((s : W) : A × A)‖ := rfl
      rw [hnorm]
      have hb := (s : W).property.neg_algebraMap_norm_le_self
      rw [Algebra.algebraMap_eq_smul_one] at hb
      simpa only [add_comm] using (neg_le_iff_add_nonneg.mp hb)
    have hminus0 : 0 ≤ ((‖s‖ • (1 : W) - (s : W) : W) : A × A) := by
      change 0 ≤ ‖s‖ • (1 : A × A) - ((s : W) : A × A)
      have hnorm : ‖s‖ = ‖((s : W) : A × A)‖ := rfl
      rw [hnorm]
      apply sub_nonneg.mpr
      simpa only [Algebra.algebraMap_eq_smul_one] using
        (s : W).property.le_algebraMap_norm_self
    have hp := hLpos _ hplusmem hplus0
    have hm := hLpos _ hminusmem hminus0
    simp only [map_add, map_sub, map_smul, hLunit, smul_eq_mul] at hp hm
    exact abs_le.mpr ⟨by change -(K * ‖s‖) ≤ L₀ s; nlinarith,
      by change L₀ s ≤ K * ‖s‖; nlinarith⟩
  let k : NNReal := ⟨K, f.opNorm_nonneg⟩
  let p : Seminorm ℝ W := k • normSeminorm ℝ W
  have hp (x : W) : p x = K * ‖x‖ := rfl
  have hpcont : Continuous p := continuous_norm.const_smul k
  have hLdom (s : S) : ‖L s‖ ≤ p (s : W) := by
    rw [hp]
    change ‖L s‖ ≤ K * ‖s‖
    exact hLbound s
  obtain ⟨G, hGext, hGbound⟩ :=
    Module.Dual.exists_continuous_extension_of_le_seminorm S L hpcont hLdom
  have hGunitK : G (1 : W) = K := (hGext ⟨1, huS⟩).trans hLunit
  have hGb (x : W) : ‖G x‖ ≤ K * ‖x‖ := by
    simpa only [hp] using hGbound x
  have hGnorm : ‖G‖ = K := by
    apply le_antisymm (G.opNorm_le_bound f.opNorm_nonneg hGb)
    have huW : ‖(1 : W)‖ = 1 := norm_one (α := A × A)
    have hb := G.le_opNorm (1 : W)
    have hKnorm : ‖K‖ = K := Real.norm_of_nonneg f.opNorm_nonneg
    simpa only [hGunitK, hKnorm, huW, mul_one] using hb
  have hGunit : G (1 : W) = ‖G‖ := by
    exact hGunitK.trans hGnorm.symm
  let g := G.comp (selfAdjointPairInl (A := A))
  let h := G.comp (selfAdjointPairInr (A := A))
  refine ⟨g, h, ?_, ?_, ?_⟩
  · intro x hx
    apply selfAdjoint_dual_nonneg_of_unit_eq_norm G hGunit
    exact ⟨hx, le_rfl⟩
  · intro x hx
    apply selfAdjoint_dual_nonneg_of_unit_eq_norm G hGunit
    exact ⟨le_rfl, hx⟩
  · ext x
    have hTx : T (x, 0) ∈ S := ⟨(x, 0), rfl⟩
    have hext := hGext ⟨T (x, 0), hTx⟩
    have hval := hLT x 0
    simpa [L, g, h, T, selfAdjointJordanEmbedding, map_sub, map_add] using
      (hext.trans hval).symm

private def selfAdjointSubtypeCLM : selfAdjoint A →L[ℝ] A :=
  (selfAdjoint.submodule ℝ A).subtypeL

/-- Every complex bounded functional on a nontrivial unital C⋆-algebra is
a complex linear combination of four actual positive functionals. -/
theorem exists_four_positive_functionals_decomposition [Nontrivial A]
    (f : StrongDual ℂ A) :
    ∃ p q r s : A →ₚ[ℂ] ℂ,
      ∀ a : A, f a = p a - q a + Complex.I * (r a - s a) := by
  let fre : StrongDual ℝ (selfAdjoint A) :=
    Complex.reCLM.comp ((f.restrictScalars ℝ).comp selfAdjointSubtypeCLM)
  let fim : StrongDual ℝ (selfAdjoint A) :=
    Complex.imCLM.comp ((f.restrictScalars ℝ).comp selfAdjointSubtypeCLM)
  obtain ⟨gp, gq, hgp, hgq, hfre⟩ := exists_positive_real_dual_decomposition fre
  obtain ⟨gr, gs, hgr, hgs, hfim⟩ := exists_positive_real_dual_decomposition fim
  let p := positiveComplexifySelfAdjointFunctional gp hgp
  let q := positiveComplexifySelfAdjointFunctional gq hgq
  let r := positiveComplexifySelfAdjointFunctional gr hgr
  let s := positiveComplexifySelfAdjointFunctional gs hgs
  let g : A →ₗ[ℂ] ℂ := p.toLinearMap - q.toLinearMap +
    Complex.I • (r.toLinearMap - s.toLinearMap)
  have hsa (a : selfAdjoint A) : f (a : A) = g (a : A) := by
    have hre : (f (a : A)).re = gp a - gq a := by
      exact congrArg (fun k : StrongDual ℝ (selfAdjoint A) => k a) hfre
    have him : (f (a : A)).im = gr a - gs a := by
      exact congrArg (fun k : StrongDual ℝ (selfAdjoint A) => k a) hfim
    change f (a : A) =
      complexifySelfAdjointFunctional gp.toLinearMap (a : A) -
        complexifySelfAdjointFunctional gq.toLinearMap (a : A) +
          Complex.I * (complexifySelfAdjointFunctional gr.toLinearMap (a : A) -
            complexifySelfAdjointFunctional gs.toLinearMap (a : A))
    simp only [complexifySelfAdjointFunctional_selfAdjoint]
    apply Complex.ext <;> simp [hre, him]
  refine ⟨p, q, r, s, fun a => ?_⟩
  change f a = g a
  calc
    f a = f ((realPart a : selfAdjoint A) : A) +
        Complex.I * f ((imaginaryPart a : selfAdjoint A) : A) := by
      conv_lhs => rw [← realPart_add_I_smul_imaginaryPart a]
      simp
    _ = g ((realPart a : selfAdjoint A) : A) +
        Complex.I * g ((imaginaryPart a : selfAdjoint A) : A) := by
      rw [hsa, hsa]
    _ = g a := by
      conv_rhs => rw [← realPart_add_I_smul_imaginaryPart a]
      simp

end BC4lean.KKTheory
