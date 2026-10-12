import BC4lean.KasparovCountableSelection

/-! # Explicit discrete technical-theorem test scheduling

The normalizer sequence and its grading images occupy two tracks.
The second-algebra AU, the whole discrete family, their stars, and their
grading images occupy six tracks. The compact band tests combine these
with the first-algebra AU. Every specified test has an explicit index;
no ambient endomorphism separability is used.
-/

noncomputable section
namespace BC4lean.KKTheory

/-- Interleave finitely many countable test tracks by an exact quotient
and remainder schedule. -/
def periodicCountableTests {A : Type*} (r : ℕ) (hr : 0 < r)
    (F : Fin r → ℕ → A) (n : ℕ) : A := F ⟨n % r, Nat.mod_lt n hr⟩ (n / r)

theorem periodicCountableTests_at {A : Type*} (r : ℕ) (hr : 0 < r)
    (F : Fin r → ℕ → A) (k : ℕ) (i : Fin r) :
    periodicCountableTests r hr F (r * k + i.val) = F i k := by
  have hmod : (r * k + i.val) % r = i.val := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt i.isLt]
  have hdiv : (r * k + i.val) / r = k := by
    rw [Nat.mul_add_div hr, Nat.div_eq_of_lt i.isLt, Nat.add_zero]
  simp only [periodicCountableTests, hmod, hdiv, Fin.eta]

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- Both a dense normalizer track and its actual grading image are tested. -/
def kasparovNormalizerTests (σ : A ≃⋆ₐ[ℂ] A) (δ : ℕ → A) : ℕ → A :=
  periodicCountableTests 2 (by decide) (fun i k => if i.val = 0 then δ k else σ (δ k))

theorem kasparovNormalizerTests_original (σ : A ≃⋆ₐ[ℂ] A) (δ : ℕ → A) (k : ℕ) :
    kasparovNormalizerTests σ δ (2 * k) = δ k := by
  simpa [kasparovNormalizerTests] using
    periodicCountableTests_at 2 (by decide) (fun i k => if i.val = 0 then δ k else σ (δ k)) k 0

theorem kasparovNormalizerTests_grading (σ : A ≃⋆ₐ[ℂ] A) (δ : ℕ → A) (k : ℕ) :
    kasparovNormalizerTests σ δ (2 * k + 1) = σ (δ k) := by
  simpa only [kasparovNormalizerTests, Fin.val_one, if_neg (by decide : (1 : ℕ) ≠ 0)] using
    periodicCountableTests_at 2 (by decide) (fun i k => if i.val = 0 then δ k else σ (δ k)) k 1

/-- E₂ approximate-unit values and every discrete family value, with
their star and grading images, enter the compact-product schedule. -/
def kasparovFamilyTests (σ : A ≃⋆ₐ[ℂ] A) (q₂ f : ℕ → A) : ℕ → A :=
  periodicCountableTests 6 (by decide) (fun i k =>
    if i.val = 0 then q₂ k else if i.val = 1 then f k else
      if i.val = 2 then star (f k) else if i.val = 3 then σ (f k) else
        if i.val = 4 then σ (star (f k)) else σ (q₂ k))

theorem kasparovFamilyTests_at (σ : A ≃⋆ₐ[ℂ] A) (q₂ f : ℕ → A) (k : ℕ) :
    kasparovFamilyTests σ q₂ f (6 * k) = q₂ k ∧
    kasparovFamilyTests σ q₂ f (6 * k + 1) = f k ∧
    kasparovFamilyTests σ q₂ f (6 * k + 2) = star (f k) ∧
    kasparovFamilyTests σ q₂ f (6 * k + 3) = σ (f k) ∧
    kasparovFamilyTests σ q₂ f (6 * k + 4) = σ (star (f k)) ∧
    kasparovFamilyTests σ q₂ f (6 * k + 5) = σ (q₂ k) := by
  have h := periodicCountableTests_at 6 (by decide)
    (fun i k => if i.val = 0 then q₂ k else if i.val = 1 then f k else
      if i.val = 2 then star (f k) else if i.val = 3 then σ (f k) else
        if i.val = 4 then σ (star (f k)) else σ (q₂ k)) k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [kasparovFamilyTests] using h 0
  · simpa [kasparovFamilyTests] using h 1
  · simpa [kasparovFamilyTests] using h 2
  · simpa [kasparovFamilyTests] using h 3
  · simpa [kasparovFamilyTests] using h 4
  · simpa [kasparovFamilyTests] using h 5

/-- All band commutator tests occupy three explicit countable tracks:
normalizers, the first-algebra AU, and E₂/discrete-family values. -/
def kasparovBandTests (δ q₁ b : ℕ → A) : ℕ → A :=
  periodicCountableTests 3 (by decide)
    (fun i k => if i.val = 0 then δ k else if i.val = 1 then q₁ k else b k)

omit [NonUnitalCStarAlgebra A] in
theorem kasparovBandTests_at (δ q₁ b : ℕ → A) (k : ℕ) :
    kasparovBandTests δ q₁ b (3 * k) = δ k ∧
    kasparovBandTests δ q₁ b (3 * k + 1) = q₁ k ∧
    kasparovBandTests δ q₁ b (3 * k + 2) = b k := by
  have h := periodicCountableTests_at 3 (by decide)
    (fun i k => if i.val = 0 then δ k else if i.val = 1 then q₁ k else b k) k
  refine ⟨?_, ?_, ?_⟩
  · simpa [kasparovBandTests] using h 0
  · simpa [kasparovBandTests] using h 1
  · simpa [kasparovBandTests] using h 2

/-- A dense countable normalizer family and its grading images remain
dense in the required original and grading-image test sets. -/
theorem kasparovNormalizerTests_closure
    (σ : A ≃⋆ₐ[ℂ] A) (δ : ℕ → A) (Δ : Set A) (hΔ : Δ ⊆ closure (Set.range δ)) :
    Δ ⊆ closure (Set.range (kasparovNormalizerTests σ δ)) ∧
      σ '' Δ ⊆ closure (Set.range (kasparovNormalizerTests σ δ)) := by
  have horiginal : Set.range δ ⊆ Set.range (kasparovNormalizerTests σ δ) := by
    rintro _ ⟨k, rfl⟩
    exact ⟨2 * k, kasparovNormalizerTests_original σ δ k⟩
  have hgrading : σ '' Set.range δ ⊆ Set.range (kasparovNormalizerTests σ δ) := by
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨2 * k + 1, kasparovNormalizerTests_grading σ δ k⟩
  refine ⟨hΔ.trans (closure_mono horiginal), ?_⟩
  exact (Set.image_mono hΔ).trans
    ((image_closure_subset_closure_image (NonUnitalStarAlgHom.isometry σ σ.injective).continuous).trans (closure_mono hgrading))

end BC4lean.KKTheory
