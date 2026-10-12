import BC4lean.GroupUniverseParityUnits

/-! # Genuine equivariant functoriality of the full parity groups

Both algebra maps are independently defined by actual standard even
homomorphism cycles: first-algebra pullback multiplies on the left and
second-algebra pushforward multiplies on the right. Their real cycle
composition and standard units prove the functor laws. The actual parity
associativity cases prove source/coefficient naturality and middle
balancing. Coefficient universes are independent, and the common module
universe includes precisely the carriers introduced by real tensors.
-/

noncomputable section
universe uΓ uA uB uC uD u
namespace BC4lean.KKTheory.GroupUniverseParityFunctoriality
open GroupUniverseParityGroup GroupUniverseParityUnits

section Pairs
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

/-- Contravariance is actual left multiplication by the standard target
module cycle carrying the given equivariant nonunital homomorphism. -/
def sourcePullback (p : Bool) (f : A →⋆ₙₐ[ℂ] B)
    (hact : ∀ k a, f (α.automorphism k a) = β.automorphism k (f a))
    (x : KKParityGroup.{uΓ,uB,uC,max u (max uA (max uB uC))} p β γ) :
    KKParityGroup.{uΓ,uA,uC,max u (max uA (max uB uC))} p α γ :=
  leftEvenProduct p
    (GroupUniverseParityHomCycle.homClass.{uΓ,uA,uB,max u (max uA (max uB uC))} f hact) x

/-- Covariance is actual right multiplication by the same genuine even
homomorphism cycle, without a unit-preserving or nondegeneracy hypothesis. -/
def coefficientPushforward (p : Bool) (f : B →⋆ₙₐ[ℂ] C)
    (hact : ∀ k b, f (β.automorphism k b) = γ.automorphism k (f b))
    (x : KKParityGroup.{uΓ,uA,uB,max u (max uA (max uB uC))} p α β) :
    KKParityGroup.{uΓ,uA,uC,max u (max uA (max uB uC))} p α γ :=
  rightEvenProduct p x
    (GroupUniverseParityHomCycle.homClass.{uΓ,uB,uC,max u (max uA (max uB uC))} f hact)

theorem sourcePullback_add (p : Bool) (f : A →⋆ₙₐ[ℂ] B)
    (hact : ∀ k a, f (α.automorphism k a) = β.automorphism k (f a))
    (x y : KKParityGroup.{uΓ,uB,uC,max u (max uA (max uB uC))} p β γ) :
    sourcePullback p f hact (x + y) = sourcePullback p f hact x + sourcePullback p f hact y := by
  cases p
  · exact GroupUniverseParityProduct.evenProduct_add_second _ x y
  · exact GroupUniverseParityProduct.evenOddProduct_add_second _ x y

theorem coefficientPushforward_add (p : Bool) (f : B →⋆ₙₐ[ℂ] C)
    (hact : ∀ k b, f (β.automorphism k b) = γ.automorphism k (f b))
    (x y : KKParityGroup.{uΓ,uA,uB,max u (max uA (max uB uC))} p α β) :
    coefficientPushforward p f hact (x + y) =
      coefficientPushforward p f hact x + coefficientPushforward p f hact y := by
  cases p
  · exact GroupUniverseParityProduct.evenProduct_add_first x y _
  · exact GroupUniverseOddFirstParityProduct.oddEvenProduct_add_first x y _

def sourcePullbackHom (p : Bool) (f : A →⋆ₙₐ[ℂ] B)
    (hact : ∀ k a, f (α.automorphism k a) = β.automorphism k (f a)) :
    KKParityGroup.{uΓ,uB,uC,max u (max uA (max uB uC))} p β γ →+
    KKParityGroup.{uΓ,uA,uC,max u (max uA (max uB uC))} p α γ :=
  AddMonoidHom.mk' (sourcePullback p f hact) (sourcePullback_add p f hact)

def coefficientPushforwardHom (p : Bool) (f : B →⋆ₙₐ[ℂ] C)
    (hact : ∀ k b, f (β.automorphism k b) = γ.automorphism k (f b)) :
    KKParityGroup.{uΓ,uA,uB,max u (max uA (max uB uC))} p α β →+
    KKParityGroup.{uΓ,uA,uC,max u (max uA (max uB uC))} p α γ :=
  AddMonoidHom.mk' (coefficientPushforward p f hact) (coefficientPushforward_add p f hact)

end Pairs

section Identities
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

theorem sourcePullback_id (p : Bool)
    (x : KKParityGroup.{uΓ,uA,uB,max u (max uA uB)} p α β) :
    sourcePullback.{uΓ,uA,uA,uB,u} p (NonUnitalStarAlgHom.id ℂ A) (fun _ _ => rfl) x = x := by
  unfold sourcePullback
  rw [homClass_id]
  exact left_identity p x

theorem coefficientPushforward_id (p : Bool)
    (x : KKParityGroup.{uΓ,uA,uB,max u (max uA uB)} p α β) :
    coefficientPushforward.{uΓ,uA,uB,uB,u} p
      (NonUnitalStarAlgHom.id ℂ B) (fun _ _ => rfl) x = x := by
  unfold coefficientPushforward
  rw [homClass_id]
  exact right_identity p x

end Identities

section Triples
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
  [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C] [TopologicalSpace.SeparableSpace D]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {γ : CStarAlgebraAction Γ C} {η : CStarAlgebraAction Γ D}

/-- Actual first-algebra maps compose contravariantly. -/
theorem sourcePullback_comp (p : Bool) (f : A →⋆ₙₐ[ℂ] B) (g : B →⋆ₙₐ[ℂ] C)
    (hactf : ∀ k a, f (α.automorphism k a) = β.automorphism k (f a))
    (hactg : ∀ k b, g (β.automorphism k b) = γ.automorphism k (g b))
    (x : KKParityGroup.{uΓ,uC,uD,max u (max uA (max uB (max uC uD)))} p γ η) :
    sourcePullback.{uΓ,uA,uB,uD,max u uC} p f hactf
      (sourcePullback.{uΓ,uB,uC,uD,max u uA} p g hactg x) =
    sourcePullback.{uΓ,uA,uC,uD,max u uB} p (g.comp f)
      (fun k a => by change g (f (α.automorphism k a)) = _; rw [hactf, hactg]) x := by
  unfold sourcePullback
  cases p
  · rw [leftEvenProduct, ← GroupUniverseParityProduct.evenProduct_assoc,
      GroupUniverseParityHomCycle.homClass_product]
  · rw [leftEvenProduct, ← GroupUniverseParityProduct.evenEvenOddProduct_assoc,
      GroupUniverseParityHomCycle.homClass_product]

/-- Actual second-algebra maps compose covariantly. -/
theorem coefficientPushforward_comp (p : Bool) (f : B →⋆ₙₐ[ℂ] C) (g : C →⋆ₙₐ[ℂ] D)
    (hactf : ∀ k b, f (β.automorphism k b) = γ.automorphism k (f b))
    (hactg : ∀ k c, g (γ.automorphism k c) = η.automorphism k (g c))
    (x : KKParityGroup.{uΓ,uA,uB,max u (max uA (max uB (max uC uD)))} p α β) :
    coefficientPushforward.{uΓ,uA,uC,uD,max u uB} p g hactg
      (coefficientPushforward.{uΓ,uA,uB,uC,max u uD} p f hactf x) =
    coefficientPushforward.{uΓ,uA,uB,uD,max u uC} p (g.comp f)
      (fun k b => by change g (f (β.automorphism k b)) = _; rw [hactf, hactg]) x := by
  unfold coefficientPushforward
  cases p
  · rw [rightEvenProduct, GroupUniverseParityProduct.evenProduct_assoc,
      GroupUniverseParityHomCycle.homClass_product]
  · rw [rightEvenProduct, GroupUniverseOddFirstParityProduct.oddEvenEvenProduct_assoc,
      GroupUniverseParityHomCycle.homClass_product]

/-- The actual source and coefficient maps commute. -/
theorem sourcePullback_coefficientPushforward (p : Bool)
    (f : A →⋆ₙₐ[ℂ] B) (g : C →⋆ₙₐ[ℂ] D)
    (hactf : ∀ k a, f (α.automorphism k a) = β.automorphism k (f a))
    (hactg : ∀ k c, g (γ.automorphism k c) = η.automorphism k (g c))
    (x : KKParityGroup.{uΓ,uB,uC,max u (max uA (max uB (max uC uD)))} p β γ) :
    coefficientPushforward.{uΓ,uA,uC,uD,max u uB} p g hactg
      (sourcePullback.{uΓ,uA,uB,uC,max u uD} p f hactf x) =
    sourcePullback.{uΓ,uA,uB,uD,max u uC} p f hactf
      (coefficientPushforward.{uΓ,uB,uC,uD,max u uA} p g hactg x) := by
  cases p
  · exact GroupUniverseParityProduct.evenProduct_assoc _ _ _
  · exact GroupUniverseOddFirstParityProduct.evenOddEvenProduct_assoc _ _ _

/-- Contravariance respects every genuine parity product. -/
theorem sourcePullback_product (p q : Bool) (f : A →⋆ₙₐ[ℂ] B)
    (hact : ∀ k a, f (α.automorphism k a) = β.automorphism k (f a))
    (x : KKParityGroup.{uΓ,uB,uC,max u (max uA (max uB (max uC uD)))} p β γ)
    (y : KKParityGroup.{uΓ,uC,uD,max u (max uA (max uB (max uC uD)))} q γ η) :
    sourcePullback.{uΓ,uA,uB,uD,max u uC} (Bool.xor p q) f hact
      (GroupUniverseCommonParityProduct.product.{uΓ,uB,uC,uD,max u uA} p q x y) =
    GroupUniverseCommonParityProduct.product.{uΓ,uA,uC,uD,max u uB} p q
      (sourcePullback.{uΓ,uA,uB,uC,max u uD} p f hact x) y := by
  cases p <;> cases q
  · exact (GroupUniverseParityProduct.evenProduct_assoc _ _ _).symm
  · exact (GroupUniverseParityProduct.evenEvenOddProduct_assoc _ _ _).symm
  · exact (GroupUniverseOddFirstParityProduct.evenOddEvenProduct_assoc _ _ _).symm
  · exact (GroupUniverseOddFirstParityProduct.evenOddOddProduct_assoc _ _ _).symm

/-- Covariance respects every genuine parity product. -/
theorem coefficientPushforward_product (p q : Bool) (f : C →⋆ₙₐ[ℂ] D)
    (hact : ∀ k c, f (γ.automorphism k c) = η.automorphism k (f c))
    (x : KKParityGroup.{uΓ,uA,uB,max u (max uA (max uB (max uC uD)))} p α β)
    (y : KKParityGroup.{uΓ,uB,uC,max u (max uA (max uB (max uC uD)))} q β γ) :
    coefficientPushforward.{uΓ,uA,uC,uD,max u uB} (Bool.xor p q) f hact
      (GroupUniverseCommonParityProduct.product.{uΓ,uA,uB,uC,max u uD} p q x y) =
    GroupUniverseCommonParityProduct.product.{uΓ,uA,uB,uD,max u uC} p q x
      (coefficientPushforward.{uΓ,uB,uC,uD,max u uA} q f hact y) := by
  cases p <;> cases q
  · exact GroupUniverseParityProduct.evenProduct_assoc _ _ _
  · exact GroupUniverseOddFirstParityProduct.evenOddEvenProduct_assoc _ _ _
  · exact GroupUniverseOddFirstParityProduct.oddEvenEvenProduct_assoc _ _ _
  · exact GroupUniverseOddFirstParityProduct.oddOddEvenProduct_assoc _ _ _

/-- The middle coefficient map is balanced by the genuine first-algebra map. -/
theorem coefficientPushforward_product_eq_sourcePullback (p q : Bool) (f : B →⋆ₙₐ[ℂ] C)
    (hact : ∀ k b, f (β.automorphism k b) = γ.automorphism k (f b))
    (x : KKParityGroup.{uΓ,uA,uB,max u (max uA (max uB (max uC uD)))} p α β)
    (y : KKParityGroup.{uΓ,uC,uD,max u (max uA (max uB (max uC uD)))} q γ η) :
    GroupUniverseCommonParityProduct.product.{uΓ,uA,uC,uD,max u uB} p q
      (coefficientPushforward.{uΓ,uA,uB,uC,max u uD} p f hact x) y =
    GroupUniverseCommonParityProduct.product.{uΓ,uA,uB,uD,max u uC} p q x
      (sourcePullback.{uΓ,uB,uC,uD,max u uA} q f hact y) := by
  cases p <;> cases q
  · exact GroupUniverseParityProduct.evenProduct_assoc _ _ _
  · exact GroupUniverseParityProduct.evenEvenOddProduct_assoc _ _ _
  · exact GroupUniverseOddFirstParityProduct.oddEvenEvenProduct_assoc _ _ _
  · exact GroupUniverseOddFirstParityProduct.oddEvenOddProduct_assoc _ _ _

end Triples
end BC4lean.KKTheory.GroupUniverseParityFunctoriality
