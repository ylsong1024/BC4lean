import Mathlib.Algebra.Group.Subgroup.Ker

/-! # Identifying a kernel from an additive product decomposition -/
namespace BC4lean.OperatorKTheory
variable {G H J : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup J]

/-- If the first coordinate of an additive product decomposition is `f`, its kernel
is canonically the second factor. -/
def kernelProductEquiv (e : G ≃+ H × J) (f : G →+ H) (h : ∀ x, (e x).1 = f x) :
    f.ker ≃+ J where
  toFun x := (e x.val).2
  invFun y := ⟨e.symm (0, y), by
    change f (e.symm (0, y)) = 0
    rw [← h, e.apply_symm_apply]⟩
  left_inv x := by
    apply Subtype.ext
    apply e.injective
    rw [e.apply_symm_apply]
    apply Prod.ext
    · exact (h x.val |>.trans x.property).symm
    · rfl
  right_inv y := by simp
  map_add' x y := by
    change (e (x.val + y.val)).2 = (e x.val).2 + (e y.val).2
    rw [map_add]
    rfl

end BC4lean.OperatorKTheory
