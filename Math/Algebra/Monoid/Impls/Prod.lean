import Math.Algebra.Semigroup.Impls.Prod
import Math.Algebra.Monoid.Defs
import Math.Algebra.Monoid.Char

instance [AddMonoidOps α] [AddMonoidOps β] [IsAddMonoid α] [IsAddMonoid β] : IsAddMonoid (α × β) where
  zero_nsmul := by
    intro f; ext <;>
    apply zero_nsmul
  succ_nsmul := by
    intro n f; ext <;>
    apply succ_nsmul

instance [MonoidOps α] [MonoidOps β] [IsMonoid α] [IsMonoid β] : IsMonoid (α × β)  :=
  inferInstanceAs (IsMonoid (MulOfAdd (AddOfMul α × AddOfMul β)))

instance (priority := 100)
  [AddMonoidOps α] [AddMonoidOps β]
  [IsAddMonoid α] [IsAddMonoid β]
  [HasChar α n] [HasChar β m] : HasChar (α × β) (Nat.lcm n m) := by
  apply HasChar.of_spec
  · intro a
    ext <;> simp
    apply HasChar.nsmul_eq_zero_of_dvd
    exact Nat.dvd_lcm_left n m
    apply HasChar.nsmul_eq_zero_of_dvd
    exact Nat.dvd_lcm_right n m
  · intro k h
    refine Nat.lcm_dvd ?_ ?_
    apply HasChar.char_dvd (α := α)
    intro x
    show k • (x, (0: β)).fst = 0
    rw [←Prod.nsmul_fst, h]
    rfl
    apply HasChar.char_dvd (α := β)
    intro x
    show k • ((0: α), x).snd = 0
    rw [←Prod.nsmul_snd, h]
    rfl

instance
  [AddMonoidOps α] [AddMonoidOps β]
  [IsAddMonoid α] [IsAddMonoid β]
  [HasChar α n] [HasChar β n] : HasChar (α × β) n := by
  rw [←Nat.lcm_self n]
  infer_instance

variable [Add α] [Add β] [Add γ] [Add δ]
variable [Mul α] [Mul β] [Mul γ] [Mul δ]
variable [Zero α] [Zero β] [Zero γ] [Zero δ]
variable [One α] [One β] [One γ] [One δ]

def GroupEquiv.congrProd (h: α ≃* γ) (g: β ≃* δ) : α × β ≃* γ × δ := {
  Equiv.congrProd h.toEquiv g.toEquiv with
  map_one := by
    show (h 1, g 1) = _
    rw [map_one, map_one]; rfl
  map_mul {x y} := by
    show (h (x.fst * y.fst), g (x.snd * y.snd)) = _
    rw [map_mul, map_mul]; rfl
}

def AddGroupEquiv.congrProd (h: α ≃+ γ) (g: β ≃+ δ) : α × β ≃+ γ × δ := {
  Equiv.congrProd h.toEquiv g.toEquiv with
  map_zero := by
    show (h 0, g 0) = _
    rw [map_zero, map_zero]; rfl
  map_add {x y} := by
    show (h (x.fst + y.fst), g (x.snd + y.snd)) = _
    rw [map_add, map_add]; rfl
}

def ExpEquiv.congrProd (h: α ≃ₐ* γ) (g: β ≃ₐ* δ) : α × β ≃ₐ* γ × δ := {
  Equiv.congrProd h.toEquiv g.toEquiv with
  map_zero_to_one := by
    show (h 0, g 0) = _
    rw [map_zero_to_one, map_zero_to_one]; rfl
  map_add_to_mul {x y} := by
    show (h (x.fst + y.fst), g (x.snd + y.snd)) = _
    rw [map_add_to_mul, map_add_to_mul]; rfl
}

def LogEquiv.congrProd (h: α ≃ₘ+ γ) (g: β ≃ₘ+ δ) : α × β ≃ₘ+ γ × δ := {
  Equiv.congrProd h.toEquiv g.toEquiv with
  map_one_to_zero := by
    show (h 1, g 1) = _
    rw [map_one_to_zero, map_one_to_zero]; rfl
  map_mul_to_add {x y} := by
    show (h (x.fst * y.fst), g (x.snd * y.snd)) = _
    rw [map_mul_to_add, map_mul_to_add]; rfl
}
