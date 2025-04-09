import Math.Algebra.Semigroup.Impls.Pi
import Math.Algebra.Monoid.Defs
import Math.Algebra.Monoid.Char

section Pi

variable {ι: Type*} {α: ι -> Type*}

instance [∀i, AddMonoidOps (α i)] [∀i, IsAddMonoid (α i)] : IsAddMonoid (∀i, α i) where
  zero_nsmul := by
    intro f; ext i
    apply zero_nsmul
  succ_nsmul := by
    intro n f; ext i
    apply succ_nsmul

instance [∀i, MonoidOps (α i)] [∀i, IsMonoid (α i)] : IsMonoid (∀i, α i)  :=
  inferInstanceAs (IsMonoid (MulOfAdd (∀i, AddOfMul (α i))))

instance [Nonempty ι] [Nonempty (∀i, α i)] [∀i, AddMonoidOps (α i)] [∀i, IsAddMonoid (α i)] [∀i, HasChar (α i) n] : HasChar (∀i, α i) n := by
  apply HasChar.of_spec
  . intro f
    ext; apply HasChar.char_spec
  . intro m h
    rename_i ne₀ ne₁ _ _ _
    obtain ⟨i⟩ := ne₀
    obtain ⟨f⟩ := ne₁
    apply HasChar.char_dvd (α := α i)
    intro x
    classical
    have := congrFun (h (fun j => if h:i = j then h ▸ x else f j)) i
    simpa using this

end Pi

section Function

variable {ι: Type*} {α: Type*}

instance [AddMonoidOps α] [IsAddMonoid α] : IsAddMonoid (ι -> α) :=
  inferInstance
instance [MonoidOps α] [IsMonoid α] : IsMonoid (ι -> α) :=
  inferInstance

instance [Nonempty ι] [Nonempty α] [AddMonoidOps α] [IsAddMonoid α] [HasChar α n] : HasChar (ι -> α) n :=
  inferInstance

end Function
