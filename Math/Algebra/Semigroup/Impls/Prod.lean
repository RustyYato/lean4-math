import Math.Algebra.Semigroup.Defs

section Prod.Operators

variable {α β: Type*}

instance [Zero α] [Zero β] : Zero (α × β) where
  zero := (0, 0)
instance [One α] [One β] : One (α × β) where
  one := (1, 1)
instance [NatCast α] [NatCast β] : NatCast (α × β) where
  natCast n := (n, n)
instance [IntCast α] [IntCast β] : IntCast (α × β) where
  intCast n := (n, n)

instance [Add α] [Add β] : Add (α × β) where
  add f g := (f.1 + g.1, f.2 + g.2)

instance [Sub α] [Sub β] : Sub (α × β) where
  sub f g := (f.1 - g.1, f.2 - g.2)

instance [Mul α] [Mul β] : Mul (α × β) where
  mul f g := (f.1 * g.1, f.2 * g.2)

instance [Div α] [Div β] : Div (α × β) where
  div f g := (f.1 / g.1, f.2 / g.2)

instance [SMul R α] [SMul R β] : SMul R (α × β) where
  smul n f := (n • f.1, n • f.2)

instance [Pow α ℕ] [Pow β ℕ] : Pow (α × β) ℕ where
  pow f n := (f.1 ^ n, f.2 ^ n)

instance [Pow α ℤ] [Pow β ℤ] : Pow (α × β) ℤ where
  pow f n := (f.1 ^ n, f.2 ^ n)

instance [Neg α] [Neg β] : Neg (α × β) where
  neg f := (-f.1, -f.2)

instance [Inv α] [Inv β] : Inv (α × β) where
  inv f := (f.1⁻¹, f.2⁻¹)

namespace Prod

@[simp] def zero_fst [Zero α] [Zero β] : (0: α × β).1 = 0 := rfl
@[simp] def zero_snd [Zero α] [Zero β] : (0: α × β).2 = 0 := rfl
@[simp] def one_fst [One α] [One β] : (1: α × β).1 = 1 := rfl
@[simp] def one_snd [One α] [One β] : (1: α × β).2 = 1 := rfl
@[simp] def natCast_fst [NatCast α] [NatCast β] (n: ℕ) : (n: α × β).1 = n := rfl
@[simp] def natCast_snd [NatCast α] [NatCast β] (n: ℕ) : (n: α × β).2 = n := rfl
@[simp] def intCast_fst [IntCast α] [IntCast β] (n: ℤ) : (n: α × β).1 = n := rfl
@[simp] def intCast_snd [IntCast α] [IntCast β] (n: ℤ) : (n: α × β).2 = n := rfl
@[simp] def add_fst [Add α] [Add β] (a b: α × β) : (a + b).1 = a.1 + b.1 := rfl
@[simp] def add_snd [Add α] [Add β] (a b: α × β) : (a + b).2 = a.2 + b.2 := rfl
@[simp] def mul_fst [Mul α] [Mul β] (a b: α × β) : (a * b).1 = a.1 * b.1 := rfl
@[simp] def mul_snd [Mul α] [Mul β] (a b: α × β) : (a * b).2 = a.2 * b.2 := rfl
@[simp] def sub_fst [Sub α] [Sub β] (a b: α × β) : (a - b).1 = a.1 - b.1 := rfl
@[simp] def sub_snd [Sub α] [Sub β] (a b: α × β) : (a - b).2 = a.2 - b.2 := rfl
@[simp] def div_fst [Div α] [Div β] (a b: α × β) : (a / b).1 = a.1 / b.1 := rfl
@[simp] def div_snd [Div α] [Div β] (a b: α × β) : (a / b).2 = a.2 / b.2 := rfl
@[simp] def neg_fst [Neg α] [Neg β] (a: α × β) : (-a).1 = -a.1 := rfl
@[simp] def neg_snd [Neg α] [Neg β] (a: α × β) : (-a).2 = -a.2 := rfl
@[simp] def inv_fst [Inv α] [Inv β] (a: α × β) : (a⁻¹).1 = a.1⁻¹ := rfl
@[simp] def inv_snd [Inv α] [Inv β] (a: α × β) : (a⁻¹).2 = a.2⁻¹ := rfl
@[simp] def nsmul_fst [SMul ℕ α] [SMul ℕ β] (n: ℕ) (a: α × β) : (n • a).1 = n • a.1 := rfl
@[simp] def nsmul_snd [SMul ℕ α] [SMul ℕ β] (n: ℕ) (a: α × β) : (n • a).2 = n • a.2 := rfl
@[simp] def zsmul_fst [SMul ℤ α] [SMul ℤ β] (n: ℤ) (a: α × β) : (n • a).1 = n • a.1 := rfl
@[simp] def zsmul_snd [SMul ℤ α] [SMul ℤ β] (n: ℤ) (a: α × β) : (n • a).2 = n • a.2 := rfl
@[simp] def npow_fst [Pow α ℕ] [Pow β ℕ] (n: ℕ) (a: α × β) : (a ^ n).1 = a.1 ^ n := rfl
@[simp] def npow_snd [Pow α ℕ] [Pow β ℕ] (n: ℕ) (a: α × β) : (a ^ n).2 = a.2 ^ n := rfl
@[simp] def zpow_fst [Pow α ℤ] [Pow β ℤ] (n: ℤ) (a: α × β) : (a ^ n).1 = a.1 ^ n := rfl
@[simp] def zpow_snd [Pow α ℤ] [Pow β ℤ] (n: ℤ) (a: α × β) : (a ^ n).2 = a.2 ^ n := rfl

end Prod

end Prod.Operators

instance [Zero α] [Zero β] [Add α] [Add β] [IsAddZeroClass α] [IsAddZeroClass β] : IsAddZeroClass (α × β) where
  zero_add := by
    intro f; ext <;> apply zero_add
  add_zero := by
    intro f; ext <;> apply add_zero

instance [One α] [One β] [Mul α] [Mul β] [IsMulOneClass α] [IsMulOneClass β] : IsMulOneClass (α × β)
  := inferInstanceAs (IsMulOneClass (MulOfAdd (AddOfMul α × AddOfMul β)))

instance [Zero α] [Zero β] [Mul α] [Mul β] [IsMulZeroClass α] [IsMulZeroClass β] : IsMulZeroClass (α × β) where
  zero_mul := by
    intro f; ext <;> apply zero_mul
  mul_zero := by
    intro f; ext <;> apply mul_zero

instance [Add α] [Add β] [IsAddSemigroup α] [IsAddSemigroup β] : IsAddSemigroup (α × β) where
  add_assoc := by
    intro a b c; ext <;> apply add_assoc

instance [Mul α] [Mul β] [IsSemigroup α] [IsSemigroup β] : IsSemigroup (α × β) :=
  inferInstanceAs (IsSemigroup (MulOfAdd (AddOfMul α × AddOfMul β)))

instance [Add α] [Add β] [IsAddCommMagma α] [IsAddCommMagma β] : IsAddCommMagma (α × β) where
  add_comm := by
    intro a b; ext <;> apply add_comm

instance [Mul α] [Mul β] [IsCommMagma α] [IsCommMagma β] : IsCommMagma (α × β) :=
  inferInstanceAs (IsCommMagma (MulOfAdd (AddOfMul α × AddOfMul β)))
