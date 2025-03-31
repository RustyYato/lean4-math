import Math.Algebra.Semigroup.Con
import Math.Algebra.Monoid.Defs
import Math.Algebra.Hom.Defs

variable {C α: Type*} [RelLike C α] (c: C)

def resp_nsmul [AddMonoidOps α] [IsAddMonoid α] [IsAddCon C] (c: C) (n: ℕ) {a b: α} (h: c a b) : c (n • a) (n • b) := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul]
  | succ n ih =>
    rw [succ_nsmul, succ_nsmul]
    apply resp_add
    assumption
    assumption

def resp_npow [MonoidOps α] [IsMonoid α] [IsMulCon C] (c: C) (n: ℕ) {a b: α} (h: c a b) : c (a ^ n) (b ^ n) :=
  resp_nsmul (C := AddOfMul C) c n h

instance [AddMonoidOps α] [IsAddMonoid α] [IsAddCon C] : SMul ℕ (IsCon.Quotient c) where
  smul n := by
    apply Quotient.lift (fun a => IsCon.mkQuot c (n • a))
    intro a b h
    apply Quotient.sound
    apply resp_nsmul
    assumption
instance [MonoidOps α] [IsMonoid α] [IsMulCon C] : Pow (IsCon.Quotient c) ℕ where
  pow := flip <| by
    intro n
    apply Quotient.lift (fun a => IsCon.mkQuot c (a ^ n))
    intro a b h
    apply Quotient.sound
    apply resp_npow
    assumption

instance [AddMonoidOps α] [IsAddMonoid α] [IsAddCon C] : IsAddMonoid (IsCon.Quotient c) where
  zero_nsmul a := by
    induction a with | mk a =>
    apply Quotient.sound
    rw [zero_nsmul]
  succ_nsmul n a := by
    induction a with | mk a =>
    apply Quotient.sound
    rw [succ_nsmul]
instance [MonoidOps α] [IsMonoid α] [IsMulCon C] : IsMonoid (IsCon.Quotient c) where
  npow_zero := zero_nsmul (α := (IsCon.Quotient (AddOfMul.mk c)))
  npow_succ := succ_nsmul (α := (IsCon.Quotient (AddOfMul.mk c)))

def IsAddCon.mkQuot [AddMonoidOps α] [IsAddMonoid α] [IsAddCon C] : α →+ IsCon.Quotient c where
  toFun a := IsCon.mkQuot c a
  map_zero := rfl
  map_add := rfl

def IsMulCon.mkQuot [MonoidOps α] [IsMonoid α] [IsMulCon C] : α →* IsCon.Quotient c where
  toFun a := IsCon.mkQuot c a
  map_one := rfl
  map_mul := rfl
