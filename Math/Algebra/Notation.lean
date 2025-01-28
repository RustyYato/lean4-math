notation "ℕ" => Nat
notation "ℤ" => Int

class One (α) where
  one: α

instance (priority := 100) [OfNat α 1] : One α where
  one := 1

instance One.ofNat [One α] : OfNat α 1 := ⟨ One.one ⟩

variable {a b c k: a₀}

class SMul (M α) where
  smul : M -> α -> α

infixr:73 " • " => SMul.smul

instance [Mul α] : SMul α α := ⟨(· * ·)⟩

class Inv (α) where
  inv: α -> α

postfix:max "⁻¹" => Inv.inv
