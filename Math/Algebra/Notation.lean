import Math.Type.Notation

class One (α) where
  one: α

instance (priority := 100) [OfNat α 1] : One α where
  one := 1

instance One.ofNat [One α] : OfNat α 1 := ⟨One.one⟩

instance (priority := 100) [One α] : Nonempty α := ⟨One.one⟩

variable {a b c k: a₀}

class SMul (M α) where
  smul : M -> α -> α

infixr:73 " • " => SMul.smul

instance [Mul α] : SMul α α := ⟨(· * ·)⟩

class Inv (α) where
  inv: α -> α

postfix:max "⁻¹" => Inv.inv

class IsInvertible (x: α) [One α] [Mul α] where
  invOf: α
  mul_invOf: x * invOf = 1
  invOf_mul: invOf * x = 1

export IsInvertible (mul_invOf invOf_mul)

abbrev invOf [One α] [Mul α] (x: α) [h: IsInvertible x] := h.invOf

prefix:max "⅟" => invOf

instance (priority := 100) {x: α} [One α] [Mul α] [IsInvertible x] : IsInvertible (⅟ x) where
  invOf := x
  mul_invOf := invOf_mul
  invOf_mul := mul_invOf
