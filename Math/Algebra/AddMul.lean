import Math.Algebra.Notation
import Math.Data.Nat.Cast

def AddOfMul (α: Sort u) := α
def AddOfMul.get : AddOfMul α -> α := id
def AddOfMul.mk : α -> AddOfMul α := id

def MulOfAdd (α: Sort u) := α
def MulOfAdd.get : MulOfAdd α -> α := id
def MulOfAdd.mk : α -> MulOfAdd α := id

def AddOpp (α: Sort u) := α
def AddOpp.get : AddOpp α -> α := id
def AddOpp.mk : α -> AddOpp α := id

def MulOpp (α: Sort u) := α
def MulOpp.get : MulOpp α -> α := id
def MulOpp.mk : α -> MulOpp α := id

postfix:max "ᵃᵒᵖ" => AddOpp
postfix:max "ᵐᵒᵖ" => MulOpp

instance [One α] : Zero (AddOfMul α) where
  zero := (1: α)

instance [Mul α] : Add (AddOfMul α) where
  add a b := a.get * b.get

instance [Div α] : Sub (AddOfMul α) where
  sub a b := a.get / b.get

instance [Inv α] : Neg (AddOfMul α) where
  neg a := .mk a.get⁻¹

instance [Pow α ℕ] : SMul ℕ (AddOfMul α) where
  smul n a := .mk (a.get ^ n)

instance [Pow α ℤ] : SMul ℤ (AddOfMul α) where
  smul n a := .mk (a.get ^ n)

instance [Zero α] : One (MulOfAdd α) where
  one := (0: α)

instance [Add α] : Mul (MulOfAdd α) where
  mul a b := a.get + b.get

instance [Sub α] : Div (MulOfAdd α) where
  div a b := a.get - b.get

instance [Neg α] : Inv (MulOfAdd α) where
  inv a := .mk (-a.get)

instance [SMul ℕ α] : Pow (MulOfAdd α) ℕ where
  pow a n := .mk (n • a.get)

instance [SMul ℤ α] : Pow (MulOfAdd α) ℤ where
  pow a n := .mk (n • a.get)

instance [Zero α] : Zero αᵃᵒᵖ where
  zero := (0: α)

instance [One α] : One αᵃᵒᵖ where
  one := (1: α)

instance [Add α] : Add αᵃᵒᵖ where
  add a b := b.get + a.get

instance [Neg α] : Neg αᵃᵒᵖ := ⟨(.mk <| -·.get)⟩
instance [Add α] [Neg α] : Sub αᵃᵒᵖ where
  sub a b := a + -b

instance [Pow α ℕ] : Pow αᵃᵒᵖ ℕ where
  pow a n := .mk (a.get ^ n)

instance [Pow α ℤ] : Pow αᵃᵒᵖ ℤ where
  pow a n := .mk (a.get ^ n)

instance [Mul α] : Mul αᵃᵒᵖ := ⟨(.mk <| ·.get * ·.get)⟩
instance [Inv α] : Inv αᵃᵒᵖ := ⟨(.mk <| ·.get⁻¹)⟩
instance [Div α] : Div αᵃᵒᵖ := ⟨(.mk <| ·.get / ·.get)⟩
instance [SMul Nat α] : SMul Nat αᵃᵒᵖ := ⟨(.mk <| · • ·.get)⟩
instance [SMul Int α] : SMul Int αᵃᵒᵖ := ⟨(.mk <| · • ·.get)⟩

instance [NatCast α] : NatCast αᵃᵒᵖ := ⟨(.mk ·)⟩
instance [IntCast α] : IntCast αᵃᵒᵖ := ⟨(.mk ·)⟩

instance [Zero α] : Zero αᵐᵒᵖ where
  zero := (0: α)

instance [One α] : One αᵐᵒᵖ where
  one := (1: α)

instance [Mul α] : Mul αᵐᵒᵖ where
  mul a b := b.get * a.get

instance [Inv α] : Inv αᵐᵒᵖ where
  inv a := .mk (a.get⁻¹)

instance [Mul α] [Inv α] : Div αᵐᵒᵖ where
  div a b := a * b⁻¹

instance [Pow α ℕ] : Pow αᵐᵒᵖ ℕ where
  pow a n := .mk (a.get ^ n)

instance [Pow α ℤ] : Pow αᵐᵒᵖ ℤ where
  pow a n := .mk (a.get ^ n)

instance [Mul α] : SMul αᵐᵒᵖ α where
  smul c x := x * c.get

instance [Mul α] : SMul α αᵐᵒᵖ where
  smul c x := .mk c * x

instance [Add α] : Add αᵐᵒᵖ := ⟨(.mk <| ·.get + ·.get)⟩
instance [Sub α] : Sub αᵐᵒᵖ := ⟨(.mk <| ·.get - ·.get)⟩
instance [Neg α] : Neg αᵐᵒᵖ := ⟨(.mk <| -·.get)⟩
instance [SMul Nat α] : SMul Nat αᵐᵒᵖ := ⟨(.mk <| · • ·.get)⟩
instance [SMul Int α] : SMul Int αᵐᵒᵖ := ⟨(.mk <| · • ·.get)⟩

instance [NatCast α] : NatCast αᵐᵒᵖ := ⟨(.mk ·)⟩
instance [IntCast α] : IntCast αᵐᵒᵖ := ⟨(.mk ·)⟩

-- instance [Nat.AtLeastTwoOfNat α n] : Nat.AtLeastTwoOfNat αᵃᵒᵖ n := ⟨(.mk (OfNat.ofNat n))⟩
-- instance [Nat.AtLeastTwoOfNat α n] : Nat.AtLeastTwoOfNat αᵐᵒᵖ n := ⟨(.mk (OfNat.ofNat n))⟩

namespace AddOpp

@[cases_eliminator]
def cases {motive: αᵃᵒᵖ -> Sort _} (mk: ∀x: α, motive (mk x)) : ∀x, motive x := mk

@[simp] def mk_zero [Zero α] : mk (0: α) = 0 := rfl
@[simp] def mk_one [One α] : mk (1: α) = 1 := rfl
@[simp] def mk_add [Add α] (a b: α) : mk (a + b) = mk b + mk a := rfl
@[simp] def mk_neg [Neg α] (a: α) : mk (-a) = -mk a := rfl
@[simp] def mk_mul [Mul α] (a b: α) : mk (a * b) = mk a * mk b := rfl

@[simp] def get_zero [Zero α] : get (0: αᵃᵒᵖ) = 0 := rfl
@[simp] def get_one [One α] : get (1: αᵃᵒᵖ) = 1 := rfl
@[simp] def get_add [Add α] (a b: αᵃᵒᵖ) : get (a + b) = get b + get a := rfl
@[simp] def get_neg [Neg α] (a: αᵃᵒᵖ) : get (-a) = -get a := rfl
@[simp] def get_mul [Mul α] (a b: αᵃᵒᵖ) : get (a * b) = get a * get b := rfl

end AddOpp

namespace MulOpp

@[cases_eliminator]
def cases {motive: αᵐᵒᵖ -> Sort _} (mk: ∀x: α, motive (mk x)) : ∀x, motive x := mk

@[simp] def mk_zero [Zero α] : mk (0: α) = 0 := rfl
@[simp] def mk_one [One α] : mk (1: α) = 1 := rfl
@[simp] def mk_add [Add α] (a b: α) : mk (a + b) = mk a + mk b := rfl
@[simp] def mk_neg [Neg α] (a: α) : mk (-a) = -mk a := rfl
@[simp] def mk_mul [Mul α] (a b: α) : mk (a * b) = mk b * mk a := rfl

@[simp] def get_zero [Zero α] : get (0: αᵐᵒᵖ) = 0 := rfl
@[simp] def get_one [One α] : get (1: αᵐᵒᵖ) = 1 := rfl
@[simp] def get_add [Add α] (a b: αᵐᵒᵖ) : get (a + b) = get a + get b := rfl
@[simp] def get_neg [Neg α] (a: αᵐᵒᵖ) : get (-a) = -get a := rfl
@[simp] def get_mul [Mul α] (a b: αᵐᵒᵖ) : get (a * b) = get b * get a := rfl

@[simp] def mk_get (a: α) : (mk a).get = a := rfl

end MulOpp
