import Math.Algebra.Notation

def AddOfMul (α: Sort u) := α
def AddOfMul.get : AddOfMul α -> α := id
def AddOfMul.mk : α -> AddOfMul α := id

def MulOfAdd (α: Sort u) := α
def MulOfAdd.get : MulOfAdd α -> α := id
def MulOfAdd.mk : α -> MulOfAdd α := id

def MulOpp (α: Sort u) := α
def MulOpp.get : MulOpp α -> α := id
def MulOpp.mk : α -> MulOpp α := id

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
