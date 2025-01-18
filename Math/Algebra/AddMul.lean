import Math.Algebra.Notation

def AddOfMul (α: Sort u) := α
def AddOfMul.get : AddOfMul α -> α := id
def AddOfMul.mk : α -> AddOfMul α := id

def MulOfAdd (α: Sort u) := α
def MulOfAdd.get : MulOfAdd α -> α := id
def MulOfAdd.mk : α -> MulOfAdd α := id

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
