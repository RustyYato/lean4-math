import Math.Algebra.Notation
import Math.Logic.Equiv.Defs
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
instance [SMul R α] : SMul R αᵃᵒᵖ := ⟨(.mk <| · • ·.get)⟩

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
instance [SMul R α] : SMul R αᵐᵒᵖ := ⟨(.mk <| · • ·.get)⟩

instance [NatCast α] : NatCast αᵐᵒᵖ := ⟨(.mk ·)⟩
instance [IntCast α] : IntCast αᵐᵒᵖ := ⟨(.mk ·)⟩

-- instance [Nat.AtLeastTwoOfNat α n] : Nat.AtLeastTwoOfNat αᵃᵒᵖ n := ⟨(.mk (OfNat.ofNat n))⟩
-- instance [Nat.AtLeastTwoOfNat α n] : Nat.AtLeastTwoOfNat αᵐᵒᵖ n := ⟨(.mk (OfNat.ofNat n))⟩

namespace MulOfAdd

@[cases_eliminator]
def cases {motive: MulOfAdd α -> Sort _} (mk: ∀x: α, motive (mk x)) : ∀x, motive x := mk

@[simp] def mk_zero [Zero α] : mk (0: α) = 1 := rfl
@[simp] def mk_add [Add α] (a b: α) : mk (a + b) = mk a * mk b := rfl
@[simp] def mk_neg [Neg α] (a: α) : mk (-a) = (mk a)⁻¹ := rfl
@[simp] def mk_nsmul [SMul ℕ α] (n: ℕ) (a: α) : mk (n • a) = (mk a) ^ n := rfl
@[simp] def mk_zsmul [SMul ℤ α] (n: ℤ) (a: α) : mk (n • a) = (mk a) ^ n := rfl
@[simp] def get_one [Zero α] : (get 1: α) = 0 := rfl
@[simp] def get_mul [Add α] (a b: MulOfAdd α) : (a * b).get = a.get + b.get := rfl
@[simp] def get_inv [Neg α] (a: MulOfAdd α) : (a⁻¹).get = -a.get := rfl
@[simp] def get_npow [SMul ℕ α] (n: ℕ) (a: MulOfAdd α) : (a ^ n).get = n • a.get := rfl
@[simp] def get_zpow [SMul ℤ α] (n: ℤ) (a: MulOfAdd α) : (a ^ n).get = n • a.get := rfl

@[simp] def mk_get (a: MulOfAdd α) : mk a.get = a := rfl
@[simp] def get_mk (a: α) : (mk a).get = a := rfl

end MulOfAdd

namespace AddOfMul

@[cases_eliminator]
def cases {motive: MulOfAdd α -> Sort _} (mk: ∀x: α, motive (mk x)) : ∀x, motive x := mk

@[simp] def get_zero [One α] : get (0: AddOfMul α) = 1 := rfl
@[simp] def get_add [Mul α] (a b: AddOfMul α) : get (a + b) = get a * get b := rfl
@[simp] def get_neg [Inv α] (a: AddOfMul α) : get (-a) = (get a)⁻¹ := rfl
@[simp] def get_nsmul [Pow α ℕ] (n: ℕ) (a: AddOfMul α) : get (n • a) = (get a) ^ n := rfl
@[simp] def get_zsmul [Pow α ℤ] (n: ℤ) (a: AddOfMul α) : get (n • a) = (get a) ^ n := rfl

@[simp] def mk_one [One α] : (mk 1: AddOfMul α) = 0 := rfl
@[simp] def mk_mul [Mul α] (a b: α) : mk (a * b) = mk a + mk b := rfl
@[simp] def mk_inv [Inv α] (a: α) : mk a⁻¹ = -mk a := rfl
@[simp] def mk_npow [Pow α ℕ] (n: ℕ) (a: α) : mk (a ^ n) = n • mk a := rfl
@[simp] def mk_zpow [Pow α ℤ] (n: ℤ) (a: α) : mk (a ^ n) = n • mk a := rfl

@[simp] def mk_get (a: AddOfMul α) : mk a.get = a := rfl
@[simp] def get_mk (a: α) : (mk a).get = a := rfl

end AddOfMul

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

def lsmul [SMul R A] (r: R) (a: A) := r • a
def rsmul [SMul (MulOpp R) A] (a: A) (r: R) := MulOpp.mk r • a

infixr:73 " •> " => lsmul
infixl:73 " <• " => rsmul

def lsmul_eq_smul [SMul R A] (r: R) (a: A) : r •> a = r • a := rfl
def rsmul_eq_smul [SMul (MulOpp R) A] (r: R) (a: A) : a <• r = MulOpp.mk r • a := rfl

namespace Equiv

attribute [local irreducible] MulOpp AddOpp AddOfMul MulOfAdd

protected def MulOfAdd : α ≃ MulOfAdd α where
  toFun := MulOfAdd.mk
  invFun := MulOfAdd.get
  leftInv _ := rfl
  rightInv _ := rfl
protected def AddOfMul : α ≃ AddOfMul α where
  toFun := AddOfMul.mk
  invFun := AddOfMul.get
  leftInv _ := rfl
  rightInv _ := rfl
protected def MulOpp : α ≃ αᵐᵒᵖ where
  toFun := MulOpp.mk
  invFun := MulOpp.get
  leftInv _ := rfl
  rightInv _ := rfl
protected def AddOpp : α ≃ αᵃᵒᵖ where
  toFun := AddOpp.mk
  invFun := AddOpp.get
  leftInv _ := rfl
  rightInv _ := rfl

@[simp] def apply_mul_of_add : Equiv.MulOfAdd (α := α) = MulOfAdd.mk (α := α) := rfl
@[simp] def symm_apply_mul_of_add : Equiv.MulOfAdd.symm (α := α) = MulOfAdd.get (α := α) := rfl
@[simp] def apply_add_of_mul : Equiv.AddOfMul (α := α) = AddOfMul.mk (α := α) := rfl
@[simp] def symm_apply_add_of_mul : Equiv.AddOfMul.symm (α := α) = AddOfMul.get (α := α) := rfl
@[simp] def apply_add_opp : Equiv.AddOpp (α := α) = AddOpp.mk (α := α) := rfl
@[simp] def symm_apply_add_opp : Equiv.AddOpp.symm (α := α) = AddOpp.get (α := α) := rfl
@[simp] def apply_mul_opp : Equiv.MulOpp (α := α) = MulOpp.mk (α := α) := rfl
@[simp] def symm_apply_mul_opp : Equiv.MulOpp.symm (α := α) = MulOpp.get (α := α) := rfl

end Equiv
