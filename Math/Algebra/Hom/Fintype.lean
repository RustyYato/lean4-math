import Math.Data.Fintype.Basic
import Math.Data.Fintype.Impls.Subtype
import Math.Data.Fintype.Impls.Finset
import Math.Algebra.Hom.Defs

variable (R α β: Type*)
variable [Zero α] [One α] [Add α] [Mul α] [SMul R α]
variable [Zero β] [One β] [Add β] [Mul β] [SMul R β]
variable [Zero R] [One R] [Add R] [Mul R]
variable [Fintype α] [Fintype β] [Fintype R]
  [DecidableEq α] [DecidableEq β] [DecidableEq R]

namespace Equiv

abbrev is_add_hom (f: α -> β) : Prop := ∀{x y}, f (x + y) = f x + f y
abbrev is_mul_hom (f: α -> β) : Prop := ∀{x y}, f (x * y) = f x * f y

protected def ZeroHom : ZeroHom α β ≃ { f: α -> β // f 0 = 0 } where
  toFun f := ⟨f.1, f.2⟩
  invFun f := ⟨f.1, f.2⟩
  leftInv _ := rfl
  rightInv _ := rfl

protected def OneHom : OneHom α β ≃ { f: α -> β // f 1 = 1 } where
  toFun f := ⟨f.1, f.2⟩
  invFun f := ⟨f.1, f.2⟩
  leftInv _ := rfl
  rightInv _ := rfl

protected def AddHom : AddHom α β ≃ { f: α -> β // is_add_hom _ _ f } where
  toFun f := ⟨f.1, f.2⟩
  invFun f := ⟨f.1, f.2⟩
  leftInv _ := rfl
  rightInv _ := rfl

protected def MulHom : MulHom α β ≃ { f: α -> β // is_mul_hom _ _ f } where
  toFun f := ⟨f.1, f.2⟩
  invFun f := ⟨f.1, f.2⟩
  leftInv _ := rfl
  rightInv _ := rfl

protected def SMulHom : SMulHom R α β ≃ { f: α -> β // ∀{r: R} {x}, f (r • x) = r • f x } where
  toFun f := ⟨f.1, f.2⟩
  invFun f := ⟨f.1, f.2⟩
  leftInv _ := rfl
  rightInv _ := rfl

protected def AddGroupHom : (α →+ β) ≃ { f: α -> β // f 0 = 0 ∧ is_add_hom _ _ f } where
  toFun f := ⟨f.1, f.map_zero, f.map_add⟩
  invFun f := {
    toFun := f.val
    map_zero := f.property.1
    map_add := f.property.2
  }
  leftInv _ := rfl
  rightInv _ := rfl

protected def GroupHom : (α →* β) ≃ { f: α -> β // f 1 = 1 ∧ is_mul_hom _ _ f } where
  toFun f := ⟨f.1, f.map_one, f.map_mul⟩
  invFun f := {
    toFun := f.val
    map_one := f.property.1
    map_mul := f.property.2
  }
  leftInv _ := rfl
  rightInv _ := rfl

protected def AddGroupWithOneHom : (α →+₁ β) ≃ { f: α -> β // f 0 = 0 ∧ f 1 = 1 ∧ is_add_hom _ _ f } where
  toFun f := ⟨f.1, f.map_zero, f.map_one, f.map_add⟩
  invFun f := {
    toFun := f.val
    map_zero := f.property.1
    map_one := f.property.2.1
    map_add := f.property.2.2
  }
  leftInv _ := rfl
  rightInv _ := rfl

protected def GroupWithZeroHom : (α →*₀ β) ≃ { f: α -> β // f 0 = 0 ∧ f 1 = 1 ∧ is_mul_hom _ _ f } where
  toFun f := ⟨f.1, f.map_zero, f.map_one, f.map_mul⟩
  invFun f := {
    toFun := f.val
    map_zero := f.property.1
    map_one := f.property.2.1
    map_mul := f.property.2.2
  }
  leftInv _ := rfl
  rightInv _ := rfl

protected def RingHom : (α →+* β) ≃ { f: α -> β // f 0 = 0 ∧ f 1 = 1 ∧ is_add_hom _ _ f ∧ is_mul_hom _ _ f } where
  toFun f := ⟨f.1, f.map_zero, f.map_one, f.map_add, f.map_mul⟩
  invFun f := {
    toFun := f.val
    map_zero := f.property.1
    map_one := f.property.2.1
    map_add := f.property.2.2.1
    map_mul := f.property.2.2.2
  }
  leftInv _ := rfl
  rightInv _ := rfl

protected def RngHom : (α →+*₀ β) ≃ { f: α -> β // f 0 = 0 ∧ is_add_hom _ _ f  ∧ is_mul_hom _ _ f } where
  toFun f := ⟨f.1, f.map_zero, f.map_add, f.map_mul⟩
  invFun f := {
    toFun := f.val
    map_zero := f.property.1
    map_add := f.property.2.1
    map_mul := f.property.2.2
  }
  leftInv _ := rfl
  rightInv _ := rfl

end Equiv

instance : Fintype (ZeroHom α β) := Fintype.ofEquiv (Equiv.ZeroHom α β)
instance : Fintype (OneHom α β) := Fintype.ofEquiv (Equiv.OneHom α β)
instance : Fintype (AddHom α β) := Fintype.ofEquiv (Equiv.AddHom α β)
instance : Fintype (MulHom α β) := Fintype.ofEquiv (Equiv.MulHom α β)
instance : Fintype (SMulHom R α β) := Fintype.ofEquiv (Equiv.SMulHom R α β)
instance : Fintype (α →+ β) := Fintype.ofEquiv (Equiv.AddGroupHom α β)
instance : Fintype (α →* β) := Fintype.ofEquiv (Equiv.GroupHom α β)
instance : Fintype (α →+₁ β) := Fintype.ofEquiv (Equiv.AddGroupWithOneHom α β)
instance : Fintype (α →*₀ β) := Fintype.ofEquiv (Equiv.GroupWithZeroHom α β)
instance : Fintype (α →+* β) := Fintype.ofEquiv (Equiv.RingHom α β)
instance : Fintype (α →+*₀ β) := Fintype.ofEquiv (Equiv.RngHom α β)
