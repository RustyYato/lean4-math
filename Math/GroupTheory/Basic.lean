import Math.Algebra.Ring

private
def IsGroup.monoidOps
  [One α] [Mul α] [Inv α]
  : MonoidOps α where
    one := 1
    mul a b := a * b
    npow := flip npowRec

def IsGroup.ofAxiomsLeft
  [One α] [Mul α] [Inv α]
  (one_mul: ∀x: α, 1 * x = x)
  (inv_mul: ∀x: α, x⁻¹ * x = 1)
  (mul_assoc: ∀a b c: α, a * b * c = a * (b * c))
  : (_: GroupOps α) ×' IsGroup α :=
  let this := IsGroup.monoidOps
  let ops: GroupOps α := {
    toMonoidOps := this
    inv a := a⁻¹
    div a b := a * b⁻¹
    zpow := flip zpowRec
  }
  have mul_inv: ∀x: α, x * x⁻¹ = 1 := by
    intro x
    conv => { lhs; lhs; rw [←one_mul x, ←inv_mul x⁻¹] }
    rw [mul_assoc (x⁻¹⁻¹), inv_mul, mul_assoc, one_mul,
    inv_mul]
  let prf : IsGroup α := {
    mul_assoc := mul_assoc
    one_mul := one_mul
    div_eq_mul_inv _ _ := rfl
    zpow_ofNat _ _ := rfl
    zpow_negSucc _ _ := rfl
    inv_mul_cancel := inv_mul
    mul_one := by
      intro x
      erw [←inv_mul x, ←mul_assoc, mul_inv, one_mul]
  }
  ⟨ops, prf⟩

structure Group (α: Type*) extends GroupOps α, IsGroup α where

namespace Group

def Elem (_: Group α) := α

instance : CoeSort (Group α) (Type _) where
  coe := Elem

instance (g: Group α) : One g.Elem where
  one := g.one

instance (g: Group α) : Inv g.Elem where
  inv := g.inv

instance (g: Group α) : Mul g.Elem where
  mul := g.mul

instance (g: Group α) : Div g.Elem where
  div a b := a * b⁻¹

instance (g: Group α) : Pow g.Elem ℕ where
  pow := g.npow

instance (g: Group α) : Pow g.Elem ℤ where
  pow := g.zpow

instance (g: Group α) : IsGroup g.Elem where
  mul_assoc := g.mul_assoc
  one_mul := g.one_mul
  mul_one := g.mul_one
  inv_mul_cancel := g.inv_mul_cancel
  div_eq_mul_inv _ _ := rfl
  zpow_ofNat := g.zpow_ofNat
  zpow_negSucc := g.zpow_negSucc
  npow_zero := g.npow_zero
  npow_succ := g.npow_succ

def ofAxiomsLeft
  [One α] [Mul α] [Inv α]
  (one_mul: ∀x: α, 1 * x = x)
  (inv_mul: ∀x: α, x⁻¹ * x = 1)
  (mul_assoc: ∀a b c: α, a * b * c = a * (b * c)): Group α :=
  let this := IsGroup.monoidOps
  let ops: GroupOps α := {
    toMonoidOps := this
    inv a := a⁻¹
    div a b := a * b⁻¹
    zpow := flip zpowRec
  }
  have mul_inv: ∀x: α, x * x⁻¹ = 1 := by
    intro x
    conv => { lhs; lhs; rw [←one_mul x, ←inv_mul x⁻¹] }
    rw [mul_assoc (x⁻¹⁻¹), inv_mul, mul_assoc, one_mul,
    inv_mul]
  let prf : IsGroup α := {
    mul_assoc := mul_assoc
    one_mul := one_mul
    div_eq_mul_inv _ _ := rfl
    zpow_ofNat _ _ := rfl
    zpow_negSucc _ _ := rfl
    inv_mul_cancel := inv_mul
    mul_one := by
      intro x
      erw [←inv_mul x, ←mul_assoc, mul_inv, one_mul]
  }
  ⟨ops, prf⟩

def ofAxiomsRight
  [One α] [Mul α] [Inv α]
  (mul_one: ∀x: α, x * 1 = x)
  (mul_inv: ∀x: α, x * x⁻¹ = 1)
  (mul_assoc: ∀a b c: α, a * b * c = a * (b * c)): Group α :=
  Group.ofAxiomsLeft (α := αᵐᵒᵖ) mul_one mul_inv <| by
    intro a b c
    exact (mul_assoc _ _ _).symm

def opp (g: Group α) : Group αᵐᵒᵖ :=
  let _ := g.toGroupOps
  let _ := g.toIsGroup
  Group.mk inferInstance inferInstance

end Group
