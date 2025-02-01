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
