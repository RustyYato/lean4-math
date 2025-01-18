import Math.Type.Basic
import Math.Algebra.Ring
import Math.Data.QuotLike.Basic
import Math.Type.Finite
import Math.Data.Set.Finite
import Math.Data.Fin.Basic
import Math.Data.Set.Basic
import Math.Data.StdNat.Prime
import Math.Data.StdNat.Find

attribute [local simp] IsEquivLike.coe
attribute [local simp] DFunLike.coe

structure Group where
  ty: Type*
  mul': ty -> ty -> ty
  one': ty
  inv': ty -> ty
  mul_assoc': ∀a b c: ty, mul' (mul' a b) c = mul' a (mul' b c)
  one_mul': ∀a: ty, mul' one' a = a
  inv_mul': ∀a: ty, mul' (inv' a) a = one'

section

variable {g: Group}

instance : Mul g.ty where
  mul := g.mul'

instance : One g.ty where
  one := g.one'

instance : Inv g.ty where
  inv := g.inv'

instance : Div g.ty where
  div a b := a * b⁻¹

instance : Pow g.ty ℕ := ⟨flip npowRec⟩
instance : Pow g.ty ℤ := ⟨flip zpowRec⟩

local notation "𝟙" => One.one

def Group.mul_inv' {g: Group} (a: g.ty) : g.mul' a (g.inv' a) = 𝟙 := by
  rw [←g.one_mul' (g.mul' a (g.inv' a))]
  conv => { lhs; rw [←g.inv_mul' (a⁻¹)] }
  erw [←g.mul_assoc', g.mul_assoc' (g.inv' a⁻¹), g.inv_mul', g.mul_assoc', g.one_mul', g.inv_mul']
  rfl
def Group.mul_one' {g: Group} (a: g.ty) : a * 𝟙 = a := by
  show g.mul' a g.one' = a
  erw [←g.inv_mul' a, ←g.mul_assoc', g.mul_inv', g.one_mul']

instance : IsGroup g.ty where
  mul_assoc := g.mul_assoc'
  one_mul := g.one_mul'
  div_eq_mul_inv _ _ := rfl
  zpow_ofNat _ _ := rfl
  zpow_negSucc _ _:= rfl
  inv_mul_cancel := g.inv_mul'
  mul_one := g.mul_one'

end
