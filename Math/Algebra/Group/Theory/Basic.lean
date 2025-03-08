import Math.Algebra.Group.Defs
import Math.Algebra.Group.Hom

structure Group (α: Type*) where
  [ops: GroupOps α]
  [spec: IsGroup α]

structure AbelianGroup (α: Type*) extends Group α where
  [comm: IsCommMagma α]

namespace Group

def ofAdd (α: Type*) [AddGroupOps α] [IsAddGroup α] :=
  Group.mk (α := MulOfAdd α)

@[coe]
def Elem (_: Group α) := α

attribute [coe] AbelianGroup.toGroup

instance : CoeSort (Group α) (Type _) := ⟨Elem⟩
instance : Coe (AbelianGroup α) (Group α) := ⟨AbelianGroup.toGroup⟩

def opp (g: Group α) : Group αᵐᵒᵖ :=
  let _ := g.ops
  have := g.spec
  Group.mk

set_option linter.unusedVariables false in
def ofAxiomsLeft
  (one: α) (mul: α -> α -> α) (inv: α -> α):
  let _ : One α := ⟨one⟩
  let _ : Mul α := ⟨mul⟩
  let _ : Inv α := ⟨inv⟩
  ∀(one_mul: ∀x: α, 1 * x = x)
   (inv_mul: ∀x: α, x⁻¹ * x = 1)
   (mul_assoc: ∀a b c: α, a * b * c = a * (b * c)),
   Group α :=
  fun one_mul inv_mul mul_assoc =>
  let _ : One α := ⟨one⟩
  let _ : Mul α := ⟨mul⟩
  let _ : Inv α := ⟨inv⟩
  let this: MonoidOps α := {
    npow := flip npowRec
  }
  let ops: GroupOps α := {
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
  Group.mk

set_option linter.unusedVariables false in
def ofAxiomsRight
  (one: α) (mul: α -> α -> α) (inv: α -> α):
  let _ : One α := ⟨one⟩
  let _ : Mul α := ⟨mul⟩
  let _ : Inv α := ⟨inv⟩
  ∀(one_mul: ∀x: α, x * 1 = x)
   (inv_mul: ∀x: α, x * x⁻¹ = 1)
   (mul_assoc: ∀a b c: α, a * b * c = a * (b * c)),
   Group α :=
   fun one_mul inv_mul mul_assoc =>
   Group.opp (α := αᵐᵒᵖ) (Group.ofAxiomsLeft (α := αᵐᵒᵖ) one (flip mul) inv one_mul inv_mul (fun _ _ _ => (mul_assoc _ _ _).symm))

section

variable (G: Group α)

instance : One G where
  one := G.ops.one

instance : Inv G where
  inv := G.ops.inv

instance : Mul G where
  mul := G.ops.mul

instance : Div G where
  div := G.ops.div

instance : Pow G ℕ where
  pow := G.ops.npow

instance : Pow G ℤ where
  pow := G.ops.zpow

instance : IsGroup G where
  mul_assoc := G.spec.mul_assoc
  one_mul := G.spec.one_mul
  mul_one := G.spec.mul_one
  div_eq_mul_inv := G.spec.div_eq_mul_inv
  zpow_ofNat := G.spec.zpow_ofNat
  zpow_negSucc := G.spec.zpow_negSucc
  inv_mul_cancel := G.spec.inv_mul_cancel
  npow_zero := G.spec.npow_zero
  npow_succ := G.spec.npow_succ

instance : IsDivInvMonoid G := inferInstance
instance : IsDivisionMonoid G := inferInstance

end

def conj [GroupOps α] [IsGroup α] (x: α) : α ≃* α where
  toFun a := x⁻¹ * a * x
  invFun a := x * a * x⁻¹
  leftInv := by
    intro a
    dsimp
    rw [←mul_assoc, mul_assoc, mul_inv_cancel, mul_one,
      ←mul_assoc, mul_inv_cancel, one_mul]
  rightInv := by
    intro a
    dsimp
    rw [←mul_assoc, mul_assoc, inv_mul_cancel, mul_one,
      ←mul_assoc, inv_mul_cancel, one_mul]
  resp_one := by
    dsimp
    rw [mul_one, inv_mul_cancel]
  resp_mul := by
    intro a b; dsimp
    rw [mul_assoc (_ * _), ←mul_assoc x (x⁻¹ * _), ←mul_assoc x x⁻¹,
      mul_inv_cancel, one_mul]
    ac_nf

def apply_conj [GroupOps α] [IsGroup α] (x: α) :
  ∀{a}, conj x a = x⁻¹ * a * x := rfl
def apply_conj_symm [GroupOps α] [IsGroup α] (x: α) :
  ∀{a}, (conj x).symm a = x * a * x⁻¹ := rfl

def Trivial : Group Unit := Group.ofAxiomsLeft () (fun _ _ => ()) (fun _ => ())
    (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl)

def toTrival (G: Type*) [GroupOps G] [IsGroup G] : G →* Trivial where
  toFun _ := 1
  resp_one := rfl
  resp_mul := rfl

def ofTrival (G: Type*) [GroupOps G] [IsGroup G] : Trivial ↪* G where
  toFun _ := 1
  inj' _ _ _ := rfl
  resp_one := rfl
  resp_mul { _ _ } := (mul_one 1).symm

def eqv_trivial (G: Type*) [GroupOps G] [IsGroup G] [Subsingleton G] : G ≃* Trivial where
  toFun _ := 1
  invFun _ := 1
  leftInv _ := Subsingleton.allEq _ _
  rightInv _ := rfl
  resp_one := rfl
  resp_mul := rfl

instance (G: Type*) [GroupOps G] [IsGroup G] : Subsingleton (G →* Trivial) where
  allEq a b := by
    ext x
    rfl

instance (G: Type*) [GroupOps G] [IsGroup G] : Subsingleton (Trivial →* G) where
  allEq a b := by
    ext x; show a 1 = b 1
    rw [resp_one, resp_one]

end Group

namespace AbelianGroup

def ofAdd (α: Type*) [AddGroupOps α] [IsAddGroup α] [IsAddCommMagma α] :=
  AbelianGroup.mk (Group.ofAdd α)

instance (G: AbelianGroup α) : IsCommMagma (G: Group α).Elem := G.comm

end AbelianGroup
