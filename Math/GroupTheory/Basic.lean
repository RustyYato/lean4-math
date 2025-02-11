import Math.Algebra.Hom

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
structure AbelianGroup (α: Type*) extends Group α, IsCommMagma α where

namespace Group

def ofAdd (α: Type*) [AddGroupOps α] [IsAddGroup α] :=
  Group.mk (α := MulOfAdd α) inferInstance inferInstance

def Elem (_: Group α) := α

attribute [coe] Elem

instance : CoeSort (Group α) (Type _) where
  coe := Elem
instance : Coe (AbelianGroup α) (Group α) := ⟨AbelianGroup.toGroup⟩
instance : CoeSort (AbelianGroup α) (Type _) where
  coe x := (x: Group α)

instance (g: Group α) : One g where
  one := g.one

instance (g: Group α) : Inv g where
  inv := g.inv

instance (g: Group α) : Mul g where
  mul := g.mul

instance (g: Group α) : Div g where
  div a b := a * b⁻¹

instance (g: Group α) : Pow g ℕ where
  pow := g.npow

instance (g: Group α) : Pow g ℤ where
  pow := g.zpow

instance (g: Group α) : IsGroup g where
  mul_assoc := g.mul_assoc
  one_mul := g.one_mul
  mul_one := g.mul_one
  inv_mul_cancel := g.inv_mul_cancel
  div_eq_mul_inv _ _ := rfl
  zpow_ofNat := g.zpow_ofNat
  zpow_negSucc := g.zpow_negSucc
  npow_zero := g.npow_zero
  npow_succ := g.npow_succ

instance (g: Group α) : IsDivInvMonoid g := inferInstance
instance (g: Group α) : IsDivisionMonoid g := inferInstance

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

protected abbrev Hom (a: Group α) (b: Group β) := a →* b
protected abbrev Embedding (a: Group α) (b: Group β) := a ↪* b
protected abbrev Equiv (a: Group α) (b: Group β) := a ≃* b

variable {a: Group α} {b: Group β} {c: Group γ}

-- conjugate each the elements of `A` by `x` as an group equivalence relation
def conj (A: Group α) (x: A) : A ≃* A where
  toFun a := x⁻¹ * a * x
  invFun a := x * a * x⁻¹
  leftInv := by
    intro a
    dsimp
    rw [←mul_assoc, ←mul_assoc, mul_inv_cancel, one_mul,
      mul_assoc, mul_inv_cancel, mul_one]
  rightInv := by
    intro a
    dsimp
    rw [←mul_assoc, ←mul_assoc, inv_mul_cancel, one_mul,
      mul_assoc, inv_mul_cancel, mul_one]
  resp_mul := by
    intro a b
    dsimp
    rw [mul_assoc (x⁻¹ * a), ←mul_assoc x, ←mul_assoc x, mul_inv_cancel, one_mul]
    repeat rw [mul_assoc]
  resp_one := by
    dsimp
    rw [mul_one, inv_mul_cancel]

instance : GroupOps Unit where
  mul _ _ := ()
  one := ()
  inv _ := ()
  div _ _ := ()
  npow _ _ := ()
  zpow _ _ := ()

def Trivial : Group Unit where
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  div_eq_mul_inv _ _ := rfl
  zpow_ofNat _ _ := rfl
  zpow_negSucc _ _ := rfl
  inv_mul_cancel _ := rfl

def toTrivial (g: Group α) : g →* Trivial where
  toFun _ := 1
  resp_mul := rfl
  resp_one := rfl

def ofTrivial (g: Group α) : Trivial ↪* g where
  toFun _ := 1
  inj { _ _ } _  := rfl
  resp_mul := by
    intro x y
    rw [mul_one]
  resp_one := rfl

def toTrivial.Subsingleton (g: Group α) : Subsingleton (g →* Trivial) where
  allEq a b := by
    apply DFunLike.ext
    intro x
    rfl

def ofTrivial.Subsingleton (g: Group α) : Subsingleton (Trivial →* g) where
  allEq a b := by
    apply DFunLike.ext
    intro x
    show a 1 = b 1
    rw [resp_one, resp_one]

def Equiv.toHom_comp_toHom (h: b ≃* c) (g: a ≃* b) :
  h.toHom.comp g.toHom = (g.trans h).toHom := rfl

def Equiv.refl_toHom : GroupEquiv.refl.toHom = GroupHom.id a := rfl

def Equiv.trans_symm (h: a ≃* b) :
  h.trans h.symm = .refl := by
  apply DFunLike.ext
  intro x
  show h.symm (h x) = x
  rw [h.coe_symm]

def Equiv.symm_trans (h: a ≃* b) :
  h.symm.trans h = .refl := by
  apply DFunLike.ext
  intro x
  show h (h.symm x) = x
  rw [h.symm_coe]

end Group

namespace AbelianGroup

attribute [coe] AbelianGroup.toGroup

def ofAdd (α: Type*) [AddGroupOps α] [IsAddGroup α] [IsAddCommMagma α] :=
  AbelianGroup.mk (Group.ofAdd α) inferInstance

instance (g: AbelianGroup α) : IsCommMagma (g: Group α).Elem := g.toIsCommMagma

end AbelianGroup
