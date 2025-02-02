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

protected structure Hom (a: Group α) (b: Group β) extends MulHom a b, OneHom a b
protected structure Embedding (a: Group α) (b: Group β) extends a ↪ b, Group.Hom a b where
protected structure Equiv (a: Group α) (b: Group β) extends a ≃ b, Group.Hom a b where

infixr:25 " →g " => Group.Hom
infixr:25 " ↪g " => Group.Embedding
infixr:25 " ≃g " => Group.Equiv

instance : FunLike (Group.Hom a b) a b where
  coe f := f.toFun
  coe_inj := by
    intro x y eq
    cases x; cases y
    congr
    apply DFunLike.coe_inj
    assumption

instance : MulHomClass (Group.Hom a b) a b where
  resp_mul f := f.resp_mul

instance : OneHomClass (Group.Hom a b) a b where
  resp_one f := f.resp_one

instance : InvHomClass (Group.Hom a b) a b where
  resp_inv f y := by
    symm
    apply inv_eq_of_mul_left
    rw [←resp_mul, mul_inv_cancel, resp_one]

instance : FunLike (Group.Embedding a b) a b where
  coe f := f.toFun
  coe_inj := by
    intro x y eq
    cases x; cases y
    congr
    apply DFunLike.coe_inj
    assumption

instance : MulHomClass (Group.Embedding a b) a b where
  resp_mul f := f.resp_mul

instance : OneHomClass (Group.Embedding a b) a b where
  resp_one f := f.resp_one

instance : InvHomClass (Group.Embedding a b) a b where
  resp_inv f y := by
    symm
    apply inv_eq_of_mul_left
    rw [←resp_mul, mul_inv_cancel, resp_one]

instance : FunLike (Group.Equiv a b) a b where
  coe f := f.toFun
  coe_inj := by
    intro x y eq
    cases x; cases y
    congr
    apply DFunLike.coe_inj
    assumption

instance : MulHomClass (Group.Equiv a b) a b where
  resp_mul f := f.resp_mul

instance : OneHomClass (Group.Equiv a b) a b where
  resp_one f := f.resp_one

instance : InvHomClass (Group.Equiv a b) a b where
  resp_inv f y := by
    symm
    apply inv_eq_of_mul_left
    rw [←resp_mul, mul_inv_cancel, resp_one]

def Equiv.toEmbedding (f: a ≃g b) : a ↪g b where
  toEmbedding := f.toEquiv.toEmbedding
  resp_mul := f.resp_mul
  resp_one := f.resp_one

def Hom.id : a →g a where
  toFun x := x
  resp_mul := rfl
  resp_one := rfl

def Hom.comp (h: b →g c) (g: a →g b) : a →g c where
  toFun := h ∘ g
  resp_mul := by
    intro x y
    dsimp
    rw [resp_mul, resp_mul]
  resp_one := by
    dsimp
    rw [OneHomClass.resp_one, OneHomClass.resp_one]

def Embedding.refl : a ↪g a where
  toEmbedding := _root_.Embedding.refl
  resp_mul := rfl
  resp_one := rfl

def Embedding.trans (h: a ↪g b) (g: b ↪g c): a ↪g c where
  toEmbedding := h.toEmbedding.trans g.toEmbedding
  resp_mul := by
    intro x y
    show g.toFun (h.toFun (x * y)) = _
    rw [h.resp_mul, g.resp_mul]
    rfl
  resp_one := by
    show g.toFun (h.toFun 1) = 1
    rw [h.resp_one, g.resp_one]

def Equiv.refl : a ≃g a where
  toEquiv := _root_.Equiv.refl
  resp_mul := rfl
  resp_one := rfl

def Equiv.symm (h: a ≃g b): b ≃g a where
  toEquiv := h.toEquiv.symm
  resp_mul := by
    intro x y
    apply h.toFun_inj
    show h.toEquiv (h.toEquiv.symm (x * y)) = h.toFun _
    rw [h.symm_coe, h.resp_mul]
    show _ = h.toEquiv (h.toEquiv.symm x) * h.toEquiv (h.toEquiv.symm y)
    rw [h.symm_coe, h.symm_coe]
  resp_one := by
    apply h.toFun_inj
    show h.toEquiv (h.toEquiv.symm 1) = h 1
    rw [h.symm_coe, OneHomClass.resp_one]

def Equiv.trans (h: a ≃g b) (g: b ≃g c): a ≃g c where
  toEquiv := h.toEquiv.trans g.toEquiv
  resp_mul := by
    intro x y
    show g.toFun (h.toFun (x * y)) = _
    rw [h.resp_mul, g.resp_mul]
    rfl
  resp_one := by
    show g.toFun (h.toFun 1) = 1
    rw [h.resp_one, g.resp_one]

-- conjugate each the elements of `A` by `x` as an group equivalence relation
def conj (A: Group α) (x: A) : A ≃g A where
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

def toTrivial : g →g Trivial where
  toFun _ := 1
  resp_mul := rfl
  resp_one := rfl

def ofTrivial : Trivial ↪g g where
  toFun _ := 1
  inj { _ _ } _  := rfl
  resp_mul := by
    intro x y
    rw [mul_one]
  resp_one := rfl

def toTrivial.Subsingleton : Subsingleton (g →g Trivial) where
  allEq a b := by
    apply DFunLike.ext
    intro x
    rfl

def ofTrivial.Subsingleton : Subsingleton (Trivial →g g) where
  allEq a b := by
    apply DFunLike.ext
    intro x
    show a 1 = b 1
    rw [resp_one, resp_one]

end Group
