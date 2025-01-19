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

class HasNormalSubgroup (α: Type*) where
  NormalSubgroup: α -> α -> Prop

infix:75 " ◀ " => HasNormalSubgroup.NormalSubgroup

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

instance : Inhabited g.ty where
  default := 1

@[simp]
def mul'_eq {g: Group} (a b: g.ty) : g.mul' a b = a * b := rfl
@[simp]
def inv'_eq {g: Group} (a: g.ty) : g.inv' a = a⁻¹ := rfl
@[simp]
def one'_eq {g: Group} : g.one' = 1 := rfl

def Group.mul_inv' {g: Group} (a: g.ty) : g.mul' a (g.inv' a) = 1 := by
  rw [←g.one_mul' (g.mul' a (g.inv' a))]
  conv => { lhs; rw [←g.inv_mul' (a⁻¹)] }
  erw [←g.mul_assoc', g.mul_assoc' (g.inv' a⁻¹), g.inv_mul', g.mul_assoc', g.one_mul', g.inv_mul']
  rfl
def Group.mul_one' {g: Group} (a: g.ty) : a * 1 = a := by
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

namespace Group

structure SubgroupEmbedding (a b: Group) extends a.ty ↪ b.ty where
  resp_one: toFun 1 = 1
  resp_inv: ∀x, toFun (x⁻¹) = (toFun x)⁻¹
  resp_mul: ∀x y, toFun (x * y) = toFun x * toFun y

structure Isomorphsism (a b: Group) extends a.ty ≃ b.ty where
  resp_one: toFun 1 = 1
  resp_inv: ∀x, toFun (x⁻¹) = (toFun x)⁻¹
  resp_mul: ∀x y, toFun (x * y) = toFun x * toFun y

structure NormalSubgroupEmbedding (N G: Group) extends SubgroupEmbedding N G where
  conj_in_norm: ∀g: G.ty, ∀n: N.ty, g * toFun n * g⁻¹ ∈ Set.range toFun

def Isomorphsism.inv_resp_one (iso: Isomorphsism a b) : iso.invFun 1 = 1 := by
  apply iso.toFun_inj
  rw [iso.resp_one, iso.rightInv]
def Isomorphsism.inv_resp_inv (iso: Isomorphsism a b) (x: b.ty) : iso.invFun (x⁻¹) = (iso.invFun x)⁻¹ := by
  apply iso.toFun_inj
  rw [iso.resp_inv, iso.rightInv, iso.rightInv]
def Isomorphsism.inv_resp_mul (iso: Isomorphsism a b) (x y: b.ty) : iso.invFun (x * y) = (iso.invFun x) * (iso.invFun y) := by
  apply iso.toFun_inj
  rw [iso.resp_mul, iso.rightInv, iso.rightInv, iso.rightInv]

instance : IsEquivLike (Isomorphsism a b) a.ty b.ty where
  coe a := a.toEquiv
  inv a := a.toEquiv.symm
  leftInv a := a.leftInv
  rightInv a := a.rightInv
  inj a b eq eq' := by
    cases a; cases b; dsimp at *; congr
    apply Equiv.toFun_inj'
    assumption

inductive IsSubgroup (a b: Group): Prop where
| ofSub (sub: SubgroupEmbedding a b)

inductive IsIsomorphic (a b: Group): Prop where
| ofIso (iso: Isomorphsism a b)

inductive IsNormalSubgroup (a b: Group): Prop where
| ofSub (sub: NormalSubgroupEmbedding a b)

instance : HasSubset Group := ⟨Group.IsSubgroup⟩

instance : HasNormalSubgroup Group := ⟨Group.IsNormalSubgroup⟩

def IsSubgroup.intro {a b: Group}
  (emb: a.ty ↪ b.ty)
  (resp_one: emb 1 = 1)
  (resp_inv: ∀x, emb (x⁻¹) = (emb x)⁻¹)
  (resp_mul: ∀x y, emb (x * y) = emb x * emb y) : a ⊆ b := ⟨⟨emb, resp_one, resp_inv, resp_mul⟩⟩

def IsNormalSubgroup.intro {N G: Group}
  (emb: N.ty ↪ G.ty)
  (resp_one: emb 1 = 1)
  (resp_inv: ∀x, emb (x⁻¹) = (emb x)⁻¹)
  (resp_mul: ∀x y, emb (x * y) = emb x * emb y)
  (conj_in_norm: ∀g: G.ty, ∀n: N.ty, g * emb.toFun n * g⁻¹ ∈ Set.range emb.toFun) : N ◀ G := .ofSub <| by
  apply NormalSubgroupEmbedding.mk _ _
  apply SubgroupEmbedding.mk
  all_goals assumption

def IsIsomorphic.intro {a b: Group}
  (eq: a.ty ≃ b.ty)
  (resp_one: eq 1 = 1)
  (resp_inv: ∀x, eq (x⁻¹) = (eq x)⁻¹)
  (resp_mul: ∀x y, eq (x * y) = eq x * eq y) : IsIsomorphic a b := ⟨⟨eq, resp_one, resp_inv, resp_mul⟩⟩

def Isomorphsism.toSubgroupEmbedding (h: Isomorphsism a b) : SubgroupEmbedding a b where
  toEmbedding := h.toEmbedding
  resp_one := h.resp_one
  resp_inv := h.resp_inv
  resp_mul := h.resp_mul

def Isomorphsism.toNormalSubgroupEmbedding (h: Isomorphsism a b) : NormalSubgroupEmbedding a b where
  toEmbedding := h.toEmbedding
  resp_one := h.resp_one
  resp_inv := h.resp_inv
  resp_mul := h.resp_mul
  conj_in_norm := by
    intro x y
    simp
    apply Set.mem_range.mpr
    exists (h.invFun x) * y * (h.invFun x⁻¹)
    simp [Equiv.toEmbedding]
    rw [h.resp_mul, h.rightInv, h.resp_mul, h.rightInv]

def SubgroupEmbedding.respIso
  (ac: Isomorphsism a c)
  (bd: Isomorphsism b d)
  (ab: SubgroupEmbedding a b)
  : SubgroupEmbedding c d where
  toEmbedding := bd.toEmbedding.comp <| ab.toEmbedding.comp ac.symm.toEmbedding
  resp_one := by
    simp [Equiv.toEmbedding, Equiv.symm, Embedding.comp]
    rw [ac.inv_resp_one, ab.resp_one, bd.resp_one]
  resp_inv x := by
    simp [Equiv.toEmbedding, Equiv.symm, Embedding.comp]
    rw [ac.inv_resp_inv, ab.resp_inv, bd.resp_inv]
  resp_mul x y := by
    simp [Equiv.toEmbedding, Equiv.symm, Embedding.comp]
    rw [ac.inv_resp_mul, ab.resp_mul, bd.resp_mul]

def NormalSubgroupEmbedding.respIso
  (ac: Isomorphsism a c)
  (bd: Isomorphsism b d)
  (ab: NormalSubgroupEmbedding a b)
  : NormalSubgroupEmbedding c d where
  toSubgroupEmbedding := SubgroupEmbedding.respIso ac bd ab.toSubgroupEmbedding
  conj_in_norm g n := by
    simp [SubgroupEmbedding.respIso,
      Equiv.toEmbedding, Equiv.symm, Embedding.comp]
    have ⟨x, prf⟩ := Set.mem_range.mp <| ab.conj_in_norm (bd.invFun g) (ac.invFun n)
    apply Set.mem_range.mpr
    exists ac.toFun x
    simp
    rw [ac.leftInv, ←prf]
    simp [bd.resp_mul]
    rw [bd.rightInv, bd.resp_inv, bd.rightInv]

def Isomorphsism.refl (a: Group) : Isomorphsism a a where
  toEquiv := .refl
  resp_one := rfl
  resp_inv _ := rfl
  resp_mul _ _ := rfl

def Isomorphsism.symm (h: Isomorphsism a b) : Isomorphsism b a where
  toEquiv := h.toEquiv.symm
  resp_one := by
    simp [Equiv.symm]
    rw [h.inv_resp_one]
  resp_inv _ := by
    simp [Equiv.symm]
    rw [h.inv_resp_inv]
  resp_mul x y := by
    simp [Equiv.symm]
    rw [h.inv_resp_mul]

def Isomorphsism.trans (h: Isomorphsism a b) (g: Isomorphsism b c) : Isomorphsism a c where
  toEquiv := h.toEquiv.trans g.toEquiv
  resp_one := by
    simp [Equiv.trans]
    rw [h.resp_one, g.resp_one]
  resp_inv _ := by
    simp [Equiv.trans]
    rw [h.resp_inv, g.resp_inv]
  resp_mul x y := by
    simp [Equiv.trans]
    rw [h.resp_mul, g.resp_mul]

def SubgroupEmbedding.trans (h: SubgroupEmbedding a b) (g: SubgroupEmbedding b c) : SubgroupEmbedding a c where
  toEmbedding := g.toEmbedding.comp h.toEmbedding
  resp_one := by
    simp [Embedding.comp]
    rw [h.resp_one, g.resp_one]
  resp_inv _ := by
    simp [Embedding.comp]
    rw [h.resp_inv, g.resp_inv]
  resp_mul x y := by
    simp [Embedding.comp]
    rw [h.resp_mul, g.resp_mul]

def SubgroupEmbedding.resp_npow {a b: Group} (h: SubgroupEmbedding a b) :
  ∀(x: a.ty) (n: ℕ), h.toFun (x ^ n) = (h.toFun x) ^ n := by
  intro x n
  induction n with
  | zero => simp [npow_zero, resp_one]
  | succ n ih => simp [npow_succ]; rw [resp_mul, ih]

def SubgroupEmbedding.resp_zpow {a b: Group} (h: SubgroupEmbedding a b) :
  ∀(x: a.ty) (n: ℤ), h.toFun (x ^ n) = (h.toFun x) ^ n := by
  intro x n
  cases n with
  | ofNat n => simp [zpow_ofNat, resp_npow]
  | negSucc n => simp [zpow_negSucc, resp_inv, resp_npow]

def SubgroupEmbedding.resp_div {a b: Group} (h: SubgroupEmbedding a b) :
  ∀(x y: a.ty), h.toFun (x / y) = (h.toFun x) / (h.toFun y) := by
  intro x n
  erw [resp_mul, resp_inv]; rfl

def NormalSubgroupEmbedding.resp_npow {a b: Group} (h: NormalSubgroupEmbedding a b) :
  ∀(x: a.ty) (n: ℕ), h.toFun (x ^ n) = (h.toFun x) ^ n := h.toSubgroupEmbedding.resp_npow

def NormalSubgroupEmbedding.resp_zpow {a b: Group} (h: NormalSubgroupEmbedding a b) :
  ∀(x: a.ty) (n: ℤ), h.toFun (x ^ n) = (h.toFun x) ^ n := h.toSubgroupEmbedding.resp_zpow

def NormalSubgroupEmbedding.resp_div {a b: Group} (h: NormalSubgroupEmbedding a b) :
  ∀(x y: a.ty), h.toFun (x / y) = (h.toFun x) / (h.toFun y) := h.toSubgroupEmbedding.resp_div

def Isomorphsism.resp_npow {a b: Group} (h: NormalSubgroupEmbedding a b) :
  ∀(x: a.ty) (n: ℕ), h.toFun (x ^ n) = (h.toFun x) ^ n := h.toSubgroupEmbedding.resp_npow

def Isomorphsism.resp_zpow {a b: Group} (h: NormalSubgroupEmbedding a b) :
  ∀(x: a.ty) (n: ℤ), h.toFun (x ^ n) = (h.toFun x) ^ n := h.toSubgroupEmbedding.resp_zpow

def Isomorphsism.resp_div {a b: Group} (h: NormalSubgroupEmbedding a b) :
  ∀(x y: a.ty), h.toFun (x / y) = (h.toFun x) / (h.toFun y) := h.toSubgroupEmbedding.resp_div

def Isomorphsism.inv_resp_npow {a b: Group} (h: Isomorphsism a b) :
  ∀(x: b.ty) (n: ℕ), h.invFun (x ^ n) = (h.invFun x) ^ n := h.symm.toSubgroupEmbedding.resp_npow

def Isomorphsism.inv_resp_zpow {a b: Group} (h: Isomorphsism a b) :
  ∀(x: b.ty) (n: ℤ), h.invFun (x ^ n) = (h.invFun x) ^ n := h.symm.toSubgroupEmbedding.resp_zpow

def Isomorphsism.inv_resp_div {a b: Group} (h: Isomorphsism a b) :
  ∀(x y: b.ty), h.invFun (x / y) = (h.invFun x) / (h.invFun y) := h.symm.toSubgroupEmbedding.resp_div

def SubgroupEmbedding.refl (a: Group): SubgroupEmbedding a a := (Isomorphsism.refl a).toSubgroupEmbedding
def NormalSubgroupEmbedding.refl (a: Group): NormalSubgroupEmbedding a a := (Isomorphsism.refl a).toNormalSubgroupEmbedding

def IsIsomorphic.IsSubgroup {a b: Group} (h: a.IsIsomorphic b) : a.IsSubgroup b := by
  obtain ⟨iso⟩ := h
  apply IsSubgroup.ofSub iso.toSubgroupEmbedding

def IsIsomorphic.IsNormalSubgroup {a b: Group} (h: a.IsIsomorphic b) : a ◀ b := by
  obtain ⟨iso⟩ := h
  apply IsNormalSubgroup.ofSub iso.toNormalSubgroupEmbedding

def IsNormalSubgroup.IsSubgroup {a b: Group} (h: a ◀ b) : a ⊆ b := by
  obtain ⟨emb⟩ := h
  exact ⟨emb.toSubgroupEmbedding⟩

@[refl]
def IsIsomorphic.refl (a: Group) : a.IsIsomorphic a := by
  apply IsIsomorphic.intro Equiv.refl <;> (intros; rfl)

@[symm]
def IsIsomorphic.symm {a b: Group} (h: a.IsIsomorphic b) : b.IsIsomorphic a := by
  obtain ⟨iso⟩ := h
  exact ⟨iso.symm⟩

def IsIsomorphic.trans {a b c: Group} :
  a.IsIsomorphic b -> b.IsIsomorphic c -> a.IsIsomorphic c := by
  intro ⟨ab⟩ ⟨bc⟩
  exact ⟨ab.trans bc⟩

def IsSubgroup.refl (a: Group) : a ⊆ a := (IsIsomorphic.refl a).IsSubgroup
def IsSubgroup.trans {a b c: Group} : a ⊆ b -> b ⊆ c -> a ⊆ c := by
  intro h g
  obtain ⟨h, hresp_one, hresp_inv, hresp_mul⟩ := h
  obtain ⟨g, gresp_one, gresp_inv, gresp_mul⟩ := g
  apply IsSubgroup.intro (g.comp h)
  simp [Embedding.comp]
  rw [hresp_one, gresp_one]
  simp [Embedding.comp]; intro x
  rw [hresp_inv, gresp_inv]
  simp [Embedding.comp]; intro x y
  rw [hresp_mul, gresp_mul]

def IsNormalSubgroup.refl (a: Group) : a ◀ a := (IsIsomorphic.refl a).IsNormalSubgroup

@[refl]
def gsub_refl (a: Group) : a ⊆ a := IsSubgroup.refl _
def gsub_trans {a b c: Group} : a ⊆ b -> b ⊆ c -> a ⊆ c := IsSubgroup.trans

@[refl]
def nsub_refl (a: Group) : a ◀ a := by
  apply IsNormalSubgroup.ofSub
  apply NormalSubgroupEmbedding.refl

instance setoid : Setoid Group where
  r := IsIsomorphic
  iseqv := ⟨.refl, .symm, .trans⟩

@[refl]
def eqv_refl (a: Group) : a ≈ a := IsIsomorphic.refl _
@[symm]
def eqv_symm {a b: Group} : a ≈ b -> b ≈ a := IsIsomorphic.symm
def eqv_trans {a b: Group} : a ≈ b -> b ≈ c -> a ≈ c := IsIsomorphic.trans

def IsoClass := Quotient setoid
def IsoClass.mk : Group -> IsoClass := Quotient.mk _

scoped notation "⟦" a "⟧" => IsoClass.mk a

@[induction_eliminator]
def IsoClass.ind {motive: IsoClass -> Prop} (mk: ∀x, motive ⟦x⟧) : ∀g, motive g := Quotient.ind mk
@[induction_eliminator]
def IsoClass.ind₂ {motive: IsoClass -> IsoClass -> Prop} (mk: ∀a b, motive ⟦a⟧ ⟦b⟧) : ∀a b, motive a b := Quotient.ind₂ mk
@[induction_eliminator]
def IsoClass.ind₃ {motive: IsoClass -> IsoClass -> IsoClass -> Prop} (mk: ∀a b c, motive ⟦a⟧ ⟦b⟧ ⟦c⟧) : ∀a b c, motive a b c := by
  intro a b c
  induction a, b with | mk =>
  induction c with | mk =>
  apply mk
@[induction_eliminator]
def IsoClass.ind₄ {motive: IsoClass -> IsoClass -> IsoClass -> IsoClass -> Prop} (mk: ∀a b c d, motive ⟦a⟧ ⟦b⟧ ⟦c⟧ ⟦d⟧) : ∀a b c d, motive a b c d := by
  intro a b c d
  induction a, b with | mk =>
  induction c, d with | mk =>
  apply mk

instance : Membership Group IsoClass where
  mem a b := a = ⟦b⟧

end Group

namespace Group

def Trivial: Group where
  ty := PUnit
  mul' _ _ := ()
  one' := ()
  inv' _ := ()
  mul_assoc' _ _ _ := rfl
  one_mul' _ := rfl
  inv_mul' _ := rfl

def IsoClass.Trivial: IsoClass := ⟦Group.Trivial⟧

instance : One Group := ⟨.Trivial⟩
instance : One IsoClass := ⟨.Trivial⟩

instance : Subsingleton Trivial.ty :=
  inferInstanceAs (Subsingleton PUnit)
instance : Subsingleton (1: Group).ty :=
  inferInstanceAs (Subsingleton PUnit)

def eqv_gsub_eqv {a b c d: Group} : a ≈ c -> b ≈ d -> a ⊆ b -> c ⊆ d := by
  intro ⟨ac⟩ ⟨bd⟩ ⟨sub⟩
  exact ⟨sub.respIso ac bd⟩

def eqv_gsub {a b k: Group} : a ≈ b -> a ⊆ k -> b ⊆ k := by
  intro eqv a_sub_k
  apply eqv_gsub_eqv
  assumption
  rfl
  assumption

def gsub_eqv {a b k: Group} : a ≈ b -> k ⊆ a -> k ⊆ b := by
  intro eqv a_sub_k
  apply eqv_gsub_eqv
  rfl
  assumption
  assumption

def eqv_nsub_eqv {a b c d: Group} : a ≈ c -> b ≈ d -> a ◀ b -> c ◀ d := by
  intro ⟨ac⟩ ⟨bd⟩ ⟨ab⟩
  exact ⟨ab.respIso ac bd⟩

def eqv_nsub {a b k: Group} : a ≈ b -> a ◀ k -> b ◀ k := by
  intro eqv a_sub_k
  apply eqv_nsub_eqv
  assumption
  rfl
  assumption

def nsub_eqv {a b k: Group} : a ≈ b -> k ◀ a -> k ◀ b := by
  intro eqv a_sub_k
  apply eqv_nsub_eqv
  rfl
  assumption
  assumption

-- the trivial group is a subgroup of every group
def one_nsub (a: Group) : 1 ◀ a := by
  apply IsNormalSubgroup.intro ⟨fun _ => 1, _⟩
  rfl
  intros
  simp
  intros
  rw [inv_one]
  intro x y
  dsimp
  rw [one_mul]
  intro a n
  dsimp
  apply Set.mem_range.mpr
  exists 1
  rw [mul_one, mul_inv_cancel]
  intros x y eq
  rfl

-- the trivial group is a subgroup of every group
def one_gsub (a: Group) : 1 ⊆ a := by
  apply IsSubgroup.intro ⟨fun _ => 1, _⟩
  rfl
  intros
  simp
  intros
  rw [inv_one]
  intro x y
  dsimp
  rw [one_mul]
  intros x y eq
  rfl

-- the only subgroup of the trivial subgroup is itself up to isomorphism
def gsub_one (a: Group) : a ⊆ 1 -> a ∈ (1: IsoClass) := by
  intro ⟨h, resp_one, resp_inv, resp_mul⟩
  apply Quotient.sound
  apply IsIsomorphic.intro
  case a.eq =>
    apply Equiv.mk (fun _ => 1) h.toFun
    intro _
    rfl
    intro
    simp
    apply h.inj
    rfl
  rfl
  intros; simp; rw [inv_one]
  intros; simp; rw [one_mul]

def IsoClass.IsSubgroup : IsoClass -> IsoClass -> Prop := by
  apply Quotient.lift₂ Group.IsSubgroup
  intros; ext
  apply Iff.intro
  apply eqv_gsub_eqv <;> assumption
  apply eqv_gsub_eqv <;> (symm; assumption)

def IsoClass.IsNormalSubgroup : IsoClass -> IsoClass -> Prop := by
  apply Quotient.lift₂ Group.IsNormalSubgroup
  intros; ext
  apply Iff.intro
  apply eqv_nsub_eqv <;> assumption
  apply eqv_nsub_eqv <;> (symm; assumption)

instance : HasSubset IsoClass where
  Subset := IsoClass.IsSubgroup
instance : HasNormalSubgroup IsoClass where
  NormalSubgroup := IsoClass.IsNormalSubgroup

def IsoClass.IsSubgroup.def {a b: IsoClass} :
  a ⊆ b -> ∀a' ∈ a, ∃b' ∈ b, a' ⊆ b' := by
  induction a, b with | mk a b =>
  intro a_sub_b a' a'_in_a
  replace a_eqv_a' := Quotient.exact a'_in_a
  replace a_sub_b: a ⊆ b := a_sub_b
  exists b
  apply And.intro
  rfl
  apply eqv_gsub
  assumption
  assumption

def IsoClass.IsNormalSubgroup.IsSubgroup {a b: IsoClass} : a ◀ b -> a ⊆ b := by
  induction a, b with | mk a b =>
  apply Group.IsNormalSubgroup.IsSubgroup

-- the class trivial group is a normal subgroup of every group
def IsoClass.one_nsub (a: IsoClass) : 1 ◀ a := by
  induction a with | mk a =>
  show 1 ◀ a
  apply Group.one_nsub

-- the class trivial group can embed into any other isomorphism classs
def IsoClass.one_sub (a: IsoClass) : 1 ⊆ a := by
  apply IsNormalSubgroup.IsSubgroup
  apply one_nsub

def IsSimple (a: Group) : Prop := ∀n, n ◀ a -> n ≈ 1 ∨ n ≈ a

def IsSimple.spec (a b: Group) : a ≈ b -> a.IsSimple -> b.IsSimple := by
  intro eq asimp n norm
  suffices n ≈ 1 ∨ n ≈ a by
    cases this; left; assumption
    right; apply eqv_trans; assumption; assumption
  apply asimp
  exact nsub_eqv eq.symm norm

def IsoClass.IsSimple : IsoClass -> Prop := by
  apply Quotient.lift Group.IsSimple
  intros _ _ eq
  ext
  apply Iff.intro
  apply IsSimple.spec; assumption
  apply IsSimple.spec; symm; assumption

def mk_IsSimple : ⟦a⟧.IsSimple = a.IsSimple := rfl

def Nontrivial (a: Group) := ∃x: a.ty, x ≠ 1
def Nontrivial.spec (a b: Group) : a ≈ b -> a.Nontrivial -> b.Nontrivial := by
  intro ⟨eqv, resp_one, resp_inv, resp_mul⟩ ⟨x, h⟩
  exists eqv x
  intro g
  apply h
  rw [←resp_one] at g
  exact Equiv.toFun_inj _ g

def Nontrivial_def (a: Group) : a.Nontrivial ↔ a ∉ IsoClass.Trivial := by
  apply Iff.intro
  intro ⟨x, eq⟩ g
  have ⟨eqv, resp_one, resp_inv, resp_mul⟩ := Quotient.exact g
  have := Equiv.invFun_inj eqv
  unfold Function.Injective at this
  have := @this x 1 rfl
  contradiction
  intro h
  replace h : ¬a ≈ Trivial := by
    intro g
    apply h
    apply Quot.sound
    exact g.symm
  let emb : (ty 1) ↪ a.ty := by
    apply Embedding.mk (fun _ => 1)
    intro x y eq; rfl
  have : ¬Function.Surjective emb.toFun := by
    intro surj
    apply h
    have ⟨eqv, eqv_eq⟩ := Equiv.ofBij ⟨emb.inj, surj⟩
    apply IsIsomorphic.intro eqv.symm
    rfl
    intros; rfl
    intros; rfl
  replace ⟨x, this⟩ := Classical.not_forall.mp this
  replace this := fun y => not_exists.mp this y
  exists x
  intro h
  cases h
  apply this ()
  rfl

def Trivial.notNontrivial : ¬Nontrivial 1 := by
  intro ⟨_, h⟩
  apply h rfl

def IsoClass.Trivial.notNontrivial : ¬Nontrivial 1 := by
  intro ⟨_, h⟩
  apply h rfl

def Trivial.IsSimple : IsSimple 1 := by
  intro x nsub_one; left; symm
  exact Quotient.exact <| gsub_one _ (IsNormalSubgroup.IsSubgroup nsub_one)

def IsoClass.Trivial.IsSimple : IsoClass.IsSimple 1 := by
  apply Eq.mpr mk_IsSimple
  exact Group.Trivial.IsSimple

def eq_trivial_of_subsingleton (a: Group) [Subsingleton a.ty] : a ≈ 1 := by
  apply IsIsomorphic.intro (unique_eq_unique _ _)
  apply Subsingleton.allEq
  intros; apply Subsingleton.allEq
  intros; apply Subsingleton.allEq

end Group

end
