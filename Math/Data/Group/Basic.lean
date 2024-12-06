import Math.Type.Basic
import Math.Algebra.Ring
import Math.Data.QuotLike.Basic
import Math.Type.Finite
import Math.Data.Set.Finite
import Math.Data.Fin.Basic
import Math.Data.Set.Basic

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

def Nat.sub_mul (a b k: Nat)  : (a - b) * k = a * k - b * k := by sorry

namespace Group

instance (g: Group) : One g.ty := ⟨g.one'⟩
instance (g: Group) : Mul g.ty := ⟨g.mul'⟩
instance (g: Group) : Inv g.ty := ⟨g.inv'⟩

def mul_assoc {g: Group} (a b c: g.ty) : a * b * c = a * (b * c) := g.mul_assoc' _ _ _
def one_mul {g: Group} (a: g.ty) : 1 * a = a := g.one_mul' _
def inv_mul {g: Group} (a: g.ty) : a⁻¹ * a = 1 := g.inv_mul' _
def mul_inv {g: Group} (a: g.ty) : a * a⁻¹ = 1 := by
  rw [←one_mul (a * a⁻¹)]
  conv => { lhs; rw [←inv_mul (a⁻¹)] }
  rw [←mul_assoc, mul_assoc (a⁻¹⁻¹), inv_mul, mul_assoc, one_mul, inv_mul]
def mul_one {g: Group} (a: g.ty) : a * 1 = a := by
  rw [←inv_mul a, ←mul_assoc, mul_inv, one_mul]
def mul_cancel_left {g: Group} {k a b: g.ty} : k * a = k * b -> a = b := by
  intro eq
  rw [←one_mul a, ←one_mul b, ←inv_mul k, mul_assoc, mul_assoc, eq]
def mul_cancel_right {g: Group} {k a b: g.ty} : a * k = b * k -> a = b := by
  intro eq
  rw [←mul_one a, ←mul_one b, ←mul_inv k, ←mul_assoc, ←mul_assoc, eq]
def inv_unique {g: Group} {a b: g.ty} : a * b = 1 -> a = b⁻¹ := by
  intro m
  apply mul_cancel_right
  rw [inv_mul]
  assumption
def inv_one (g: Group) : (1: g.ty)⁻¹ = 1 := by
  apply mul_cancel_left
  rw [mul_inv, one_mul]
def inv_inj (g: Group) : Function.Injective (fun x: g.ty => x⁻¹) := by
  intro a b eq
  simp at eq
  apply mul_cancel_right
  rw [mul_inv, eq, mul_inv]

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

inductive IsSubgroup (a b: Group): Prop where
| ofSub (sub: SubgroupEmbedding a b)

inductive IsNormalSubgroup (a b: Group): Prop where
| ofSub (sub: NormalSubgroupEmbedding a b)

inductive IsIsomorphic (a b: Group): Prop where
| ofIso (iso: Isomorphsism a b)

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
    simp [toSubgroupEmbedding, SubgroupEmbedding.respIso,
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

def sub_refl (a: Group) : a ⊆ a := IsSubgroup.refl _
def sub_trans {a b c: Group} : a ⊆ b -> b ⊆ c -> a ⊆ c := IsSubgroup.trans

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
instance : QuotientLike setoid IsoClass where

local notation "⟦" a "⟧" => IsoClass.mk a

instance : Membership Group IsoClass where
  mem a b := a = ⟦b⟧

def fin_inverse (x: Fin n): Fin n :=
  Fin.mk ((n - x.val) % n) (Nat.mod_lt _ (Nat.zero_lt_of_ne_zero (by
    intro h
    cases h
    exact x.elim0)))

-- a cyclic group with n elements
def FinCyclic (n: Nat) [h: NeZero n] : Group where
  ty := Fin n
  mul' a b := a + b
  one' := ⟨0, Nat.zero_lt_of_ne_zero h.ne⟩
  inv' := fin_inverse
  mul_assoc' := by
    intro a b c
    simp [Fin.add_def]
    rw [Nat.add_assoc]
  one_mul' := Fin.zero_add
  inv_mul' := by
    intro x
    simp [Fin.add_def, fin_inverse]

-- the cyclic groups of order n elements
def IsoClass.Cyclic (n: Nat) [NeZero n] := ⟦FinCyclic n⟧

example [NeZero n] : FinCyclic n ∈ IsoClass.Cyclic n := rfl

def Trivial : Group where
  ty := Unit
  one' := ()
  inv' _ := ()
  mul' _ _ := ()
  mul_assoc' _ _ _ := rfl
  one_mul' _ := rfl
  inv_mul' _ := rfl

-- the cyclic groups of order n elements
def IsoClass.Trivial := ⟦.Trivial⟧

instance : One Group := ⟨.Trivial⟩
instance : One IsoClass := ⟨.Trivial⟩

def eqv_sub_eqv {a b c d: Group} : a ≈ c -> b ≈ d -> a ⊆ b -> c ⊆ d := by
  intro ⟨ac⟩ ⟨bd⟩ ⟨sub⟩
  exact ⟨sub.respIso ac bd⟩

def eqv_sub {a b k: Group} : a ≈ b -> a ⊆ k -> b ⊆ k := by
  intro eqv a_sub_k
  apply eqv_sub_eqv
  assumption
  rfl
  assumption

def sub_eqv {a b k: Group} : a ≈ b -> k ⊆ a -> k ⊆ b := by
  intro eqv a_sub_k
  apply eqv_sub_eqv
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
def one_sub (a: Group) : 1 ⊆ a := by
  apply IsSubgroup.intro ⟨fun _ => 1, _⟩
  rfl
  intros
  simp
  rw [inv_one]
  simp
  intros
  rw [mul_one]
  intros x y eq
  rfl

-- the only subgroup of the trivial subgroup is itself up to isomorphism
def sub_one (a: Group) : a ⊆ 1 -> a ∈ (1: IsoClass) := by
  intro ⟨h, resp_one, resp_inv, resp_mul⟩
  apply quot.sound
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
  intros
  simp
  rw [inv_one]
  intros; simp
  rw [mul_one]

def IsoClass.IsSubgroup : IsoClass -> IsoClass -> Prop := by
  apply Quotient.lift₂ Group.IsSubgroup
  intros; ext
  apply Iff.intro
  apply eqv_sub_eqv <;> assumption
  apply eqv_sub_eqv <;> (symm; assumption)

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
  quot_ind (a b)
  intro a_sub_b a' a'_in_a
  replace a_eqv_a' := Quotient.exact a'_in_a
  replace a_sub_b: a ⊆ b := a_sub_b
  exists b
  apply And.intro
  rfl
  apply eqv_sub
  assumption
  assumption

def IsoClass.IsNormalSubgroup.IsSubgroup {a b: IsoClass} : a ◀ b -> a ⊆ b := by
  quot_ind (a b)
  apply Group.IsNormalSubgroup.IsSubgroup

-- the class trivial group is a normal subgroup of every group
def IsoClass.one_nsub (a: IsoClass) : 1 ◀ a := by
  quot_ind a
  show 1 ◀ a
  apply IsNormalSubgroup.intro ⟨fun _ => 1, _⟩
  any_goals
    try intro x
    intros
    rfl
  intro
  simp
  rw [inv_one]
  intros
  simp
  rw [mul_one]
  intro g ()
  simp
  rw [mul_one, mul_inv]
  apply Set.mem_range.mpr
  exists 1

-- the class trivial group can embed into any other isomorphism classs
def IsoClass.one_sub (a: IsoClass) : 1 ⊆ a := by
  apply IsNormalSubgroup.IsSubgroup
  apply one_nsub

@[local simp]
def mul (a b: Group) : Group where
  ty := a.ty × b.ty
  one' := ⟨1, 1⟩
  inv' | ⟨x, y⟩ => ⟨x⁻¹, y⁻¹⟩
  mul' | ⟨a, b⟩, ⟨x, y⟩ => ⟨a * x, b * y⟩
  mul_assoc' := by
    intro ⟨a₀, a₁⟩ ⟨b₀, b₁⟩ ⟨c₀, c₁⟩
    simp [mul_assoc]
  one_mul' := by
    intro ⟨a₀, a₁⟩
    simp [one_mul]
  inv_mul' := by
    intro ⟨a₀, a₁⟩
    simp [inv_mul]

instance : Mul Group := ⟨.mul⟩

@[local simp]
def gmul_def (a b: Group) : a * b = a.mul b := rfl

def gmul.spec (a b c d: Group) : a ≈ c -> b ≈ d -> a * b ≈ c * d := by
  intro ⟨ac, ac_resp_one, ac_resp_inv, ac_resp_mul⟩
  intro ⟨bd, bd_resp_one, bd_resp_inv, bd_resp_mul⟩
  simp at *
  apply IsIsomorphic.intro (ac.toProd bd)
  simp [Equiv.toProd]
  congr
  intro ⟨x, y⟩
  simp [Equiv.toProd, Inv.inv]
  apply And.intro
  apply ac_resp_inv
  apply bd_resp_inv
  intro ⟨x₀, y₀⟩ ⟨x₁, y₁⟩
  simp [Equiv.toProd]
  congr
  apply ac_resp_mul
  apply bd_resp_mul

def IsoClass.mul : IsoClass -> IsoClass -> IsoClass := by
  apply Quotient.lift₂ (⟦· * ·⟧)
  intros
  apply Quot.sound
  apply gmul.spec <;> assumption

instance : Mul IsoClass := ⟨IsoClass.mul⟩

def mk_mul (a b: Group) : ⟦a⟧ * ⟦b⟧ = ⟦a * b⟧ := rfl

def IsSimple (a: Group) : Prop := ∀n, n ◀ a -> n ≈ 1 ∨ n ≈ a

def gmul_one (a: Group) : a * 1 ≈ a := by
  apply IsIsomorphic.intro
  case eq =>
    apply Equiv.mk (·.1) (⟨·, ()⟩)
    intro x; rfl
    intro x; rfl
  rfl
  intros; rfl
  intros; rfl

def one_gmul (a: Group) : 1 * a ≈ a := by
  apply IsIsomorphic.intro
  case eq =>
    apply Equiv.mk (·.2) (⟨(), ·⟩)
    intro x; rfl
    intro x; rfl
  rfl
  intros; rfl
  intros; rfl

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

def of_gmul_eq_one (a b: Group) : a * b ≈ 1 -> a ≈ 1 ∧ b ≈ 1 := by
  intro ⟨iso⟩
  apply And.intro
  · apply IsIsomorphic.intro ⟨(fun _ => ()), (fun x => (iso.invFun x).1), _, _⟩
    rfl
    any_goals try intro x; intros; rfl
    intro x
    simp [Equiv.symm]
    show (iso.invFun 1).fst = _
    rw [iso.inv_resp_one]
    show 1 = x
    symm
    have : Prod.mk x 1 = (1: (a * b).ty) := by
      apply iso.toFun_inj
      rfl
    exact (Prod.mk.inj this).left
  · apply IsIsomorphic.intro ⟨(fun _ => ()), (fun x => (iso.invFun x).2), _, _⟩
    rfl
    any_goals try intro x; intros; rfl
    intro x
    simp [Equiv.symm]
    show (iso.invFun 1).snd = _
    rw [iso.inv_resp_one]
    show 1 = x
    symm
    have : Prod.mk 1 x = (1: (a * b).ty) := by
      apply iso.toFun_inj
      rfl
    exact (Prod.mk.inj this).right

def Trivial.IsSimple : IsSimple 1 := by
  intro x nsub_one; left; symm
  exact Quotient.exact <| sub_one _ (IsNormalSubgroup.IsSubgroup nsub_one)

def IsoClass.Trivial.IsSimple : IsoClass.IsSimple 1 := by
  apply Eq.mpr mk_IsSimple
  exact Group.Trivial.IsSimple

instance {n m: Nat} [NeZero n] [NeZero m] : NeZero (n * m) where
  out := by
    intro h
    cases Nat.mul_eq_zero.mp h <;> (rename_i h; exact NeZero.ne _ h)

def cyclic_sub_of_mul' [NeZero n] [NeZero m] : SubgroupEmbedding (FinCyclic n) (FinCyclic (n * m)) where
  toFun a := ⟨a.val * m, (Nat.mul_lt_mul_right (Nat.zero_lt_of_ne_zero (NeZero.ne _))).mpr a.isLt⟩
  inj a b eq := by
    simp at eq
    injection eq with eq
    apply Fin.val_inj.mp
    apply Nat.mul_right_cancel
    exact Nat.zero_lt_of_ne_zero (NeZero.ne m)
    assumption
  resp_one := by
    show Fin.mk (0 * _) _  = 0
    congr
    rw [Nat.zero_mul, Nat.zero_mod]
  resp_inv x := by
    simp
    congr
    simp
    rw [←Nat.sub_mul, Nat.mul_comm n m, Nat.mod_mul, Nat.mul_div_cancel,
      Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod, Nat.zero_add, Nat.mul_comm]
    congr
    exact Nat.zero_lt_of_ne_zero (NeZero.ne m)
  resp_mul x y := by
    simp
    cases x with | mk x xLt =>
    cases y with | mk y yLt =>
    congr
    simp
    show (_ + _) % _ * _ = _
    rw [Nat.mul_comm n m, Nat.mod_mul, ←Nat.add_mul, Nat.mul_mod_left, Nat.zero_add, Nat.mul_comm]
    congr
    rw [Nat.mul_div_cancel]
    exact Nat.zero_lt_of_ne_zero (NeZero.ne m)

def cyclic_sub_of_mul (n m: Nat) [NeZero n] [NeZero m] : FinCyclic n ⊆ FinCyclic (n * m) := ⟨cyclic_sub_of_mul'⟩
def IsoClass.cyclic_sub_of_mul (n m: Nat) [NeZero n] [NeZero m] : Cyclic n ⊆ Cyclic (n * m) := ⟨cyclic_sub_of_mul'⟩

def cyclic_nsub_of_mul' [NeZero n] [NeZero m] : NormalSubgroupEmbedding (FinCyclic n) (FinCyclic (n * m)) where
  toSubgroupEmbedding := cyclic_sub_of_mul'
  conj_in_norm  := by
    intro ⟨x, xLt⟩ ⟨y, yLt⟩
    unfold cyclic_sub_of_mul'
    simp
    unfold HMul.hMul instHMul Mul.mul instMulNat FinCyclic instMulTy Inv.inv instInvTy fin_inverse
    simp [Fin.add_def]
    apply Set.mem_range.mpr
    simp
    exists ⟨y, yLt⟩
    simp
    rw [Nat.add_comm x, Nat.add_assoc, ←Nat.add_sub_assoc, Nat.add_comm x, Nat.add_sub_cancel]
    rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod, Nat.mul_comm n, Nat.mod_mul, Nat.mul_mod_left]
    rw [Nat.zero_add, Nat.mul_div_cancel, Nat.mod_eq_of_lt yLt, Nat.mul_comm]
    exact Nat.zero_lt_of_ne_zero (NeZero.ne m)
    apply Nat.le_of_lt
    assumption

def cyclic_nsub_of_mul (n m: Nat) [NeZero n] [NeZero m] : FinCyclic n ◀ FinCyclic (n * m) := ⟨cyclic_nsub_of_mul'⟩
def IsoClass.cyclic_nsub_of_mul (n m: Nat) [NeZero n] [NeZero m] : Cyclic n ◀ Cyclic (n * m) := ⟨cyclic_nsub_of_mul'⟩

end Group
