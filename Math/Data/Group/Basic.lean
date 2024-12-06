import Math.Type.Basic
import Math.Algebra.Ring
import Math.Data.QuotLike.Basic
import Math.Type.Finite
import Math.Data.Set.Finite
import Math.Data.Fin.Basic

attribute [local simp] IsEquivLike.coe
attribute [local simp] DFunLike.coe

theorem Nat.mul_sub_div' (x n p : Nat) (h₁ : p ≤ n * x) : (n * x - p) / n = x - p / n := by
  sorry

theorem Nat.sub_mul (a b k : Nat): (a - b) * k = a * k - b * k := by
  sorry

structure Group where
  ty: Type*
  mul': ty -> ty -> ty
  one': ty
  inv': ty -> ty
  mul_assoc': ∀a b c: ty, mul' (mul' a b) c = mul' a (mul' b c)
  one_mul': ∀a: ty, mul' one' a = a
  inv_mul': ∀a: ty, mul' (inv' a) a = one'

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

structure SubgroupEmbedding (a b: Group) where
  emb: a.ty ↪ b.ty
  resp_one: emb.toFun 1 = 1
  resp_inv: ∀x, emb.toFun (x⁻¹) = (emb.toFun x)⁻¹
  resp_mul: ∀x y, emb.toFun (x * y) = emb.toFun x * emb.toFun y

structure Isomorphsism (a b: Group) where
  eq: a.ty ≃ b.ty
  resp_one: eq.toFun 1 = 1
  resp_inv: ∀x, eq.toFun (x⁻¹) = (eq.toFun x)⁻¹
  resp_mul: ∀x y, eq.toFun (x * y) = eq.toFun x * eq.toFun y

def Isomorphsism.inv_resp_one (iso: Isomorphsism a b) : iso.eq.invFun 1 = 1 := by
  apply iso.eq.toFun_inj
  rw [iso.resp_one, iso.eq.rightInv]
def Isomorphsism.inv_resp_inv (iso: Isomorphsism a b) (x: b.ty) : iso.eq.invFun (x⁻¹) = (iso.eq.invFun x)⁻¹ := by
  apply iso.eq.toFun_inj
  rw [iso.resp_inv, iso.eq.rightInv, iso.eq.rightInv]
def Isomorphsism.inv_resp_mul (iso: Isomorphsism a b) (x y: b.ty) : iso.eq.invFun (x * y) = (iso.eq.invFun x) * (iso.eq.invFun y) := by
  apply iso.eq.toFun_inj
  rw [iso.resp_mul, iso.eq.rightInv, iso.eq.rightInv, iso.eq.rightInv]

inductive IsSubgroup (a b: Group): Prop where
| ofSub (sub: SubgroupEmbedding a b)

inductive IsIsomorphic (a b: Group): Prop where
| ofIso (iso: Isomorphsism a b)

def IsSubgroup.intro {a b: Group}
  (emb: a.ty ↪ b.ty)
  (resp_one: emb 1 = 1)
  (resp_inv: ∀x, emb (x⁻¹) = (emb x)⁻¹)
  (resp_mul: ∀x y, emb (x * y) = emb x * emb y) : IsSubgroup a b := ⟨⟨emb, resp_one, resp_inv, resp_mul⟩⟩

def IsIsomorphic.intro {a b: Group}
  (eq: a.ty ≃ b.ty)
  (resp_one: eq 1 = 1)
  (resp_inv: ∀x, eq (x⁻¹) = (eq x)⁻¹)
  (resp_mul: ∀x y, eq (x * y) = eq x * eq y) : IsIsomorphic a b := ⟨⟨eq, resp_one, resp_inv, resp_mul⟩⟩

def IsIsomorphic.IsSubgroup (a b: Group) (h: a.IsIsomorphic b) : a.IsSubgroup b := by
  obtain ⟨⟨eq, resp_one, resp_inv, resp_mul⟩⟩ := h
  apply IsSubgroup.intro eq.toEmbedding <;> assumption

@[refl]
def IsIsomorphic.refl (a: Group) : a.IsIsomorphic a := by
  apply IsIsomorphic.intro Equiv.refl <;> (intros; rfl)

@[symm]
def IsIsomorphic.symm {a b: Group} (h: a.IsIsomorphic b) : b.IsIsomorphic a := by
  obtain ⟨eq, resp_one, resp_inv, resp_mul⟩ := h
  apply IsIsomorphic.intro eq.symm
  simp [Equiv.symm]
  rw [←resp_one, eq.leftInv]
  intro x
  simp [Equiv.symm]
  rw [
    ←eq.rightInv x,
    ←resp_inv (eq.invFun x),
    eq.rightInv, eq.leftInv]
  intro x y
  simp [Equiv.symm]
  rw [←eq.leftInv (eq.invFun x * eq.invFun y), resp_mul, eq.rightInv, eq.rightInv]

def IsIsomorphic.trans {a b c: Group} (h: a.IsIsomorphic b) (g: b.IsIsomorphic c) : a.IsIsomorphic c := by
  obtain ⟨h, hresp_one, hresp_inv, hresp_mul⟩ := h
  obtain ⟨g, gresp_one, gresp_inv, gresp_mul⟩ := g
  apply IsIsomorphic.intro (h.trans g)
  simp [Equiv.trans]
  rw [hresp_one, gresp_one]
  simp [Equiv.trans]; intro x
  rw [hresp_inv, gresp_inv]
  simp [Equiv.trans]; intro x y
  rw [hresp_mul, gresp_mul]

def IsSubgroup.refl (a: Group) : a.IsSubgroup a := (IsIsomorphic.refl a).IsSubgroup
def IsSubgroup.trans {a b c: Group} : a.IsSubgroup b -> b.IsSubgroup c -> a.IsSubgroup c := by
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

instance : HasSubset Group := ⟨IsSubgroup⟩

def sub_refl (a: Group) : a ⊆ a := IsSubgroup.refl _
def sub_trans {a b c: Group} : a ⊆ b -> b ⊆ c -> a ⊆ c := IsSubgroup.trans

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

instance : HasSubset IsoClass where
  Subset a b := ∀a' ∈ a, ∃b' ∈ b, a' ⊆ b'

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

def eqv_sub (a b k: Group) : a ≈ b -> a ⊆ k -> b ⊆ k := by
  intro eqv a_sub_k
  apply IsSubgroup.trans _ a_sub_k
  apply IsIsomorphic.IsSubgroup
  symm; assumption

def sub_eqv (a b k: Group) : a ≈ b -> k ⊆ a -> k ⊆ b := by
  intro eqv a_sub_k
  apply IsSubgroup.trans a_sub_k
  apply IsIsomorphic.IsSubgroup
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

-- the class trivial group can embed into any other isomorphism classs
def IsoClass.one_sub (a: IsoClass) : 1 ⊆ a := by
  intros x mem
  quot_ind a
  exists a
  apply And.intro rfl
  have := quot.exact mem
  apply eqv_sub
  assumption
  apply Group.one_sub

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

def IsSimple (a: Group) : Prop := ∀x y, x * y ≈ a -> x ≈ 1 ∨ y ≈ 1

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
  intro eq asimp x y h
  have := h.trans (gmul_one b).symm
  apply asimp
  apply eqv_trans _ (gmul_one _)
  apply flip eqv_trans
  apply gmul.spec
  symm; assumption
  rfl
  apply eqv_trans _ (gmul_one _).symm
  assumption

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
  · apply IsIsomorphic.intro ⟨(fun _ => ()), (fun x => (iso.eq.invFun x).1), _, _⟩
    rfl
    any_goals try intro x; intros; rfl
    intro x
    simp [Equiv.symm]
    show (iso.eq.invFun 1).fst = _
    rw [iso.inv_resp_one]
    show 1 = x
    symm
    have : Prod.mk x 1 = (1: (a * b).ty) := by
      apply iso.eq.toFun_inj
      rfl
    exact (Prod.mk.inj this).left
  · apply IsIsomorphic.intro ⟨(fun _ => ()), (fun x => (iso.eq.invFun x).2), _, _⟩
    rfl
    any_goals try intro x; intros; rfl
    intro x
    simp [Equiv.symm]
    show (iso.eq.invFun 1).snd = _
    rw [iso.inv_resp_one]
    show 1 = x
    symm
    have : Prod.mk 1 x = (1: (a * b).ty) := by
      apply iso.eq.toFun_inj
      rfl
    exact (Prod.mk.inj this).right

def Trivial.IsSimple : IsSimple 1 := by
  intro x y eq
  exact .inl (of_gmul_eq_one _ _ eq).left

def IsoClass.Trivial.IsSimple : IsoClass.IsSimple 1 := by
  apply Eq.mpr mk_IsSimple
  exact Group.Trivial.IsSimple

instance {n m: Nat} [NeZero n] [NeZero m] : NeZero (n * m) where
  out := by
    intro h
    cases Nat.mul_eq_zero.mp h <;> (rename_i h; exact NeZero.ne _ h)

end Group
