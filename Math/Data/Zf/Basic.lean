import Math.Data.QuotLike.Basic
import Math.Type.Notation
import Math.Data.Set.Basic

namespace ZfSet

inductive Pre where
| intro (α: Type*) (mem: α -> Pre)

def Equiv : Pre -> Pre -> Prop
| .intro _ αmem, .intro _ βmem =>
  (∀a, ∃b, Equiv (αmem a) (βmem b)) ∧
  (∀b, ∃a, Equiv (αmem a) (βmem b))

infix:50 " zf≈ " => Equiv

def Pre.«Type» : Pre -> Type _
| .intro a _ => a

def Pre.Mem : ∀(s: Pre), s.Type -> Pre
| .intro _ mem => mem

@[refl]
def Equiv.refl' : ∀(a: Pre), a zf≈ a
| .intro _ _ => ⟨(fun x => ⟨x, Equiv.refl' _⟩), (fun x => ⟨x, Equiv.refl' _⟩)⟩

@[symm]
def Equiv.symm' : ∀{a b}, a zf≈ b -> b zf≈ a
| .intro a amem, .intro b bmem, ⟨ha, hb⟩ => by
  apply And.intro
  intro b₀
  have ⟨a₀, prf⟩ := hb b₀
  exists a₀
  exact Equiv.symm' prf
  intro a₀
  have ⟨b₀, prf⟩ := ha a₀
  exists b₀
  exact Equiv.symm' prf

def Equiv.trans : ∀{a b c}, a zf≈ b -> b zf≈ c -> a zf≈ c
| .intro a amem, .intro b bmem, .intro c cmem, ⟨hab, hba⟩, ⟨hbc, hcb⟩ => by
  apply And.intro
  intro a₀
  have ⟨b₀, hab⟩ := hab a₀
  have ⟨c₀, hbc⟩ := hbc b₀
  exists c₀
  exact Equiv.trans hab hbc
  intro c₀
  have ⟨b₀, hcb⟩ := hcb c₀
  have ⟨a₀, hba⟩ := hba b₀
  exists a₀
  exact Equiv.trans hba hcb

instance setoid : Setoid Pre where
  r := Equiv
  iseqv := ⟨Equiv.refl', Equiv.symm', Equiv.trans⟩

def Equiv.to_left : ∀{a b}, Equiv a b -> ∀a₀: a.Type, ∃b₀: b.Type, (a.Mem a₀) ≈ (b.Mem b₀)
| .intro _ _, .intro _ _, ⟨l, _⟩ => l
def Equiv.to_right : ∀{a b}, Equiv a b -> ∀b₀: b.Type, ∃a₀: a.Type, (a.Mem a₀) ≈ (b.Mem b₀)
| .intro _ _, .intro _ _, ⟨_, r⟩ => r

def _root_.ZfSet := Quotient setoid
def mk : Pre -> ZfSet := Quotient.mk setoid
instance : QuotientLike setoid ZfSet where

local notation "⟦" a "⟧" => mk a

def ind : {motive: ZfSet -> Prop} -> (mk: ∀x, motive ⟦x⟧) -> ∀x, motive x := Quotient.ind
def ind₂ : {motive: ZfSet -> ZfSet -> Prop} -> (mk: ∀x y, motive ⟦x⟧ ⟦y⟧) -> ∀x y, motive x y := Quotient.ind₂
def ind₃ : {motive: ZfSet -> ZfSet -> ZfSet -> Prop} -> (mk: ∀x y z, motive ⟦x⟧ ⟦y⟧ ⟦z⟧) -> ∀x y z, motive x y z := by
  intro motive h x y z
  induction x, y using ind₂ with | mk x y =>
  induction z using ind with | mk z =>
  apply h
def ind₄ : {motive: ZfSet -> ZfSet -> ZfSet -> ZfSet -> Prop} -> (mk: ∀w x y z, motive ⟦w⟧ ⟦x⟧ ⟦y⟧ ⟦z⟧) -> ∀w x y z, motive w x y z := by
  intro motive h w x y z
  induction w, x using ind₂ with | mk w x =>
  induction y, z using ind₂ with | mk y z =>
  apply h

@[refl]
def Equiv.refl : ∀(a: Pre), a ≈ a := Equiv.refl'
@[symm]
def Equiv.symm : ∀{a b}, a zf≈ b -> b ≈ a := Equiv.symm'

-- constrain membership to be in a single universe for better universe inference
instance : Membership Pre.{u} Pre.{u} where
  mem a b := ∃a₀: a.Type, b ≈ a.Mem a₀

instance : Membership ZfSet ZfSet where
  mem := by
    apply Quotient.lift₂ Membership.mem
    suffices ∀(a₀ b₀ a₁ b₁: Pre) (aeq: a₀ ≈ a₁) (beq: b₀ ≈ b₁), b₀ ∈ a₀ -> b₁ ∈ a₁ by
      intro a₀ b₀ a₁ b₁ aeq beq
      ext; apply Iff.intro
      apply this <;> assumption
      apply this <;> (symm; assumption)
    intro a₀ b₀ a₁ b₁ aeq beq ⟨a₂, b₀_eqv_a⟩
    have ⟨a₂', prf⟩ := aeq.to_left a₂
    exists a₂'
    apply beq.symm.trans
    apply Equiv.trans _ prf
    assumption

instance : HasSubset Pre where
  Subset a b := ∀x ∈ a, x ∈ b

instance : HasSubset ZfSet where
  Subset a b := ∀x ∈ a, x ∈ b

@[simp]
def mk_mem (a b: Pre) : (⟦a⟧ ∈ ⟦b⟧) = (a ∈ b) := rfl

@[simp]
def mk_sub (a b: Pre) : ⟦a⟧ ⊆ ⟦b⟧ ↔ a ⊆ b := by
  apply Iff.intro
  intro h x
  simp only [←mk_mem]
  apply h
  intro h x
  induction x using ind with | mk x =>
  simp
  apply h

def Pre.mem_def {a: Pre} : ∀{x: a.Type}, a.Mem x ∈ a := by
  intro x
  cases a with | intro a amem =>
  exists x

def Pre.ext (a b: Pre) : (∀x, x ∈ a ↔ x ∈ b) -> a ≈ b := by
  intro h
  cases a with | intro a amem =>
  cases b with | intro b bmem =>
  apply And.intro
  intro x
  have ⟨y, prf⟩  := (h (amem x)).mp Pre.mem_def
  exists y
  intro x
  have ⟨y, prf⟩  := (h (bmem x)).mpr Pre.mem_def
  exists y
  symm; assumption

@[ext]
def ext (a b: ZfSet) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := by
  intro h
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  apply Quotient.sound
  apply Pre.ext
  exact fun x => h ⟦x⟧

@[refl]
def sub_refl (a: ZfSet) : a ⊆ a := fun _ => id
def sub_trans {a b c: ZfSet} : a ⊆ b -> b ⊆ c -> a ⊆ c := fun ab bc x h => bc x (ab x h)

def Pre.lift.{u, v} : Pre.{u} -> Pre.{max u v}
| .intro a amem => .intro (ULift a) (fun x => (amem x.down).lift)

def Pre.lift.spec.{u, v} (a: Pre.{u}) : a zf≈ Pre.lift.{u, v} a := by
  induction a with | intro a amem ih =>
  apply And.intro
  intro a₀
  exists ⟨a₀⟩
  apply ih
  intro a₀
  exists a₀.down
  apply ih

def lift.{u, v} : ZfSet.{u} -> ZfSet.{max u v} := by
  apply Quotient.lift (⟦.lift ·⟧)
  intro a b eqv
  apply Quotient.sound
  apply (Pre.lift.spec a).symm'.trans
  apply Equiv.trans _ (Pre.lift.spec b)
  assumption

instance : EmptyCollection Pre where
  emptyCollection := .intro PEmpty PEmpty.elim

instance : EmptyCollection ZfSet where
  emptyCollection := ⟦∅⟧

@[simp]
def not_mem_empty : ∀x, x ∉ (∅: ZfSet) := by
  intro x
  induction x using ind with | mk x =>
  intro ⟨_, _⟩
  contradiction

def empty_sub (a: ZfSet) : ∅ ⊆ a := by
  intro _ h
  have := not_mem_empty _ h
  contradiction

def of_sub_empty (a: ZfSet) : a ⊆ ∅ -> a = ∅ := by
  intro h
  ext x
  apply Iff.intro
  apply h
  intro h
  have := not_mem_empty _ h
  contradiction

def sub_empty_iff (a: ZfSet) : a ⊆ ∅ ↔ a = ∅ := by
  apply Iff.intro
  apply of_sub_empty
  intro h
  subst h
  rfl

def Pre.union : Pre.{u} -> Pre.{u} -> Pre.{u}
| .intro a amem, .intro b bmem => .intro (a ⊕ b) (fun
  | .inl x => amem x
  | .inr x => bmem x)

instance : Union Pre := ⟨Pre.union⟩

def Pre.union.spec (a b c d: Pre) : a zf≈ c -> b zf≈ d -> a ∪ b zf≈ c ∪ d := by
  cases a with | intro a amem =>
  cases b with | intro b bmem =>
  cases c with | intro c cmem =>
  cases d with | intro d dmem =>
  intro ac bd
  apply And.intro
  intro x
  cases x <;> rename_i x
  have ⟨y, prf⟩ := ac.left x
  exists .inl y
  have ⟨y, prf⟩ := bd.left x
  exists .inr y
  intro x
  cases x <;> rename_i x
  have ⟨y, prf⟩ := ac.right x
  exists .inl y
  have ⟨y, prf⟩ := bd.right x
  exists .inr y

def union : ZfSet -> ZfSet -> ZfSet := by
  apply Quotient.lift₂ (⟦· ∪ ·⟧)
  intros
  apply Quotient.sound
  apply Pre.union.spec <;> assumption

instance : Union ZfSet := ⟨.union⟩

@[simp]
def mk_union {a b: Pre} : ⟦a⟧ ∪ ⟦b⟧ = ⟦a ∪ b⟧ := rfl

def mem_union {a b: ZfSet} : ∀{x}, x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b := by
  intro x
  induction a, b, x using ind₃ with | mk a b x =>
  cases a with | intro a amem =>
  cases b with | intro b bmem =>
  simp
  apply Iff.intro
  intro ⟨x₀, prf⟩
  cases x₀ <;> rename_i x₀
  left; exists x₀
  right; exists x₀
  intro h
  cases h <;> rename_i h
  obtain ⟨x, prf⟩ := h
  exists .inl x
  obtain ⟨x, prf⟩ := h
  exists .inr x

def union_comm (a b: ZfSet) : a ∪ b = b ∪ a := by
  ext x; simp [mem_union, or_comm]

def union_assoc (a b c: ZfSet) : a ∪ b ∪ c = a ∪ (b ∪ c) := by
  ext x; simp [mem_union, or_assoc]

def sub_union_left (a b: ZfSet) : a ⊆ a ∪ b := by
  intro x
  simp [mem_union]
  exact .inl

def sub_union_right (a b: ZfSet) : b ⊆ a ∪ b := by
  intro x
  simp [mem_union]
  exact .inr

instance : @Std.Commutative ZfSet (· ∪ ·) := ⟨union_comm⟩
instance : @Std.Associative ZfSet (· ∪ ·) := ⟨union_assoc⟩

def union_empty (a: ZfSet) : a ∪ ∅ = a := by
  ext x
  apply Iff.intro
  intro h
  cases mem_union.mp h
  assumption
  have := not_mem_empty x
  contradiction
  intro h
  apply mem_union.mpr
  left; assumption

def empty_union (a: ZfSet) : ∅ ∪ a = a := by
  rw [union_comm]
  apply union_empty

def Pre.sep (P: Pre → Prop) : Pre -> Pre
| .intro a amem => .intro { x: a // P (amem x) } (fun x => amem x.val)

def Pre.sep.spec (P: Pre → Prop) (a b: Pre) :
  a zf≈ b -> (∀x y, x zf≈ y -> P x -> P y) ->
  a.sep P zf≈ b.sep P := by
  intro ab resp
  cases a with | intro a amem =>
  cases b with | intro b bmem =>
  apply And.intro
  · intro ⟨a₀, pa₀⟩
    have ⟨b₀, prf⟩ := ab.left a₀
    refine ⟨⟨b₀, ?_⟩, ?_⟩
    apply resp
    all_goals assumption
  · intro ⟨b₀, pb₀⟩
    have ⟨a₀, prf⟩ := ab.right b₀
    refine ⟨⟨a₀, ?_⟩, ?_⟩
    apply resp
    symm
    all_goals assumption

def sep (P: ZfSet -> Prop) : ZfSet -> ZfSet := by
  apply Quotient.lift (⟦Pre.sep (fun x => P ⟦x⟧) ·⟧)
  intro a b eq
  apply Quotient.sound
  apply Pre.sep.spec
  assumption
  intro _ _ eq
  unfold ZfSet.mk
  rw [Quotient.sound eq]
  exact id

@[simp]
def mk_sep {P: ZfSet -> Prop} {a: Pre} : ⟦a⟧.sep P = ⟦a.sep (fun x => P ⟦x⟧)⟧ := rfl

def mem_sep {P: ZfSet -> Prop} {a: ZfSet} : ∀{x}, x ∈ a.sep P ↔ x ∈ a ∧ P x := by
  intro x
  induction a, x using ind₂ with | mk a x =>
  cases a with | intro a amem =>
  simp
  apply Iff.intro
  intro ⟨y, prf⟩
  apply And.intro
  exists y.val
  unfold ZfSet.mk
  rw [Quotient.sound prf]
  exact y.property
  intro ⟨⟨y, prf⟩, prop⟩
  unfold ZfSet.mk at prop
  rw [Quotient.sound prf] at prop
  exists ⟨y, prop⟩

def inter (a b: ZfSet) := a.sep (· ∈ b)

instance : Inter ZfSet := ⟨inter⟩

def mem_inter {a b: ZfSet} : ∀{x}, x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b := mem_sep

def inter_comm (a b: ZfSet) : a ∩ b = b ∩ a := by
  ext x
  simp [mem_inter, and_comm]

def inter_assoc (a b c: ZfSet) : a ∩ b ∩ c = a ∩ (b ∩ c) := by
  ext x
  simp [mem_inter, and_assoc]

def empty_inter (a: ZfSet) : ∅ ∩ a = ∅ := by
  ext; simp [mem_inter]

def inter_empty (a: ZfSet) : a ∩ ∅ = ∅ := by
  ext; simp [mem_inter]

def inter_sub_left (a b: ZfSet) : a ∩ b ⊆ a := by
  intro x
  simp [mem_inter]
  intros; assumption

def inter_sub_right (a b: ZfSet) : a ∩ b ⊆ b := by
  intro x
  simp [mem_inter]

def sdiff (a b: ZfSet) := a.sep (· ∉ b)

instance : SDiff ZfSet := ⟨sdiff⟩

def mem_sdiff {a b: ZfSet} : ∀{x}, x ∈ a \ b ↔ x ∈ a ∧ x ∉ b := by
  intro x
  show x ∈ sdiff a b ↔ _
  unfold sdiff
  exact mem_sep

def empty_sdiff (a: ZfSet) : ∅ \ a = ∅ := by
  ext; simp [mem_sdiff]

def sdiff_empty (a: ZfSet) : a \ ∅ = a := by
  ext; simp [mem_sdiff]

def sdiff_sub_left (a b: ZfSet) : a \ b ⊆ a := by
  intro x
  simp [mem_sdiff]
  intros; assumption

def Pre.singleton (a: Pre) : Pre := .intro PUnit (fun _ => a)
instance : Singleton Pre Pre := ⟨.singleton⟩
def singleton : ZfSet -> ZfSet := by
  apply Quotient.lift (⟦{·}⟧)
  intros a b  eq
  apply Quotient.sound
  apply And.intro
  intro; refine ⟨(), eq⟩
  intro; refine ⟨(), eq⟩
instance : Singleton ZfSet ZfSet := ⟨.singleton⟩

def mem_singleton {a: ZfSet} : ∀{x: ZfSet}, x ∈ ({a}: ZfSet) ↔ x = a := by
  intro x
  induction a, x using ind₂ with | mk a x =>
  apply Iff.intro
  intro ⟨h, prf⟩
  exact Quotient.sound prf
  intro h
  exact ⟨(), Quotient.exact h⟩

def Pre.powerset : Pre -> Pre
| .intro a amem => .intro (Set a) fun s => .intro { x // x ∈ s } fun x => amem x

def Pre.mem_powerset {a: Pre} : ∀{x}, x ∈ a.powerset ↔ x ⊆ a := by
  intro x
  cases a with | intro a amem =>
  cases x with | intro x xmem =>
  apply Iff.intro
  intro mem
  obtain ⟨s, h⟩ := mem
  obtain s : Set a := s
  intro x₀ x₀mem
  obtain ⟨x₁, x₀_eq_x₁⟩ := x₀mem
  obtain x₁: x := x₁
  obtain ⟨a₀, prf⟩ := h.to_left x₁
  replace ⟨a₀, a₀_mem⟩ : { a // a ∈ _ } := a₀
  refine ⟨a₀, ?_⟩
  apply x₀_eq_x₁.trans
  apply prf.trans
  rfl
  intro sub
  replace sub := fun y => sub y
  refine ⟨?_, ?_⟩
  apply Set.mk
  intro a₀
  exact ∃x₀, xmem x₀ zf≈ amem a₀
  apply And.intro
  intro x₀
  simp only
  have ⟨a₀, pf⟩ := sub (xmem x₀) Pre.mem_def
  refine ⟨⟨a₀, ?_⟩, ?_⟩
  exists x₀
  assumption
  intro ⟨a₀, prf⟩
  obtain ⟨x₀, prf⟩  := prf
  exists x₀

def powerset : ZfSet -> ZfSet := by
  apply Quotient.lift (⟦·.powerset⟧)
  intro a b eq
  ext x; induction x using ind with | mk x =>
  simp [Pre.mem_powerset]
  have : ⟦a⟧ = ⟦b⟧ := Quotient.sound eq
  rw [←mk_sub, ←mk_sub, this]

@[simp]
def mk_powerset (a: Pre) : ⟦a⟧.powerset = ⟦a.powerset⟧ := rfl

def mem_powerset {a: ZfSet} : ∀{x}, x ∈ a.powerset ↔ x ⊆ a := by
  intro x
  induction a, x using ind₂ with | mk a x =>
  simp [Pre.mem_powerset]

def powerset_empty : powerset ∅ = {∅} := by
  ext x
  rw [mem_powerset, mem_singleton]
  exact sub_empty_iff x
