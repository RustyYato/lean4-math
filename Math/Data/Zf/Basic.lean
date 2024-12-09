import Math.Data.QuotLike.Basic
import Math.Type.Notation

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

@[simp]
def mk_mem (a b: Pre) : (⟦a⟧ ∈ ⟦b⟧) = (a ∈ b) := rfl

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

end ZfSet
